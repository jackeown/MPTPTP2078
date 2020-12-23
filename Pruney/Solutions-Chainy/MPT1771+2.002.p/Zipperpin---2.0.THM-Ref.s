%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YM7qEbMb0W

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:12 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  372 (6379 expanded)
%              Number of leaves         :   32 (1854 expanded)
%              Depth                    :   34
%              Number of atoms          : 5214 (264650 expanded)
%              Number of equality atoms :   80 (4069 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(t82_tmap_1,conjecture,(
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
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( ( F = G )
                                    & ( r1_tmap_1 @ D @ B @ ( k2_tmap_1 @ A @ B @ E @ D ) @ F ) )
                                 => ( r1_tmap_1 @ C @ B @ ( k2_tmap_1 @ A @ B @ E @ C ) @ G ) ) ) ) ) ) ) ) ) ) )).

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
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                                 => ( ( ( F = G )
                                      & ( r1_tmap_1 @ D @ B @ ( k2_tmap_1 @ A @ B @ E @ D ) @ F ) )
                                   => ( r1_tmap_1 @ C @ B @ ( k2_tmap_1 @ A @ B @ E @ C ) @ G ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t82_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t78_tmap_1,axiom,(
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

thf('4',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v2_struct_0 @ X32 )
      | ~ ( v2_pre_topc @ X32 )
      | ~ ( l1_pre_topc @ X32 )
      | ( v2_struct_0 @ X33 )
      | ~ ( m1_pre_topc @ X33 @ X34 )
      | ~ ( m1_pre_topc @ X35 @ X33 )
      | ( r2_funct_2 @ ( u1_struct_0 @ X35 ) @ ( u1_struct_0 @ X32 ) @ ( k3_tmap_1 @ X34 @ X32 @ X33 @ X35 @ ( k2_tmap_1 @ X34 @ X32 @ X36 @ X33 ) ) @ ( k2_tmap_1 @ X34 @ X32 @ X36 @ X35 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X32 ) ) ) )
      | ~ ( v1_funct_2 @ X36 @ ( u1_struct_0 @ X34 ) @ ( u1_struct_0 @ X32 ) )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( m1_pre_topc @ X35 @ X34 )
      | ( v2_struct_0 @ X35 )
      | ~ ( l1_pre_topc @ X34 )
      | ~ ( v2_pre_topc @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t78_tmap_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( r2_funct_2 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X1 @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1 ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ X1 )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','6','7','8','9','10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ X0 @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( m1_pre_topc @ A @ A ) ) )).

thf('20',plain,(
    ! [X25: $i] :
      ( ( m1_pre_topc @ X25 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X21 @ X23 @ X22 @ X20 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X23 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('23',plain,(
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
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('34',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

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

thf('39',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X18 )
      | ( ( k3_tmap_1 @ X17 @ X15 @ X18 @ X16 @ X19 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) @ X19 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X25: $i] :
      ( ( m1_pre_topc @ X25 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X21 @ X23 @ X22 @ X20 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('45',plain,(
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
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('56',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['41','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','60','61','62'])).

thf('64',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X25: $i] :
      ( ( m1_pre_topc @ X25 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('66',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X18 )
      | ( ( k3_tmap_1 @ X17 @ X15 @ X18 @ X16 @ X19 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) @ X19 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( v1_funct_2 @ X19 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('68',plain,(
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
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
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
    inference(demod,[status(thm)],['68','69','70','71','72'])).

thf('74',plain,(
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
    inference('sup-',[status(thm)],['65','73'])).

thf('75',plain,(
    l1_pre_topc @ sk_A ),
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
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['64','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
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

thf('87',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( ( k2_tmap_1 @ X13 @ X11 @ X14 @ X12 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) @ X14 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('88',plain,(
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
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92','93','94'])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['84','100'])).

thf('102',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X25: $i] :
      ( ( m1_pre_topc @ X25 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('104',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X21 @ X23 @ X22 @ X20 @ X24 ) @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('106',plain,(
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
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_A @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['106','107','108','109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['103','111'])).

thf('113',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['102','116'])).

thf('118',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['84','100'])).

thf('119',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['84','100'])).

thf('125',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['84','100'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','101','123','124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['127','128','129'])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['17','130'])).

thf('132',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('134',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ( ( k2_tmap_1 @ X13 @ X11 @ X14 @ X12 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) @ X14 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('137',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_pre_topc @ X4 @ X5 )
      | ( v2_pre_topc @ X4 )
      | ~ ( l1_pre_topc @ X5 )
      | ~ ( v2_pre_topc @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('138',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('142',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('143',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_pre_topc @ X6 @ X7 )
      | ( l1_pre_topc @ X6 )
      | ~ ( l1_pre_topc @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('144',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['144','145'])).

thf('147',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('148',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['135','141','146','147','148','149'])).

thf('151',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['84','100'])).

thf('152',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['84','100'])).

thf('153',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['84','100'])).

thf('154',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['150','151','152','153'])).

thf('155',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['132','156'])).

thf('158',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['131','161','162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
    = ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) ),
    inference(clc,[status(thm)],['165','166'])).

thf('168',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['16','167'])).

thf('169',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    ! [X25: $i] :
      ( ( m1_pre_topc @ X25 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('171',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('172',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ( m1_subset_1 @ ( k3_tmap_1 @ X21 @ X23 @ X22 @ X20 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X23 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('173',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['171','172'])).

thf('174',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('175',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['173','174','175','176'])).

thf('178',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['84','100'])).

thf('179',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['84','100'])).

thf('180',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['177','178','179','180'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference('sup-',[status(thm)],['170','181'])).

thf('183',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['144','145'])).

thf('184',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['144','145'])).

thf('185',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['182','183','184','185'])).

thf('187',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['169','186'])).

thf('188',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['187','188'])).

thf('190',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['189','190'])).

thf('192',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    ! [X25: $i] :
      ( ( m1_pre_topc @ X25 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('194',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','101','123','124','125'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['144','145'])).

thf('197',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['144','145'])).

thf('198',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('199',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['195','196','197','198'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['199'])).

thf('201',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['192','200'])).

thf('202',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['201','202'])).

thf('204',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('205',plain,
    ( ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['203','204'])).

thf('206',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('207',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ),
    inference('sup+',[status(thm)],['205','206'])).

thf('208',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['191','207'])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('209',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_funct_2 @ X3 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( X0 = X3 )
      | ~ ( r2_funct_2 @ X1 @ X2 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('210',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ X0 )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    ! [X25: $i] :
      ( ( m1_pre_topc @ X25 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('213',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('214',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['84','100'])).

thf('215',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('216',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ( v1_funct_1 @ ( k3_tmap_1 @ X21 @ X23 @ X22 @ X20 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('219',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E ) ),
    inference('sup+',[status(thm)],['84','100'])).

thf('220',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('221',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['217','220','221','222'])).

thf('224',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('225',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['223','224'])).

thf('226',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['212','225'])).

thf('227',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['144','145'])).

thf('228',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['144','145'])).

thf('229',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('230',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ) ),
    inference(demod,[status(thm)],['226','227','228','229'])).

thf('231',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['211','230'])).

thf('232',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['231','232'])).

thf('234',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ),
    inference(clc,[status(thm)],['233','234'])).

thf('236',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ),
    inference('sup+',[status(thm)],['205','206'])).

thf('237',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('239',plain,(
    ! [X25: $i] :
      ( ( m1_pre_topc @ X25 @ X25 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t2_tsep_1])).

thf('240',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['213','214'])).

thf('241',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_pre_topc @ X20 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( l1_pre_topc @ X23 )
      | ~ ( v2_pre_topc @ X23 )
      | ( v2_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_2 @ X24 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X22 ) @ ( u1_struct_0 @ X23 ) ) ) )
      | ( v1_funct_2 @ ( k3_tmap_1 @ X21 @ X23 @ X22 @ X20 @ X24 ) @ ( u1_struct_0 @ X20 ) @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_tmap_1])).

thf('242',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['240','241'])).

thf('243',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('244',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('246',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['242','243','244','245'])).

thf('247',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('248',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v2_pre_topc @ X1 )
      | ~ ( l1_pre_topc @ X1 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ sk_D @ X1 )
      | ~ ( m1_pre_topc @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['246','247'])).

thf('249',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['239','248'])).

thf('250',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['144','145'])).

thf('251',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['144','145'])).

thf('252',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('253',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['249','250','251','252'])).

thf('254',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['238','253'])).

thf('255',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['254','255'])).

thf('257',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('258',plain,(
    v1_funct_2 @ ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['256','257'])).

thf('259',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
    = ( k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ) ),
    inference('sup+',[status(thm)],['205','206'])).

thf('260',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['258','259'])).

thf('261',plain,(
    ! [X0: $i] :
      ( ~ ( r2_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ X0 )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['210','237','260'])).

thf('262',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ) ),
    inference('sup-',[status(thm)],['168','261'])).

thf('263',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('264',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['51','52','53','54'])).

thf('265',plain,
    ( ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ) ),
    inference(clc,[status(thm)],['265','266'])).

thf('268',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('269',plain,(
    v1_funct_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference(clc,[status(thm)],['267','268'])).

thf('270',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('271',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('272',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['270','271'])).

thf('273',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('274',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['272','273'])).

thf('275',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['274','275'])).

thf('277',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('278',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['88','89','90','91','92','93','94'])).

thf('279',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['277','278'])).

thf('280',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['279','280'])).

thf('282',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('283',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['281','282'])).

thf('284',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['276','283'])).

thf('285',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['269','284'])).

thf('286',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('287',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('288',plain,
    ( ( v1_funct_2 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['286','287'])).

thf('289',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['276','283'])).

thf('290',plain,
    ( ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['288','289'])).

thf('291',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('292',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['290','291'])).

thf('293',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['292','293'])).

thf('295',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,(
    ! [X0: $i] :
      ( ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) ) ) ) ) ),
    inference(demod,[status(thm)],['29','30','31','32'])).

thf('297',plain,
    ( ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['295','296'])).

thf('298',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('299',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['297','298'])).

thf('300',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('301',plain,(
    m1_subset_1 @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['299','300'])).

thf('302',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C )
    = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E ) ),
    inference('sup+',[status(thm)],['276','283'])).

thf('303',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['301','302'])).

thf('304',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C )
      = ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) ) ),
    inference(demod,[status(thm)],['262','285','294','303'])).

thf('305',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('306',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('307',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['305','306'])).

thf('308',plain,(
    r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('309',plain,(
    m1_subset_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['213','214'])).

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

thf('310',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ~ ( l1_pre_topc @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ( r1_tmap_1 @ X27 @ X29 @ ( k2_tmap_1 @ X26 @ X29 @ X30 @ X27 ) @ X28 )
      | ( X31 != X28 )
      | ~ ( r1_tmap_1 @ X26 @ X29 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X26 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('311',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X29 )
      | ~ ( v2_pre_topc @ X29 )
      | ~ ( l1_pre_topc @ X29 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X26 ) @ ( u1_struct_0 @ X29 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ~ ( r1_tmap_1 @ X26 @ X29 @ X30 @ X28 )
      | ( r1_tmap_1 @ X27 @ X29 @ ( k2_tmap_1 @ X26 @ X29 @ X30 @ X27 ) @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ~ ( m1_pre_topc @ X27 @ X26 )
      | ( v2_struct_0 @ X27 )
      | ~ ( l1_pre_topc @ X26 )
      | ~ ( v2_pre_topc @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(simplify,[status(thm)],['310'])).

thf('312',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['309','311'])).

thf('313',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['138','139','140'])).

thf('314',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['144','145'])).

thf('315',plain,(
    v1_funct_2 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('316',plain,(
    v1_funct_1 @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) ),
    inference(demod,[status(thm)],['218','219'])).

thf('317',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('319',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['312','313','314','315','316','317','318'])).

thf('320',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X0 ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['308','319'])).

thf('321',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('322',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( r1_tmap_1 @ X0 @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ X0 ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['320','321'])).

thf('323',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['307','322'])).

thf('324',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D ) @ sk_C ) @ sk_F )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['323','324'])).

thf('326',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['304','325'])).

thf('327',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(simplify,[status(thm)],['326'])).

thf('328',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('329',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['328','329'])).

thf('331',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['327','330'])).

thf('332',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('333',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['331','332'])).

thf('334',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('335',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['333','334'])).

thf('336',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('337',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['335','336'])).

thf('338',plain,(
    $false ),
    inference(demod,[status(thm)],['0','337'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YM7qEbMb0W
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:48:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.59/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.82  % Solved by: fo/fo7.sh
% 0.59/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.82  % done 668 iterations in 0.367s
% 0.59/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.82  % SZS output start Refutation
% 0.59/0.82  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.82  thf(sk_D_type, type, sk_D: $i).
% 0.59/0.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.82  thf(sk_G_type, type, sk_G: $i).
% 0.59/0.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.82  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.82  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.59/0.82  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.59/0.82  thf(sk_E_type, type, sk_E: $i).
% 0.59/0.82  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.59/0.82  thf(sk_F_type, type, sk_F: $i).
% 0.59/0.82  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.59/0.82  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.59/0.82  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.59/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.82  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.59/0.82  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.82  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.59/0.82  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.59/0.82  thf(t82_tmap_1, conjecture,
% 0.59/0.82    (![A:$i]:
% 0.59/0.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.82       ( ![B:$i]:
% 0.59/0.82         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.59/0.82             ( l1_pre_topc @ B ) ) =>
% 0.59/0.82           ( ![C:$i]:
% 0.59/0.82             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.59/0.82               ( ![D:$i]:
% 0.59/0.82                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.59/0.82                   ( ![E:$i]:
% 0.59/0.82                     ( ( ( v1_funct_1 @ E ) & 
% 0.59/0.82                         ( v1_funct_2 @
% 0.59/0.82                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.82                         ( m1_subset_1 @
% 0.59/0.82                           E @ 
% 0.59/0.82                           ( k1_zfmisc_1 @
% 0.59/0.82                             ( k2_zfmisc_1 @
% 0.59/0.82                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.82                       ( ( m1_pre_topc @ C @ D ) =>
% 0.59/0.82                         ( ![F:$i]:
% 0.59/0.82                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.59/0.82                             ( ![G:$i]:
% 0.59/0.82                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.59/0.82                                 ( ( ( ( F ) = ( G ) ) & 
% 0.59/0.82                                     ( r1_tmap_1 @
% 0.59/0.82                                       D @ B @ ( k2_tmap_1 @ A @ B @ E @ D ) @ 
% 0.59/0.82                                       F ) ) =>
% 0.59/0.82                                   ( r1_tmap_1 @
% 0.59/0.82                                     C @ B @ ( k2_tmap_1 @ A @ B @ E @ C ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.82    (~( ![A:$i]:
% 0.59/0.82        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.59/0.82            ( l1_pre_topc @ A ) ) =>
% 0.59/0.82          ( ![B:$i]:
% 0.59/0.82            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.59/0.82                ( l1_pre_topc @ B ) ) =>
% 0.59/0.82              ( ![C:$i]:
% 0.59/0.82                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.59/0.82                  ( ![D:$i]:
% 0.59/0.82                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.59/0.82                      ( ![E:$i]:
% 0.59/0.82                        ( ( ( v1_funct_1 @ E ) & 
% 0.59/0.82                            ( v1_funct_2 @
% 0.59/0.82                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.82                            ( m1_subset_1 @
% 0.59/0.82                              E @ 
% 0.59/0.82                              ( k1_zfmisc_1 @
% 0.59/0.82                                ( k2_zfmisc_1 @
% 0.59/0.82                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.82                          ( ( m1_pre_topc @ C @ D ) =>
% 0.59/0.82                            ( ![F:$i]:
% 0.59/0.82                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.59/0.82                                ( ![G:$i]:
% 0.59/0.82                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.59/0.82                                    ( ( ( ( F ) = ( G ) ) & 
% 0.59/0.82                                        ( r1_tmap_1 @
% 0.59/0.82                                          D @ B @ 
% 0.59/0.82                                          ( k2_tmap_1 @ A @ B @ E @ D ) @ F ) ) =>
% 0.59/0.82                                      ( r1_tmap_1 @
% 0.59/0.82                                        C @ B @ 
% 0.59/0.82                                        ( k2_tmap_1 @ A @ B @ E @ C ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.59/0.82    inference('cnf.neg', [status(esa)], [t82_tmap_1])).
% 0.59/0.82  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('1', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('2', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('3', plain,
% 0.59/0.82      ((m1_subset_1 @ sk_E @ 
% 0.59/0.82        (k1_zfmisc_1 @ 
% 0.59/0.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf(t78_tmap_1, axiom,
% 0.59/0.82    (![A:$i]:
% 0.59/0.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.82       ( ![B:$i]:
% 0.59/0.82         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.59/0.82             ( l1_pre_topc @ B ) ) =>
% 0.59/0.82           ( ![C:$i]:
% 0.59/0.82             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.59/0.82               ( ![D:$i]:
% 0.59/0.82                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.59/0.82                   ( ![E:$i]:
% 0.59/0.82                     ( ( ( v1_funct_1 @ E ) & 
% 0.59/0.82                         ( v1_funct_2 @
% 0.59/0.82                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.82                         ( m1_subset_1 @
% 0.59/0.82                           E @ 
% 0.59/0.82                           ( k1_zfmisc_1 @
% 0.59/0.82                             ( k2_zfmisc_1 @
% 0.59/0.82                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.82                       ( ( m1_pre_topc @ C @ D ) =>
% 0.59/0.82                         ( r2_funct_2 @
% 0.59/0.82                           ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.59/0.82                           ( k3_tmap_1 @
% 0.59/0.82                             A @ B @ D @ C @ ( k2_tmap_1 @ A @ B @ E @ D ) ) @ 
% 0.59/0.82                           ( k2_tmap_1 @ A @ B @ E @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.82  thf('4', plain,
% 0.59/0.82      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.59/0.82         ((v2_struct_0 @ X32)
% 0.59/0.82          | ~ (v2_pre_topc @ X32)
% 0.59/0.82          | ~ (l1_pre_topc @ X32)
% 0.59/0.82          | (v2_struct_0 @ X33)
% 0.59/0.82          | ~ (m1_pre_topc @ X33 @ X34)
% 0.59/0.82          | ~ (m1_pre_topc @ X35 @ X33)
% 0.59/0.82          | (r2_funct_2 @ (u1_struct_0 @ X35) @ (u1_struct_0 @ X32) @ 
% 0.59/0.82             (k3_tmap_1 @ X34 @ X32 @ X33 @ X35 @ 
% 0.59/0.82              (k2_tmap_1 @ X34 @ X32 @ X36 @ X33)) @ 
% 0.59/0.82             (k2_tmap_1 @ X34 @ X32 @ X36 @ X35))
% 0.59/0.82          | ~ (m1_subset_1 @ X36 @ 
% 0.59/0.82               (k1_zfmisc_1 @ 
% 0.59/0.82                (k2_zfmisc_1 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X32))))
% 0.59/0.82          | ~ (v1_funct_2 @ X36 @ (u1_struct_0 @ X34) @ (u1_struct_0 @ X32))
% 0.59/0.82          | ~ (v1_funct_1 @ X36)
% 0.59/0.82          | ~ (m1_pre_topc @ X35 @ X34)
% 0.59/0.82          | (v2_struct_0 @ X35)
% 0.59/0.82          | ~ (l1_pre_topc @ X34)
% 0.59/0.82          | ~ (v2_pre_topc @ X34)
% 0.59/0.82          | (v2_struct_0 @ X34))),
% 0.59/0.82      inference('cnf', [status(esa)], [t78_tmap_1])).
% 0.59/0.82  thf('5', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         ((v2_struct_0 @ sk_A)
% 0.59/0.82          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.82          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.82          | (v2_struct_0 @ X0)
% 0.59/0.82          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.82          | ~ (v1_funct_1 @ sk_E)
% 0.59/0.82          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.59/0.82          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.82             (k3_tmap_1 @ sk_A @ sk_B @ X1 @ X0 @ 
% 0.59/0.82              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1)) @ 
% 0.59/0.82             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.59/0.82          | ~ (m1_pre_topc @ X0 @ X1)
% 0.59/0.82          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.59/0.82          | (v2_struct_0 @ X1)
% 0.59/0.82          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.82          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.82          | (v2_struct_0 @ sk_B))),
% 0.59/0.82      inference('sup-', [status(thm)], ['3', '4'])).
% 0.59/0.82  thf('6', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('7', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('8', plain, ((v1_funct_1 @ sk_E)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('9', plain,
% 0.59/0.82      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('10', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('11', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('12', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         ((v2_struct_0 @ sk_A)
% 0.59/0.82          | (v2_struct_0 @ X0)
% 0.59/0.82          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.82          | (r2_funct_2 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.82             (k3_tmap_1 @ sk_A @ sk_B @ X1 @ X0 @ 
% 0.59/0.82              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X1)) @ 
% 0.59/0.82             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0))
% 0.59/0.82          | ~ (m1_pre_topc @ X0 @ X1)
% 0.59/0.82          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.59/0.82          | (v2_struct_0 @ X1)
% 0.59/0.82          | (v2_struct_0 @ sk_B))),
% 0.59/0.82      inference('demod', [status(thm)], ['5', '6', '7', '8', '9', '10', '11'])).
% 0.59/0.82  thf('13', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         ((v2_struct_0 @ sk_B)
% 0.59/0.82          | (v2_struct_0 @ X0)
% 0.59/0.82          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.82          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.59/0.82          | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.82             (k3_tmap_1 @ sk_A @ sk_B @ X0 @ sk_C @ 
% 0.59/0.82              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)) @ 
% 0.59/0.82             (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 0.59/0.82          | (v2_struct_0 @ sk_C)
% 0.59/0.82          | (v2_struct_0 @ sk_A))),
% 0.59/0.82      inference('sup-', [status(thm)], ['2', '12'])).
% 0.59/0.82  thf('14', plain,
% 0.59/0.82      (((v2_struct_0 @ sk_A)
% 0.59/0.82        | (v2_struct_0 @ sk_C)
% 0.59/0.82        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.82           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.82            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.59/0.82           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 0.59/0.82        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.59/0.82        | (v2_struct_0 @ sk_D)
% 0.59/0.82        | (v2_struct_0 @ sk_B))),
% 0.59/0.82      inference('sup-', [status(thm)], ['1', '13'])).
% 0.59/0.82  thf('15', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('16', plain,
% 0.59/0.82      (((v2_struct_0 @ sk_A)
% 0.59/0.82        | (v2_struct_0 @ sk_C)
% 0.59/0.82        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.82           (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.82            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.59/0.82           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 0.59/0.82        | (v2_struct_0 @ sk_D)
% 0.59/0.82        | (v2_struct_0 @ sk_B))),
% 0.59/0.82      inference('demod', [status(thm)], ['14', '15'])).
% 0.59/0.82  thf('17', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('18', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('19', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf(t2_tsep_1, axiom,
% 0.59/0.82    (![A:$i]: ( ( l1_pre_topc @ A ) => ( m1_pre_topc @ A @ A ) ))).
% 0.59/0.82  thf('20', plain,
% 0.59/0.82      (![X25 : $i]: ((m1_pre_topc @ X25 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.59/0.82      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.59/0.82  thf('21', plain,
% 0.59/0.82      ((m1_subset_1 @ sk_E @ 
% 0.59/0.82        (k1_zfmisc_1 @ 
% 0.59/0.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf(dt_k3_tmap_1, axiom,
% 0.59/0.82    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.59/0.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.59/0.82         ( l1_pre_topc @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.59/0.82         ( v2_pre_topc @ B ) & ( l1_pre_topc @ B ) & ( m1_pre_topc @ C @ A ) & 
% 0.59/0.82         ( m1_pre_topc @ D @ A ) & ( v1_funct_1 @ E ) & 
% 0.59/0.82         ( v1_funct_2 @ E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.82         ( m1_subset_1 @
% 0.59/0.82           E @ 
% 0.59/0.82           ( k1_zfmisc_1 @
% 0.59/0.82             ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.82       ( ( v1_funct_1 @ ( k3_tmap_1 @ A @ B @ C @ D @ E ) ) & 
% 0.59/0.82         ( v1_funct_2 @
% 0.59/0.82           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ ( u1_struct_0 @ D ) @ 
% 0.59/0.82           ( u1_struct_0 @ B ) ) & 
% 0.59/0.82         ( m1_subset_1 @
% 0.59/0.82           ( k3_tmap_1 @ A @ B @ C @ D @ E ) @ 
% 0.59/0.82           ( k1_zfmisc_1 @
% 0.59/0.82             ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.59/0.82  thf('22', plain,
% 0.59/0.82      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.82         (~ (m1_pre_topc @ X20 @ X21)
% 0.59/0.82          | ~ (m1_pre_topc @ X22 @ X21)
% 0.59/0.82          | ~ (l1_pre_topc @ X23)
% 0.59/0.82          | ~ (v2_pre_topc @ X23)
% 0.59/0.82          | (v2_struct_0 @ X23)
% 0.59/0.82          | ~ (l1_pre_topc @ X21)
% 0.59/0.82          | ~ (v2_pre_topc @ X21)
% 0.59/0.82          | (v2_struct_0 @ X21)
% 0.59/0.82          | ~ (v1_funct_1 @ X24)
% 0.59/0.82          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 0.59/0.82          | ~ (m1_subset_1 @ X24 @ 
% 0.59/0.82               (k1_zfmisc_1 @ 
% 0.59/0.82                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 0.59/0.82          | (m1_subset_1 @ (k3_tmap_1 @ X21 @ X23 @ X22 @ X20 @ X24) @ 
% 0.59/0.82             (k1_zfmisc_1 @ 
% 0.59/0.82              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X23)))))),
% 0.59/0.82      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.59/0.82  thf('23', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.59/0.82           (k1_zfmisc_1 @ 
% 0.59/0.82            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.59/0.82          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.59/0.82          | ~ (v1_funct_1 @ sk_E)
% 0.59/0.82          | (v2_struct_0 @ X1)
% 0.59/0.82          | ~ (v2_pre_topc @ X1)
% 0.59/0.82          | ~ (l1_pre_topc @ X1)
% 0.59/0.82          | (v2_struct_0 @ sk_B)
% 0.59/0.82          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.82          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.82          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.59/0.82          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.82      inference('sup-', [status(thm)], ['21', '22'])).
% 0.59/0.82  thf('24', plain,
% 0.59/0.82      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('25', plain, ((v1_funct_1 @ sk_E)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('26', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('27', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('28', plain,
% 0.59/0.82      (![X0 : $i, X1 : $i]:
% 0.59/0.82         ((m1_subset_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.59/0.82           (k1_zfmisc_1 @ 
% 0.59/0.82            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.59/0.82          | (v2_struct_0 @ X1)
% 0.59/0.82          | ~ (v2_pre_topc @ X1)
% 0.59/0.82          | ~ (l1_pre_topc @ X1)
% 0.59/0.82          | (v2_struct_0 @ sk_B)
% 0.59/0.82          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.59/0.82          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.82      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.59/0.82  thf('29', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (l1_pre_topc @ sk_A)
% 0.59/0.82          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.82          | (v2_struct_0 @ sk_B)
% 0.59/0.82          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.82          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.82          | (v2_struct_0 @ sk_A)
% 0.59/0.82          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.59/0.82             (k1_zfmisc_1 @ 
% 0.59/0.82              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.82      inference('sup-', [status(thm)], ['20', '28'])).
% 0.59/0.82  thf('30', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('31', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('32', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('33', plain,
% 0.59/0.82      (![X0 : $i]:
% 0.59/0.82         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.82          | (v2_struct_0 @ sk_B)
% 0.59/0.82          | (v2_struct_0 @ sk_A)
% 0.59/0.82          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.59/0.82             (k1_zfmisc_1 @ 
% 0.59/0.82              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.82      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.59/0.82  thf('34', plain,
% 0.59/0.82      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.59/0.82         (k1_zfmisc_1 @ 
% 0.59/0.82          (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))
% 0.59/0.82        | (v2_struct_0 @ sk_A)
% 0.59/0.82        | (v2_struct_0 @ sk_B))),
% 0.59/0.82      inference('sup-', [status(thm)], ['19', '33'])).
% 0.59/0.82  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('36', plain,
% 0.59/0.82      (((v2_struct_0 @ sk_B)
% 0.59/0.82        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.59/0.82           (k1_zfmisc_1 @ 
% 0.59/0.82            (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.82      inference('clc', [status(thm)], ['34', '35'])).
% 0.59/0.82  thf('37', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.82  thf('38', plain,
% 0.59/0.82      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.59/0.82        (k1_zfmisc_1 @ 
% 0.59/0.82         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.82      inference('clc', [status(thm)], ['36', '37'])).
% 0.59/0.82  thf(d5_tmap_1, axiom,
% 0.59/0.82    (![A:$i]:
% 0.59/0.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.82       ( ![B:$i]:
% 0.59/0.82         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.59/0.82             ( l1_pre_topc @ B ) ) =>
% 0.59/0.82           ( ![C:$i]:
% 0.59/0.82             ( ( m1_pre_topc @ C @ A ) =>
% 0.59/0.82               ( ![D:$i]:
% 0.59/0.82                 ( ( m1_pre_topc @ D @ A ) =>
% 0.59/0.82                   ( ![E:$i]:
% 0.59/0.82                     ( ( ( v1_funct_1 @ E ) & 
% 0.59/0.82                         ( v1_funct_2 @
% 0.59/0.82                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.82                         ( m1_subset_1 @
% 0.59/0.82                           E @ 
% 0.59/0.82                           ( k1_zfmisc_1 @
% 0.59/0.82                             ( k2_zfmisc_1 @
% 0.59/0.82                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.83                       ( ( m1_pre_topc @ D @ C ) =>
% 0.59/0.83                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.59/0.83                           ( k2_partfun1 @
% 0.59/0.83                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.59/0.83                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.83  thf('39', plain,
% 0.59/0.83      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.83         ((v2_struct_0 @ X15)
% 0.59/0.83          | ~ (v2_pre_topc @ X15)
% 0.59/0.83          | ~ (l1_pre_topc @ X15)
% 0.59/0.83          | ~ (m1_pre_topc @ X16 @ X17)
% 0.59/0.83          | ~ (m1_pre_topc @ X16 @ X18)
% 0.59/0.83          | ((k3_tmap_1 @ X17 @ X15 @ X18 @ X16 @ X19)
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15) @ 
% 0.59/0.83                 X19 @ (u1_struct_0 @ X16)))
% 0.59/0.83          | ~ (m1_subset_1 @ X19 @ 
% 0.59/0.83               (k1_zfmisc_1 @ 
% 0.59/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15))))
% 0.59/0.83          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15))
% 0.59/0.83          | ~ (v1_funct_1 @ X19)
% 0.59/0.83          | ~ (m1_pre_topc @ X18 @ X17)
% 0.59/0.83          | ~ (l1_pre_topc @ X17)
% 0.59/0.83          | ~ (v2_pre_topc @ X17)
% 0.59/0.83          | (v2_struct_0 @ X17))),
% 0.59/0.83      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.59/0.83  thf('40', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v2_struct_0 @ X0)
% 0.59/0.83          | ~ (v2_pre_topc @ X0)
% 0.59/0.83          | ~ (l1_pre_topc @ X0)
% 0.59/0.83          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.59/0.83          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.59/0.83          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.59/0.83               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.59/0.83              (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.59/0.83                 (u1_struct_0 @ X1)))
% 0.59/0.83          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.59/0.83          | ~ (m1_pre_topc @ X1 @ X0)
% 0.59/0.83          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.83          | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('sup-', [status(thm)], ['38', '39'])).
% 0.59/0.83  thf('41', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('42', plain,
% 0.59/0.83      (![X25 : $i]: ((m1_pre_topc @ X25 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.59/0.83      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.59/0.83  thf('43', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_E @ 
% 0.59/0.83        (k1_zfmisc_1 @ 
% 0.59/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('44', plain,
% 0.59/0.83      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.83         (~ (m1_pre_topc @ X20 @ X21)
% 0.59/0.83          | ~ (m1_pre_topc @ X22 @ X21)
% 0.59/0.83          | ~ (l1_pre_topc @ X23)
% 0.59/0.83          | ~ (v2_pre_topc @ X23)
% 0.59/0.83          | (v2_struct_0 @ X23)
% 0.59/0.83          | ~ (l1_pre_topc @ X21)
% 0.59/0.83          | ~ (v2_pre_topc @ X21)
% 0.59/0.83          | (v2_struct_0 @ X21)
% 0.59/0.83          | ~ (v1_funct_1 @ X24)
% 0.59/0.83          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 0.59/0.83          | ~ (m1_subset_1 @ X24 @ 
% 0.59/0.83               (k1_zfmisc_1 @ 
% 0.59/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 0.59/0.83          | (v1_funct_1 @ (k3_tmap_1 @ X21 @ X23 @ X22 @ X20 @ X24)))),
% 0.59/0.83      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.59/0.83  thf('45', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E))
% 0.59/0.83          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | ~ (v1_funct_1 @ sk_E)
% 0.59/0.83          | (v2_struct_0 @ X1)
% 0.59/0.83          | ~ (v2_pre_topc @ X1)
% 0.59/0.83          | ~ (l1_pre_topc @ X1)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.83          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.83          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.83      inference('sup-', [status(thm)], ['43', '44'])).
% 0.59/0.83  thf('46', plain,
% 0.59/0.83      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('47', plain, ((v1_funct_1 @ sk_E)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('48', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('49', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('50', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v1_funct_1 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E))
% 0.59/0.83          | (v2_struct_0 @ X1)
% 0.59/0.83          | ~ (v2_pre_topc @ X1)
% 0.59/0.83          | ~ (l1_pre_topc @ X1)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.83      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 0.59/0.83  thf('51', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (l1_pre_topc @ sk_A)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.83          | (v2_struct_0 @ sk_A)
% 0.59/0.83          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['42', '50'])).
% 0.59/0.83  thf('52', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('53', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('54', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('55', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | (v2_struct_0 @ sk_A)
% 0.59/0.83          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 0.59/0.83      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.59/0.83  thf('56', plain,
% 0.59/0.83      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.59/0.83        | (v2_struct_0 @ sk_A)
% 0.59/0.83        | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('sup-', [status(thm)], ['41', '55'])).
% 0.59/0.83  thf('57', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('58', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_B)
% 0.59/0.83        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)))),
% 0.59/0.83      inference('clc', [status(thm)], ['56', '57'])).
% 0.59/0.83  thf('59', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('60', plain,
% 0.59/0.83      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.59/0.83      inference('clc', [status(thm)], ['58', '59'])).
% 0.59/0.83  thf('61', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('62', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('63', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v2_struct_0 @ X0)
% 0.59/0.83          | ~ (v2_pre_topc @ X0)
% 0.59/0.83          | ~ (l1_pre_topc @ X0)
% 0.59/0.83          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.59/0.83          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.59/0.83               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.59/0.83              (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.59/0.83                 (u1_struct_0 @ X1)))
% 0.59/0.83          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.59/0.83          | ~ (m1_pre_topc @ X1 @ X0)
% 0.59/0.83          | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('demod', [status(thm)], ['40', '60', '61', '62'])).
% 0.59/0.83  thf('64', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('65', plain,
% 0.59/0.83      (![X25 : $i]: ((m1_pre_topc @ X25 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.59/0.83      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.59/0.83  thf('66', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_E @ 
% 0.59/0.83        (k1_zfmisc_1 @ 
% 0.59/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('67', plain,
% 0.59/0.83      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.59/0.83         ((v2_struct_0 @ X15)
% 0.59/0.83          | ~ (v2_pre_topc @ X15)
% 0.59/0.83          | ~ (l1_pre_topc @ X15)
% 0.59/0.83          | ~ (m1_pre_topc @ X16 @ X17)
% 0.59/0.83          | ~ (m1_pre_topc @ X16 @ X18)
% 0.59/0.83          | ((k3_tmap_1 @ X17 @ X15 @ X18 @ X16 @ X19)
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15) @ 
% 0.59/0.83                 X19 @ (u1_struct_0 @ X16)))
% 0.59/0.83          | ~ (m1_subset_1 @ X19 @ 
% 0.59/0.83               (k1_zfmisc_1 @ 
% 0.59/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15))))
% 0.59/0.83          | ~ (v1_funct_2 @ X19 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X15))
% 0.59/0.83          | ~ (v1_funct_1 @ X19)
% 0.59/0.83          | ~ (m1_pre_topc @ X18 @ X17)
% 0.59/0.83          | ~ (l1_pre_topc @ X17)
% 0.59/0.83          | ~ (v2_pre_topc @ X17)
% 0.59/0.83          | (v2_struct_0 @ X17))),
% 0.59/0.83      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.59/0.83  thf('68', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v2_struct_0 @ X0)
% 0.59/0.83          | ~ (v2_pre_topc @ X0)
% 0.59/0.83          | ~ (l1_pre_topc @ X0)
% 0.59/0.83          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.59/0.83          | ~ (v1_funct_1 @ sk_E)
% 0.59/0.83          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 sk_E @ (u1_struct_0 @ X1)))
% 0.59/0.83          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.59/0.83          | ~ (m1_pre_topc @ X1 @ X0)
% 0.59/0.83          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.83          | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('sup-', [status(thm)], ['66', '67'])).
% 0.59/0.83  thf('69', plain, ((v1_funct_1 @ sk_E)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('70', plain,
% 0.59/0.83      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('71', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('72', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('73', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v2_struct_0 @ X0)
% 0.59/0.83          | ~ (v2_pre_topc @ X0)
% 0.59/0.83          | ~ (l1_pre_topc @ X0)
% 0.59/0.83          | ~ (m1_pre_topc @ sk_A @ X0)
% 0.59/0.83          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_E)
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 sk_E @ (u1_struct_0 @ X1)))
% 0.59/0.83          | ~ (m1_pre_topc @ X1 @ sk_A)
% 0.59/0.83          | ~ (m1_pre_topc @ X1 @ X0)
% 0.59/0.83          | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('demod', [status(thm)], ['68', '69', '70', '71', '72'])).
% 0.59/0.83  thf('74', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (l1_pre_topc @ sk_A)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 sk_E @ (u1_struct_0 @ X0)))
% 0.59/0.83          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.83          | (v2_struct_0 @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['65', '73'])).
% 0.59/0.83  thf('75', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('76', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('77', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('78', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 sk_E @ (u1_struct_0 @ X0)))
% 0.59/0.83          | (v2_struct_0 @ sk_A))),
% 0.59/0.83      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 0.59/0.83  thf('79', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((v2_struct_0 @ sk_A)
% 0.59/0.83          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 sk_E @ (u1_struct_0 @ X0)))
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('simplify', [status(thm)], ['78'])).
% 0.59/0.83  thf('80', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_B)
% 0.59/0.83        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 0.59/0.83            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83               sk_E @ (u1_struct_0 @ sk_D)))
% 0.59/0.83        | (v2_struct_0 @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['64', '79'])).
% 0.59/0.83  thf('81', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('82', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_A)
% 0.59/0.83        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 0.59/0.83            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83               sk_E @ (u1_struct_0 @ sk_D))))),
% 0.59/0.83      inference('clc', [status(thm)], ['80', '81'])).
% 0.59/0.83  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('84', plain,
% 0.59/0.83      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)
% 0.59/0.83         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.59/0.83            (u1_struct_0 @ sk_D)))),
% 0.59/0.83      inference('clc', [status(thm)], ['82', '83'])).
% 0.59/0.83  thf('85', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('86', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_E @ 
% 0.59/0.83        (k1_zfmisc_1 @ 
% 0.59/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(d4_tmap_1, axiom,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.83       ( ![B:$i]:
% 0.59/0.83         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.59/0.83             ( l1_pre_topc @ B ) ) =>
% 0.59/0.83           ( ![C:$i]:
% 0.59/0.83             ( ( ( v1_funct_1 @ C ) & 
% 0.59/0.83                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.59/0.83                 ( m1_subset_1 @
% 0.59/0.83                   C @ 
% 0.59/0.83                   ( k1_zfmisc_1 @
% 0.59/0.83                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.59/0.83               ( ![D:$i]:
% 0.59/0.83                 ( ( m1_pre_topc @ D @ A ) =>
% 0.59/0.83                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.59/0.83                     ( k2_partfun1 @
% 0.59/0.83                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.59/0.83                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.83  thf('87', plain,
% 0.59/0.83      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.59/0.83         ((v2_struct_0 @ X11)
% 0.59/0.83          | ~ (v2_pre_topc @ X11)
% 0.59/0.83          | ~ (l1_pre_topc @ X11)
% 0.59/0.83          | ~ (m1_pre_topc @ X12 @ X13)
% 0.59/0.83          | ((k2_tmap_1 @ X13 @ X11 @ X14 @ X12)
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ 
% 0.59/0.83                 X14 @ (u1_struct_0 @ X12)))
% 0.59/0.83          | ~ (m1_subset_1 @ X14 @ 
% 0.59/0.83               (k1_zfmisc_1 @ 
% 0.59/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.59/0.83          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.59/0.83          | ~ (v1_funct_1 @ X14)
% 0.59/0.83          | ~ (l1_pre_topc @ X13)
% 0.59/0.83          | ~ (v2_pre_topc @ X13)
% 0.59/0.83          | (v2_struct_0 @ X13))),
% 0.59/0.83      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.59/0.83  thf('88', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((v2_struct_0 @ sk_A)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.83          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.83          | ~ (v1_funct_1 @ sk_E)
% 0.59/0.83          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 sk_E @ (u1_struct_0 @ X0)))
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.83          | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('sup-', [status(thm)], ['86', '87'])).
% 0.59/0.83  thf('89', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('90', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('91', plain, ((v1_funct_1 @ sk_E)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('92', plain,
% 0.59/0.83      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('93', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('94', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('95', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((v2_struct_0 @ sk_A)
% 0.59/0.83          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 sk_E @ (u1_struct_0 @ X0)))
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('demod', [status(thm)],
% 0.59/0.83                ['88', '89', '90', '91', '92', '93', '94'])).
% 0.59/0.83  thf('96', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_B)
% 0.59/0.83        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.59/0.83            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83               sk_E @ (u1_struct_0 @ sk_D)))
% 0.59/0.83        | (v2_struct_0 @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['85', '95'])).
% 0.59/0.83  thf('97', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('98', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_A)
% 0.59/0.83        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.59/0.83            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83               sk_E @ (u1_struct_0 @ sk_D))))),
% 0.59/0.83      inference('clc', [status(thm)], ['96', '97'])).
% 0.59/0.83  thf('99', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('100', plain,
% 0.59/0.83      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.59/0.83         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.59/0.83            (u1_struct_0 @ sk_D)))),
% 0.59/0.83      inference('clc', [status(thm)], ['98', '99'])).
% 0.59/0.83  thf('101', plain,
% 0.59/0.83      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.59/0.83         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.59/0.83      inference('sup+', [status(thm)], ['84', '100'])).
% 0.59/0.83  thf('102', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('103', plain,
% 0.59/0.83      (![X25 : $i]: ((m1_pre_topc @ X25 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.59/0.83      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.59/0.83  thf('104', plain,
% 0.59/0.83      ((m1_subset_1 @ sk_E @ 
% 0.59/0.83        (k1_zfmisc_1 @ 
% 0.59/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('105', plain,
% 0.59/0.83      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.83         (~ (m1_pre_topc @ X20 @ X21)
% 0.59/0.83          | ~ (m1_pre_topc @ X22 @ X21)
% 0.59/0.83          | ~ (l1_pre_topc @ X23)
% 0.59/0.83          | ~ (v2_pre_topc @ X23)
% 0.59/0.83          | (v2_struct_0 @ X23)
% 0.59/0.83          | ~ (l1_pre_topc @ X21)
% 0.59/0.83          | ~ (v2_pre_topc @ X21)
% 0.59/0.83          | (v2_struct_0 @ X21)
% 0.59/0.83          | ~ (v1_funct_1 @ X24)
% 0.59/0.83          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 0.59/0.83          | ~ (m1_subset_1 @ X24 @ 
% 0.59/0.83               (k1_zfmisc_1 @ 
% 0.59/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 0.59/0.83          | (v1_funct_2 @ (k3_tmap_1 @ X21 @ X23 @ X22 @ X20 @ X24) @ 
% 0.59/0.83             (u1_struct_0 @ X20) @ (u1_struct_0 @ X23)))),
% 0.59/0.83      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.59/0.83  thf('106', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.59/0.83           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | ~ (v1_funct_1 @ sk_E)
% 0.59/0.83          | (v2_struct_0 @ X1)
% 0.59/0.83          | ~ (v2_pre_topc @ X1)
% 0.59/0.83          | ~ (l1_pre_topc @ X1)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.83          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.83          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.83      inference('sup-', [status(thm)], ['104', '105'])).
% 0.59/0.83  thf('107', plain,
% 0.59/0.83      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('108', plain, ((v1_funct_1 @ sk_E)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('109', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('110', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('111', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v1_funct_2 @ (k3_tmap_1 @ X1 @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.59/0.83           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | (v2_struct_0 @ X1)
% 0.59/0.83          | ~ (v2_pre_topc @ X1)
% 0.59/0.83          | ~ (l1_pre_topc @ X1)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (m1_pre_topc @ sk_A @ X1)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.83      inference('demod', [status(thm)], ['106', '107', '108', '109', '110'])).
% 0.59/0.83  thf('112', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (l1_pre_topc @ sk_A)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.83          | (v2_struct_0 @ sk_A)
% 0.59/0.83          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.59/0.83             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['103', '111'])).
% 0.59/0.83  thf('113', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('114', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('115', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('116', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | (v2_struct_0 @ sk_A)
% 0.59/0.83          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.59/0.83             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.59/0.83      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 0.59/0.83  thf('117', plain,
% 0.59/0.83      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.59/0.83         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.59/0.83        | (v2_struct_0 @ sk_A)
% 0.59/0.83        | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('sup-', [status(thm)], ['102', '116'])).
% 0.59/0.83  thf('118', plain,
% 0.59/0.83      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.59/0.83         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.59/0.83      inference('sup+', [status(thm)], ['84', '100'])).
% 0.59/0.83  thf('119', plain,
% 0.59/0.83      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83         (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.59/0.83        | (v2_struct_0 @ sk_A)
% 0.59/0.83        | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('demod', [status(thm)], ['117', '118'])).
% 0.59/0.83  thf('120', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('121', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_B)
% 0.59/0.83        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83           (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B)))),
% 0.59/0.83      inference('clc', [status(thm)], ['119', '120'])).
% 0.59/0.83  thf('122', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('123', plain,
% 0.59/0.83      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.59/0.83      inference('clc', [status(thm)], ['121', '122'])).
% 0.59/0.83  thf('124', plain,
% 0.59/0.83      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.59/0.83         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.59/0.83      inference('sup+', [status(thm)], ['84', '100'])).
% 0.59/0.83  thf('125', plain,
% 0.59/0.83      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.59/0.83         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.59/0.83      inference('sup+', [status(thm)], ['84', '100'])).
% 0.59/0.83  thf('126', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v2_struct_0 @ X0)
% 0.59/0.83          | ~ (v2_pre_topc @ X0)
% 0.59/0.83          | ~ (l1_pre_topc @ X0)
% 0.59/0.83          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.59/0.83          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.59/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X1)))
% 0.59/0.83          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.59/0.83          | ~ (m1_pre_topc @ X1 @ X0)
% 0.59/0.83          | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('demod', [status(thm)], ['63', '101', '123', '124', '125'])).
% 0.59/0.83  thf('127', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.83          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.59/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 0.59/0.83          | ~ (l1_pre_topc @ sk_A)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_A)
% 0.59/0.83          | (v2_struct_0 @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['18', '126'])).
% 0.59/0.83  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('129', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('130', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.83          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ 
% 0.59/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 0.59/0.83          | (v2_struct_0 @ sk_A))),
% 0.59/0.83      inference('demod', [status(thm)], ['127', '128', '129'])).
% 0.59/0.83  thf('131', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_A)
% 0.59/0.83        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.59/0.83            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C)))
% 0.59/0.83        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.59/0.83        | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('sup-', [status(thm)], ['17', '130'])).
% 0.59/0.83  thf('132', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('133', plain,
% 0.59/0.83      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.59/0.83        (k1_zfmisc_1 @ 
% 0.59/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.83      inference('clc', [status(thm)], ['36', '37'])).
% 0.59/0.83  thf('134', plain,
% 0.59/0.83      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.59/0.83         ((v2_struct_0 @ X11)
% 0.59/0.83          | ~ (v2_pre_topc @ X11)
% 0.59/0.83          | ~ (l1_pre_topc @ X11)
% 0.59/0.83          | ~ (m1_pre_topc @ X12 @ X13)
% 0.59/0.83          | ((k2_tmap_1 @ X13 @ X11 @ X14 @ X12)
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11) @ 
% 0.59/0.83                 X14 @ (u1_struct_0 @ X12)))
% 0.59/0.83          | ~ (m1_subset_1 @ X14 @ 
% 0.59/0.83               (k1_zfmisc_1 @ 
% 0.59/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.59/0.83          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.59/0.83          | ~ (v1_funct_1 @ X14)
% 0.59/0.83          | ~ (l1_pre_topc @ X13)
% 0.59/0.83          | ~ (v2_pre_topc @ X13)
% 0.59/0.83          | (v2_struct_0 @ X13))),
% 0.59/0.83      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.59/0.83  thf('135', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((v2_struct_0 @ sk_D)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_D)
% 0.59/0.83          | ~ (l1_pre_topc @ sk_D)
% 0.59/0.83          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.59/0.83          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.59/0.83               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.59/0.83              (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ X0)
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.59/0.83                 (u1_struct_0 @ X0)))
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.83          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.83          | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('sup-', [status(thm)], ['133', '134'])).
% 0.59/0.83  thf('136', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(cc1_pre_topc, axiom,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.59/0.83       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.59/0.83  thf('137', plain,
% 0.59/0.83      (![X4 : $i, X5 : $i]:
% 0.59/0.83         (~ (m1_pre_topc @ X4 @ X5)
% 0.59/0.83          | (v2_pre_topc @ X4)
% 0.59/0.83          | ~ (l1_pre_topc @ X5)
% 0.59/0.83          | ~ (v2_pre_topc @ X5))),
% 0.59/0.83      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.59/0.83  thf('138', plain,
% 0.59/0.83      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.59/0.83      inference('sup-', [status(thm)], ['136', '137'])).
% 0.59/0.83  thf('139', plain, ((v2_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('140', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('141', plain, ((v2_pre_topc @ sk_D)),
% 0.59/0.83      inference('demod', [status(thm)], ['138', '139', '140'])).
% 0.59/0.83  thf('142', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(dt_m1_pre_topc, axiom,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( l1_pre_topc @ A ) =>
% 0.59/0.83       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.59/0.83  thf('143', plain,
% 0.59/0.83      (![X6 : $i, X7 : $i]:
% 0.59/0.83         (~ (m1_pre_topc @ X6 @ X7) | (l1_pre_topc @ X6) | ~ (l1_pre_topc @ X7))),
% 0.59/0.83      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.59/0.83  thf('144', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.59/0.83      inference('sup-', [status(thm)], ['142', '143'])).
% 0.59/0.83  thf('145', plain, ((l1_pre_topc @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('146', plain, ((l1_pre_topc @ sk_D)),
% 0.59/0.83      inference('demod', [status(thm)], ['144', '145'])).
% 0.59/0.83  thf('147', plain,
% 0.59/0.83      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.59/0.83      inference('clc', [status(thm)], ['58', '59'])).
% 0.59/0.83  thf('148', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('149', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('150', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((v2_struct_0 @ sk_D)
% 0.59/0.83          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.59/0.83               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.59/0.83              (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ X0)
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.59/0.83                 (u1_struct_0 @ X0)))
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.83          | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('demod', [status(thm)],
% 0.59/0.83                ['135', '141', '146', '147', '148', '149'])).
% 0.59/0.83  thf('151', plain,
% 0.59/0.83      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.59/0.83         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.59/0.83      inference('sup+', [status(thm)], ['84', '100'])).
% 0.59/0.83  thf('152', plain,
% 0.59/0.83      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.59/0.83         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.59/0.83      inference('sup+', [status(thm)], ['84', '100'])).
% 0.59/0.83  thf('153', plain,
% 0.59/0.83      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.59/0.83         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.59/0.83      inference('sup+', [status(thm)], ['84', '100'])).
% 0.59/0.83  thf('154', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((v2_struct_0 @ sk_D)
% 0.59/0.83          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.59/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X0)
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.83          | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('demod', [status(thm)], ['150', '151', '152', '153'])).
% 0.59/0.83  thf('155', plain,
% 0.59/0.83      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.59/0.83      inference('clc', [status(thm)], ['121', '122'])).
% 0.59/0.83  thf('156', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((v2_struct_0 @ sk_D)
% 0.59/0.83          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.59/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X0)
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.83          | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('demod', [status(thm)], ['154', '155'])).
% 0.59/0.83  thf('157', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_B)
% 0.59/0.83        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C)
% 0.59/0.83            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C)))
% 0.59/0.83        | (v2_struct_0 @ sk_D))),
% 0.59/0.83      inference('sup-', [status(thm)], ['132', '156'])).
% 0.59/0.83  thf('158', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('159', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_D)
% 0.59/0.83        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C)
% 0.59/0.83            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C))))),
% 0.59/0.83      inference('clc', [status(thm)], ['157', '158'])).
% 0.59/0.83  thf('160', plain, (~ (v2_struct_0 @ sk_D)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('161', plain,
% 0.59/0.83      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83         sk_C)
% 0.59/0.83         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.59/0.83      inference('clc', [status(thm)], ['159', '160'])).
% 0.59/0.83  thf('162', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('163', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_A)
% 0.59/0.83        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.59/0.83            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.59/0.83               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C))
% 0.59/0.83        | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('demod', [status(thm)], ['131', '161', '162'])).
% 0.59/0.83  thf('164', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('165', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_B)
% 0.59/0.83        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.59/0.83            = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.59/0.83               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C)))),
% 0.59/0.83      inference('clc', [status(thm)], ['163', '164'])).
% 0.59/0.83  thf('166', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('167', plain,
% 0.59/0.83      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.83         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.59/0.83         = (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C))),
% 0.59/0.83      inference('clc', [status(thm)], ['165', '166'])).
% 0.59/0.83  thf('168', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_A)
% 0.59/0.83        | (v2_struct_0 @ sk_C)
% 0.59/0.83        | (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83           (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) @ 
% 0.59/0.83           (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 0.59/0.83        | (v2_struct_0 @ sk_D)
% 0.59/0.83        | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('demod', [status(thm)], ['16', '167'])).
% 0.59/0.83  thf('169', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('170', plain,
% 0.59/0.83      (![X25 : $i]: ((m1_pre_topc @ X25 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.59/0.83      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.59/0.83  thf('171', plain,
% 0.59/0.83      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.59/0.83        (k1_zfmisc_1 @ 
% 0.59/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.83      inference('clc', [status(thm)], ['36', '37'])).
% 0.59/0.83  thf('172', plain,
% 0.59/0.83      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.83         (~ (m1_pre_topc @ X20 @ X21)
% 0.59/0.83          | ~ (m1_pre_topc @ X22 @ X21)
% 0.59/0.83          | ~ (l1_pre_topc @ X23)
% 0.59/0.83          | ~ (v2_pre_topc @ X23)
% 0.59/0.83          | (v2_struct_0 @ X23)
% 0.59/0.83          | ~ (l1_pre_topc @ X21)
% 0.59/0.83          | ~ (v2_pre_topc @ X21)
% 0.59/0.83          | (v2_struct_0 @ X21)
% 0.59/0.83          | ~ (v1_funct_1 @ X24)
% 0.59/0.83          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 0.59/0.83          | ~ (m1_subset_1 @ X24 @ 
% 0.59/0.83               (k1_zfmisc_1 @ 
% 0.59/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 0.59/0.83          | (m1_subset_1 @ (k3_tmap_1 @ X21 @ X23 @ X22 @ X20 @ X24) @ 
% 0.59/0.83             (k1_zfmisc_1 @ 
% 0.59/0.83              (k2_zfmisc_1 @ (u1_struct_0 @ X20) @ (u1_struct_0 @ X23)))))),
% 0.59/0.83      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.59/0.83  thf('173', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((m1_subset_1 @ 
% 0.59/0.83           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.59/0.83            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)) @ 
% 0.59/0.83           (k1_zfmisc_1 @ 
% 0.59/0.83            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.59/0.83          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.59/0.83               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | ~ (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))
% 0.59/0.83          | (v2_struct_0 @ X1)
% 0.59/0.83          | ~ (v2_pre_topc @ X1)
% 0.59/0.83          | ~ (l1_pre_topc @ X1)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.83          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.83          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.83      inference('sup-', [status(thm)], ['171', '172'])).
% 0.59/0.83  thf('174', plain,
% 0.59/0.83      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.59/0.83      inference('clc', [status(thm)], ['58', '59'])).
% 0.59/0.83  thf('175', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('176', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('177', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((m1_subset_1 @ 
% 0.59/0.83           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.59/0.83            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E)) @ 
% 0.59/0.83           (k1_zfmisc_1 @ 
% 0.59/0.83            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.59/0.83          | ~ (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.59/0.83               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | (v2_struct_0 @ X1)
% 0.59/0.83          | ~ (v2_pre_topc @ X1)
% 0.59/0.83          | ~ (l1_pre_topc @ X1)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.83      inference('demod', [status(thm)], ['173', '174', '175', '176'])).
% 0.59/0.83  thf('178', plain,
% 0.59/0.83      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.59/0.83         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.59/0.83      inference('sup+', [status(thm)], ['84', '100'])).
% 0.59/0.83  thf('179', plain,
% 0.59/0.83      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.59/0.83         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.59/0.83      inference('sup+', [status(thm)], ['84', '100'])).
% 0.59/0.83  thf('180', plain,
% 0.59/0.83      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.59/0.83      inference('clc', [status(thm)], ['121', '122'])).
% 0.59/0.83  thf('181', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((m1_subset_1 @ 
% 0.59/0.83           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.59/0.83           (k1_zfmisc_1 @ 
% 0.59/0.83            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))))
% 0.59/0.83          | (v2_struct_0 @ X1)
% 0.59/0.83          | ~ (v2_pre_topc @ X1)
% 0.59/0.83          | ~ (l1_pre_topc @ X1)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.83      inference('demod', [status(thm)], ['177', '178', '179', '180'])).
% 0.59/0.83  thf('182', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (l1_pre_topc @ sk_D)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (l1_pre_topc @ sk_D)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_D)
% 0.59/0.83          | (v2_struct_0 @ sk_D)
% 0.59/0.83          | (m1_subset_1 @ 
% 0.59/0.83             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 0.59/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.59/0.83             (k1_zfmisc_1 @ 
% 0.59/0.83              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.83      inference('sup-', [status(thm)], ['170', '181'])).
% 0.59/0.83  thf('183', plain, ((l1_pre_topc @ sk_D)),
% 0.59/0.83      inference('demod', [status(thm)], ['144', '145'])).
% 0.59/0.83  thf('184', plain, ((l1_pre_topc @ sk_D)),
% 0.59/0.83      inference('demod', [status(thm)], ['144', '145'])).
% 0.59/0.83  thf('185', plain, ((v2_pre_topc @ sk_D)),
% 0.59/0.83      inference('demod', [status(thm)], ['138', '139', '140'])).
% 0.59/0.83  thf('186', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | (v2_struct_0 @ sk_D)
% 0.59/0.83          | (m1_subset_1 @ 
% 0.59/0.83             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 0.59/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.59/0.83             (k1_zfmisc_1 @ 
% 0.59/0.83              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.83      inference('demod', [status(thm)], ['182', '183', '184', '185'])).
% 0.59/0.83  thf('187', plain,
% 0.59/0.83      (((m1_subset_1 @ 
% 0.59/0.83         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.83          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.59/0.83         (k1_zfmisc_1 @ 
% 0.59/0.83          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.59/0.83        | (v2_struct_0 @ sk_D)
% 0.59/0.83        | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('sup-', [status(thm)], ['169', '186'])).
% 0.59/0.83  thf('188', plain, (~ (v2_struct_0 @ sk_D)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('189', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_B)
% 0.59/0.83        | (m1_subset_1 @ 
% 0.59/0.83           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.59/0.83           (k1_zfmisc_1 @ 
% 0.59/0.83            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.83      inference('clc', [status(thm)], ['187', '188'])).
% 0.59/0.83  thf('190', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('191', plain,
% 0.59/0.83      ((m1_subset_1 @ 
% 0.59/0.83        (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.83         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.59/0.83        (k1_zfmisc_1 @ 
% 0.59/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.83      inference('clc', [status(thm)], ['189', '190'])).
% 0.59/0.83  thf('192', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('193', plain,
% 0.59/0.83      (![X25 : $i]: ((m1_pre_topc @ X25 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.59/0.83      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.59/0.83  thf('194', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v2_struct_0 @ X0)
% 0.59/0.83          | ~ (v2_pre_topc @ X0)
% 0.59/0.83          | ~ (l1_pre_topc @ X0)
% 0.59/0.83          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.59/0.83          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ 
% 0.59/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X1)))
% 0.59/0.83          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.59/0.83          | ~ (m1_pre_topc @ X1 @ X0)
% 0.59/0.83          | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('demod', [status(thm)], ['63', '101', '123', '124', '125'])).
% 0.59/0.83  thf('195', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (l1_pre_topc @ sk_D)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.83          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 0.59/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 0.59/0.83          | ~ (l1_pre_topc @ sk_D)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_D)
% 0.59/0.83          | (v2_struct_0 @ sk_D))),
% 0.59/0.83      inference('sup-', [status(thm)], ['193', '194'])).
% 0.59/0.83  thf('196', plain, ((l1_pre_topc @ sk_D)),
% 0.59/0.83      inference('demod', [status(thm)], ['144', '145'])).
% 0.59/0.83  thf('197', plain, ((l1_pre_topc @ sk_D)),
% 0.59/0.83      inference('demod', [status(thm)], ['144', '145'])).
% 0.59/0.83  thf('198', plain, ((v2_pre_topc @ sk_D)),
% 0.59/0.83      inference('demod', [status(thm)], ['138', '139', '140'])).
% 0.59/0.83  thf('199', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.83          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 0.59/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 0.59/0.83          | (v2_struct_0 @ sk_D))),
% 0.59/0.83      inference('demod', [status(thm)], ['195', '196', '197', '198'])).
% 0.59/0.83  thf('200', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((v2_struct_0 @ sk_D)
% 0.59/0.83          | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 0.59/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ X0)))
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.83          | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('simplify', [status(thm)], ['199'])).
% 0.59/0.83  thf('201', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_B)
% 0.59/0.83        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.59/0.83            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C)))
% 0.59/0.83        | (v2_struct_0 @ sk_D))),
% 0.59/0.83      inference('sup-', [status(thm)], ['192', '200'])).
% 0.59/0.83  thf('202', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('203', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_D)
% 0.59/0.83        | ((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.59/0.83            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C))))),
% 0.59/0.83      inference('clc', [status(thm)], ['201', '202'])).
% 0.59/0.83  thf('204', plain, (~ (v2_struct_0 @ sk_D)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('205', plain,
% 0.59/0.83      (((k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.83         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.59/0.83         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.59/0.83      inference('clc', [status(thm)], ['203', '204'])).
% 0.59/0.83  thf('206', plain,
% 0.59/0.83      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83         sk_C)
% 0.59/0.83         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ (u1_struct_0 @ sk_C)))),
% 0.59/0.83      inference('clc', [status(thm)], ['159', '160'])).
% 0.59/0.83  thf('207', plain,
% 0.59/0.83      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83         sk_C)
% 0.59/0.83         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['205', '206'])).
% 0.59/0.83  thf('208', plain,
% 0.59/0.83      ((m1_subset_1 @ 
% 0.59/0.83        (k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83         sk_C) @ 
% 0.59/0.83        (k1_zfmisc_1 @ 
% 0.59/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.83      inference('demod', [status(thm)], ['191', '207'])).
% 0.59/0.83  thf(redefinition_r2_funct_2, axiom,
% 0.59/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.83     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.59/0.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.59/0.83         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.59/0.83         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.83       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.59/0.83  thf('209', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.83         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.59/0.83          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.59/0.83          | ~ (v1_funct_1 @ X0)
% 0.59/0.83          | ~ (v1_funct_1 @ X3)
% 0.59/0.83          | ~ (v1_funct_2 @ X3 @ X1 @ X2)
% 0.59/0.83          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.59/0.83          | ((X0) = (X3))
% 0.59/0.83          | ~ (r2_funct_2 @ X1 @ X2 @ X0 @ X3))),
% 0.59/0.83      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.59/0.83  thf('210', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83             (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.59/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) @ 
% 0.59/0.83             X0)
% 0.59/0.83          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.59/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) = (X0))
% 0.59/0.83          | ~ (m1_subset_1 @ X0 @ 
% 0.59/0.83               (k1_zfmisc_1 @ 
% 0.59/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.59/0.83          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | ~ (v1_funct_1 @ X0)
% 0.59/0.83          | ~ (v1_funct_1 @ 
% 0.59/0.83               (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.59/0.83                (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C))
% 0.59/0.83          | ~ (v1_funct_2 @ 
% 0.59/0.83               (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.59/0.83                (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) @ 
% 0.59/0.83               (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['208', '209'])).
% 0.59/0.83  thf('211', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('212', plain,
% 0.59/0.83      (![X25 : $i]: ((m1_pre_topc @ X25 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.59/0.83      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.59/0.83  thf('213', plain,
% 0.59/0.83      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E) @ 
% 0.59/0.83        (k1_zfmisc_1 @ 
% 0.59/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.83      inference('clc', [status(thm)], ['36', '37'])).
% 0.59/0.83  thf('214', plain,
% 0.59/0.83      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.59/0.83         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.59/0.83      inference('sup+', [status(thm)], ['84', '100'])).
% 0.59/0.83  thf('215', plain,
% 0.59/0.83      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83        (k1_zfmisc_1 @ 
% 0.59/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.83      inference('demod', [status(thm)], ['213', '214'])).
% 0.59/0.83  thf('216', plain,
% 0.59/0.83      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.83         (~ (m1_pre_topc @ X20 @ X21)
% 0.59/0.83          | ~ (m1_pre_topc @ X22 @ X21)
% 0.59/0.83          | ~ (l1_pre_topc @ X23)
% 0.59/0.83          | ~ (v2_pre_topc @ X23)
% 0.59/0.83          | (v2_struct_0 @ X23)
% 0.59/0.83          | ~ (l1_pre_topc @ X21)
% 0.59/0.83          | ~ (v2_pre_topc @ X21)
% 0.59/0.83          | (v2_struct_0 @ X21)
% 0.59/0.83          | ~ (v1_funct_1 @ X24)
% 0.59/0.83          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 0.59/0.83          | ~ (m1_subset_1 @ X24 @ 
% 0.59/0.83               (k1_zfmisc_1 @ 
% 0.59/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 0.59/0.83          | (v1_funct_1 @ (k3_tmap_1 @ X21 @ X23 @ X22 @ X20 @ X24)))),
% 0.59/0.83      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.59/0.83  thf('217', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v1_funct_1 @ 
% 0.59/0.83           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 0.59/0.83          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.59/0.83          | (v2_struct_0 @ X1)
% 0.59/0.83          | ~ (v2_pre_topc @ X1)
% 0.59/0.83          | ~ (l1_pre_topc @ X1)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.83          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.83          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.83      inference('sup-', [status(thm)], ['215', '216'])).
% 0.59/0.83  thf('218', plain,
% 0.59/0.83      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.59/0.83      inference('clc', [status(thm)], ['58', '59'])).
% 0.59/0.83  thf('219', plain,
% 0.59/0.83      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)
% 0.59/0.83         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_E))),
% 0.59/0.83      inference('sup+', [status(thm)], ['84', '100'])).
% 0.59/0.83  thf('220', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 0.59/0.83      inference('demod', [status(thm)], ['218', '219'])).
% 0.59/0.83  thf('221', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('222', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('223', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v1_funct_1 @ 
% 0.59/0.83           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 0.59/0.83          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | (v2_struct_0 @ X1)
% 0.59/0.83          | ~ (v2_pre_topc @ X1)
% 0.59/0.83          | ~ (l1_pre_topc @ X1)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.83      inference('demod', [status(thm)], ['217', '220', '221', '222'])).
% 0.59/0.83  thf('224', plain,
% 0.59/0.83      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.59/0.83      inference('clc', [status(thm)], ['121', '122'])).
% 0.59/0.83  thf('225', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v1_funct_1 @ 
% 0.59/0.83           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 0.59/0.83          | (v2_struct_0 @ X1)
% 0.59/0.83          | ~ (v2_pre_topc @ X1)
% 0.59/0.83          | ~ (l1_pre_topc @ X1)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.83      inference('demod', [status(thm)], ['223', '224'])).
% 0.59/0.83  thf('226', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (l1_pre_topc @ sk_D)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (l1_pre_topc @ sk_D)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_D)
% 0.59/0.83          | (v2_struct_0 @ sk_D)
% 0.59/0.83          | (v1_funct_1 @ 
% 0.59/0.83             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 0.59/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 0.59/0.83      inference('sup-', [status(thm)], ['212', '225'])).
% 0.59/0.83  thf('227', plain, ((l1_pre_topc @ sk_D)),
% 0.59/0.83      inference('demod', [status(thm)], ['144', '145'])).
% 0.59/0.83  thf('228', plain, ((l1_pre_topc @ sk_D)),
% 0.59/0.83      inference('demod', [status(thm)], ['144', '145'])).
% 0.59/0.83  thf('229', plain, ((v2_pre_topc @ sk_D)),
% 0.59/0.83      inference('demod', [status(thm)], ['138', '139', '140'])).
% 0.59/0.83  thf('230', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | (v2_struct_0 @ sk_D)
% 0.59/0.83          | (v1_funct_1 @ 
% 0.59/0.83             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 0.59/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 0.59/0.83      inference('demod', [status(thm)], ['226', '227', '228', '229'])).
% 0.59/0.83  thf('231', plain,
% 0.59/0.83      (((v1_funct_1 @ 
% 0.59/0.83         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.83          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))
% 0.59/0.83        | (v2_struct_0 @ sk_D)
% 0.59/0.83        | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('sup-', [status(thm)], ['211', '230'])).
% 0.59/0.83  thf('232', plain, (~ (v2_struct_0 @ sk_D)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('233', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_B)
% 0.59/0.83        | (v1_funct_1 @ 
% 0.59/0.83           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))))),
% 0.59/0.83      inference('clc', [status(thm)], ['231', '232'])).
% 0.59/0.83  thf('234', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('235', plain,
% 0.59/0.83      ((v1_funct_1 @ 
% 0.59/0.83        (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.83         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 0.59/0.83      inference('clc', [status(thm)], ['233', '234'])).
% 0.59/0.83  thf('236', plain,
% 0.59/0.83      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83         sk_C)
% 0.59/0.83         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['205', '206'])).
% 0.59/0.83  thf('237', plain,
% 0.59/0.83      ((v1_funct_1 @ 
% 0.59/0.83        (k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83         sk_C))),
% 0.59/0.83      inference('demod', [status(thm)], ['235', '236'])).
% 0.59/0.83  thf('238', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('239', plain,
% 0.59/0.83      (![X25 : $i]: ((m1_pre_topc @ X25 @ X25) | ~ (l1_pre_topc @ X25))),
% 0.59/0.83      inference('cnf', [status(esa)], [t2_tsep_1])).
% 0.59/0.83  thf('240', plain,
% 0.59/0.83      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83        (k1_zfmisc_1 @ 
% 0.59/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.59/0.83      inference('demod', [status(thm)], ['213', '214'])).
% 0.59/0.83  thf('241', plain,
% 0.59/0.83      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.59/0.83         (~ (m1_pre_topc @ X20 @ X21)
% 0.59/0.83          | ~ (m1_pre_topc @ X22 @ X21)
% 0.59/0.83          | ~ (l1_pre_topc @ X23)
% 0.59/0.83          | ~ (v2_pre_topc @ X23)
% 0.59/0.83          | (v2_struct_0 @ X23)
% 0.59/0.83          | ~ (l1_pre_topc @ X21)
% 0.59/0.83          | ~ (v2_pre_topc @ X21)
% 0.59/0.83          | (v2_struct_0 @ X21)
% 0.59/0.83          | ~ (v1_funct_1 @ X24)
% 0.59/0.83          | ~ (v1_funct_2 @ X24 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))
% 0.59/0.83          | ~ (m1_subset_1 @ X24 @ 
% 0.59/0.83               (k1_zfmisc_1 @ 
% 0.59/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X22) @ (u1_struct_0 @ X23))))
% 0.59/0.83          | (v1_funct_2 @ (k3_tmap_1 @ X21 @ X23 @ X22 @ X20 @ X24) @ 
% 0.59/0.83             (u1_struct_0 @ X20) @ (u1_struct_0 @ X23)))),
% 0.59/0.83      inference('cnf', [status(esa)], [dt_k3_tmap_1])).
% 0.59/0.83  thf('242', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v1_funct_2 @ 
% 0.59/0.83           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.59/0.83           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.59/0.83          | (v2_struct_0 @ X1)
% 0.59/0.83          | ~ (v2_pre_topc @ X1)
% 0.59/0.83          | ~ (l1_pre_topc @ X1)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_B)
% 0.59/0.83          | ~ (l1_pre_topc @ sk_B)
% 0.59/0.83          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.83      inference('sup-', [status(thm)], ['240', '241'])).
% 0.59/0.83  thf('243', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 0.59/0.83      inference('demod', [status(thm)], ['218', '219'])).
% 0.59/0.83  thf('244', plain, ((v2_pre_topc @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('245', plain, ((l1_pre_topc @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('246', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v1_funct_2 @ 
% 0.59/0.83           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.59/0.83           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | (v2_struct_0 @ X1)
% 0.59/0.83          | ~ (v2_pre_topc @ X1)
% 0.59/0.83          | ~ (l1_pre_topc @ X1)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.83      inference('demod', [status(thm)], ['242', '243', '244', '245'])).
% 0.59/0.83  thf('247', plain,
% 0.59/0.83      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.59/0.83      inference('clc', [status(thm)], ['121', '122'])).
% 0.59/0.83  thf('248', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v1_funct_2 @ 
% 0.59/0.83           (k3_tmap_1 @ X1 @ sk_B @ sk_D @ X0 @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.59/0.83           (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | (v2_struct_0 @ X1)
% 0.59/0.83          | ~ (v2_pre_topc @ X1)
% 0.59/0.83          | ~ (l1_pre_topc @ X1)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (m1_pre_topc @ sk_D @ X1)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ X1))),
% 0.59/0.83      inference('demod', [status(thm)], ['246', '247'])).
% 0.59/0.83  thf('249', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (l1_pre_topc @ sk_D)
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | ~ (l1_pre_topc @ sk_D)
% 0.59/0.83          | ~ (v2_pre_topc @ sk_D)
% 0.59/0.83          | (v2_struct_0 @ sk_D)
% 0.59/0.83          | (v1_funct_2 @ 
% 0.59/0.83             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 0.59/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.59/0.83             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['239', '248'])).
% 0.59/0.83  thf('250', plain, ((l1_pre_topc @ sk_D)),
% 0.59/0.83      inference('demod', [status(thm)], ['144', '145'])).
% 0.59/0.83  thf('251', plain, ((l1_pre_topc @ sk_D)),
% 0.59/0.83      inference('demod', [status(thm)], ['144', '145'])).
% 0.59/0.83  thf('252', plain, ((v2_pre_topc @ sk_D)),
% 0.59/0.83      inference('demod', [status(thm)], ['138', '139', '140'])).
% 0.59/0.83  thf('253', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (m1_pre_topc @ X0 @ sk_D)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | (v2_struct_0 @ sk_D)
% 0.59/0.83          | (v1_funct_2 @ 
% 0.59/0.83             (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ X0 @ 
% 0.59/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.59/0.83             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.59/0.83      inference('demod', [status(thm)], ['249', '250', '251', '252'])).
% 0.59/0.83  thf('254', plain,
% 0.59/0.83      (((v1_funct_2 @ 
% 0.59/0.83         (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.83          (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.59/0.83         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.59/0.83        | (v2_struct_0 @ sk_D)
% 0.59/0.83        | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('sup-', [status(thm)], ['238', '253'])).
% 0.59/0.83  thf('255', plain, (~ (v2_struct_0 @ sk_D)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('256', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_B)
% 0.59/0.83        | (v1_funct_2 @ 
% 0.59/0.83           (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.59/0.83           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.59/0.83      inference('clc', [status(thm)], ['254', '255'])).
% 0.59/0.83  thf('257', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('258', plain,
% 0.59/0.83      ((v1_funct_2 @ 
% 0.59/0.83        (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.83         (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)) @ 
% 0.59/0.83        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.59/0.83      inference('clc', [status(thm)], ['256', '257'])).
% 0.59/0.83  thf('259', plain,
% 0.59/0.83      (((k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83         sk_C)
% 0.59/0.83         = (k3_tmap_1 @ sk_D @ sk_B @ sk_D @ sk_C @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D)))),
% 0.59/0.83      inference('sup+', [status(thm)], ['205', '206'])).
% 0.59/0.83  thf('260', plain,
% 0.59/0.83      ((v1_funct_2 @ 
% 0.59/0.83        (k2_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.59/0.83         sk_C) @ 
% 0.59/0.83        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.59/0.83      inference('demod', [status(thm)], ['258', '259'])).
% 0.59/0.83  thf('261', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (r2_funct_2 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83             (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.59/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) @ 
% 0.59/0.83             X0)
% 0.59/0.83          | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.59/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) = (X0))
% 0.59/0.83          | ~ (m1_subset_1 @ X0 @ 
% 0.59/0.83               (k1_zfmisc_1 @ 
% 0.59/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.59/0.83          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.59/0.83          | ~ (v1_funct_1 @ X0))),
% 0.59/0.83      inference('demod', [status(thm)], ['210', '237', '260'])).
% 0.59/0.83  thf('262', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_B)
% 0.59/0.83        | (v2_struct_0 @ sk_D)
% 0.59/0.83        | (v2_struct_0 @ sk_C)
% 0.59/0.83        | (v2_struct_0 @ sk_A)
% 0.59/0.83        | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))
% 0.59/0.83        | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.59/0.83             (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.59/0.83        | ~ (m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.59/0.83             (k1_zfmisc_1 @ 
% 0.59/0.83              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.59/0.83        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.59/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C)
% 0.59/0.83            = (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['168', '261'])).
% 0.59/0.83  thf('263', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('264', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | (v2_struct_0 @ sk_A)
% 0.59/0.83          | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)))),
% 0.59/0.83      inference('demod', [status(thm)], ['51', '52', '53', '54'])).
% 0.59/0.83  thf('265', plain,
% 0.59/0.83      (((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))
% 0.59/0.83        | (v2_struct_0 @ sk_A)
% 0.59/0.83        | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('sup-', [status(thm)], ['263', '264'])).
% 0.59/0.83  thf('266', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('267', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_B)
% 0.59/0.83        | (v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)))),
% 0.59/0.83      inference('clc', [status(thm)], ['265', '266'])).
% 0.59/0.83  thf('268', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('269', plain,
% 0.59/0.83      ((v1_funct_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.59/0.83      inference('clc', [status(thm)], ['267', '268'])).
% 0.59/0.83  thf('270', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('271', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((v2_struct_0 @ sk_A)
% 0.59/0.83          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E)
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 sk_E @ (u1_struct_0 @ X0)))
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('simplify', [status(thm)], ['78'])).
% 0.59/0.83  thf('272', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_B)
% 0.59/0.83        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.59/0.83            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83               sk_E @ (u1_struct_0 @ sk_C)))
% 0.59/0.83        | (v2_struct_0 @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['270', '271'])).
% 0.59/0.83  thf('273', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('274', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_A)
% 0.59/0.83        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.59/0.83            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.59/0.83      inference('clc', [status(thm)], ['272', '273'])).
% 0.59/0.83  thf('275', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('276', plain,
% 0.59/0.83      (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E)
% 0.59/0.83         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.59/0.83            (u1_struct_0 @ sk_C)))),
% 0.59/0.83      inference('clc', [status(thm)], ['274', '275'])).
% 0.59/0.83  thf('277', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('278', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((v2_struct_0 @ sk_A)
% 0.59/0.83          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ X0)
% 0.59/0.83              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83                 sk_E @ (u1_struct_0 @ X0)))
% 0.59/0.83          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('demod', [status(thm)],
% 0.59/0.83                ['88', '89', '90', '91', '92', '93', '94'])).
% 0.59/0.83  thf('279', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_B)
% 0.59/0.83        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 0.59/0.83            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83               sk_E @ (u1_struct_0 @ sk_C)))
% 0.59/0.83        | (v2_struct_0 @ sk_A))),
% 0.59/0.83      inference('sup-', [status(thm)], ['277', '278'])).
% 0.59/0.83  thf('280', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('281', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_A)
% 0.59/0.83        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 0.59/0.83            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 0.59/0.83               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.59/0.83      inference('clc', [status(thm)], ['279', '280'])).
% 0.59/0.83  thf('282', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('283', plain,
% 0.59/0.83      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 0.59/0.83         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.59/0.83            (u1_struct_0 @ sk_C)))),
% 0.59/0.83      inference('clc', [status(thm)], ['281', '282'])).
% 0.59/0.83  thf('284', plain,
% 0.59/0.83      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 0.59/0.83         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.59/0.83      inference('sup+', [status(thm)], ['276', '283'])).
% 0.59/0.83  thf('285', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C))),
% 0.59/0.83      inference('demod', [status(thm)], ['269', '284'])).
% 0.59/0.83  thf('286', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('287', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | (v2_struct_0 @ sk_A)
% 0.59/0.83          | (v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.59/0.83             (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))),
% 0.59/0.83      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 0.59/0.83  thf('288', plain,
% 0.59/0.83      (((v1_funct_2 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 0.59/0.83         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.59/0.83        | (v2_struct_0 @ sk_A)
% 0.59/0.83        | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('sup-', [status(thm)], ['286', '287'])).
% 0.59/0.83  thf('289', plain,
% 0.59/0.83      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 0.59/0.83         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.59/0.83      inference('sup+', [status(thm)], ['276', '283'])).
% 0.59/0.83  thf('290', plain,
% 0.59/0.83      (((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.59/0.83         (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.59/0.83        | (v2_struct_0 @ sk_A)
% 0.59/0.83        | (v2_struct_0 @ sk_B))),
% 0.59/0.83      inference('demod', [status(thm)], ['288', '289'])).
% 0.59/0.83  thf('291', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('292', plain,
% 0.59/0.83      (((v2_struct_0 @ sk_B)
% 0.59/0.83        | (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.59/0.83           (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))),
% 0.59/0.83      inference('clc', [status(thm)], ['290', '291'])).
% 0.59/0.83  thf('293', plain, (~ (v2_struct_0 @ sk_B)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('294', plain,
% 0.59/0.83      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.59/0.83        (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))),
% 0.59/0.83      inference('clc', [status(thm)], ['292', '293'])).
% 0.59/0.83  thf('295', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('296', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (m1_pre_topc @ X0 @ sk_A)
% 0.59/0.83          | (v2_struct_0 @ sk_B)
% 0.59/0.83          | (v2_struct_0 @ sk_A)
% 0.59/0.83          | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_E) @ 
% 0.59/0.83             (k1_zfmisc_1 @ 
% 0.59/0.83              (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B)))))),
% 0.59/0.83      inference('demod', [status(thm)], ['29', '30', '31', '32'])).
% 0.66/0.83  thf('297', plain,
% 0.66/0.83      (((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 0.66/0.83         (k1_zfmisc_1 @ 
% 0.66/0.83          (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))
% 0.66/0.83        | (v2_struct_0 @ sk_A)
% 0.66/0.83        | (v2_struct_0 @ sk_B))),
% 0.66/0.83      inference('sup-', [status(thm)], ['295', '296'])).
% 0.66/0.83  thf('298', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('299', plain,
% 0.66/0.83      (((v2_struct_0 @ sk_B)
% 0.66/0.83        | (m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 0.66/0.83           (k1_zfmisc_1 @ 
% 0.66/0.83            (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B)))))),
% 0.66/0.83      inference('clc', [status(thm)], ['297', '298'])).
% 0.66/0.83  thf('300', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('301', plain,
% 0.66/0.83      ((m1_subset_1 @ (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E) @ 
% 0.66/0.83        (k1_zfmisc_1 @ 
% 0.66/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.83      inference('clc', [status(thm)], ['299', '300'])).
% 0.66/0.83  thf('302', plain,
% 0.66/0.83      (((k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)
% 0.66/0.83         = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_C @ sk_E))),
% 0.66/0.83      inference('sup+', [status(thm)], ['276', '283'])).
% 0.66/0.83  thf('303', plain,
% 0.66/0.83      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.66/0.83        (k1_zfmisc_1 @ 
% 0.66/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.83      inference('demod', [status(thm)], ['301', '302'])).
% 0.66/0.83  thf('304', plain,
% 0.66/0.83      (((v2_struct_0 @ sk_B)
% 0.66/0.83        | (v2_struct_0 @ sk_D)
% 0.66/0.83        | (v2_struct_0 @ sk_C)
% 0.66/0.83        | (v2_struct_0 @ sk_A)
% 0.66/0.83        | ((k2_tmap_1 @ sk_D @ sk_B @ 
% 0.66/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C)
% 0.66/0.83            = (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C)))),
% 0.66/0.83      inference('demod', [status(thm)], ['262', '285', '294', '303'])).
% 0.66/0.83  thf('305', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('306', plain, (((sk_F) = (sk_G))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('307', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.66/0.83      inference('demod', [status(thm)], ['305', '306'])).
% 0.66/0.83  thf('308', plain,
% 0.66/0.83      ((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.66/0.83        sk_F)),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('309', plain,
% 0.66/0.83      ((m1_subset_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.66/0.83        (k1_zfmisc_1 @ 
% 0.66/0.83         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.66/0.83      inference('demod', [status(thm)], ['213', '214'])).
% 0.66/0.83  thf(t64_tmap_1, axiom,
% 0.66/0.83    (![A:$i]:
% 0.66/0.83     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.66/0.83       ( ![B:$i]:
% 0.66/0.83         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.66/0.83             ( l1_pre_topc @ B ) ) =>
% 0.66/0.83           ( ![C:$i]:
% 0.66/0.83             ( ( ( v1_funct_1 @ C ) & 
% 0.66/0.83                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.66/0.83                 ( m1_subset_1 @
% 0.66/0.83                   C @ 
% 0.66/0.83                   ( k1_zfmisc_1 @
% 0.66/0.83                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.66/0.83               ( ![D:$i]:
% 0.66/0.83                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.66/0.83                   ( ![E:$i]:
% 0.66/0.83                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.66/0.83                       ( ![F:$i]:
% 0.66/0.83                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.66/0.83                           ( ( ( ( E ) = ( F ) ) & 
% 0.66/0.83                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.66/0.83                             ( r1_tmap_1 @
% 0.66/0.83                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.66/0.83  thf('310', plain,
% 0.66/0.83      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.66/0.83         ((v2_struct_0 @ X26)
% 0.66/0.83          | ~ (v2_pre_topc @ X26)
% 0.66/0.83          | ~ (l1_pre_topc @ X26)
% 0.66/0.83          | (v2_struct_0 @ X27)
% 0.66/0.83          | ~ (m1_pre_topc @ X27 @ X26)
% 0.66/0.83          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 0.66/0.83          | (r1_tmap_1 @ X27 @ X29 @ (k2_tmap_1 @ X26 @ X29 @ X30 @ X27) @ X28)
% 0.66/0.83          | ((X31) != (X28))
% 0.66/0.83          | ~ (r1_tmap_1 @ X26 @ X29 @ X30 @ X31)
% 0.66/0.83          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X26))
% 0.66/0.83          | ~ (m1_subset_1 @ X30 @ 
% 0.66/0.83               (k1_zfmisc_1 @ 
% 0.66/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X29))))
% 0.66/0.83          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X29))
% 0.66/0.83          | ~ (v1_funct_1 @ X30)
% 0.66/0.83          | ~ (l1_pre_topc @ X29)
% 0.66/0.83          | ~ (v2_pre_topc @ X29)
% 0.66/0.83          | (v2_struct_0 @ X29))),
% 0.66/0.83      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.66/0.83  thf('311', plain,
% 0.66/0.83      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.66/0.83         ((v2_struct_0 @ X29)
% 0.66/0.83          | ~ (v2_pre_topc @ X29)
% 0.66/0.83          | ~ (l1_pre_topc @ X29)
% 0.66/0.83          | ~ (v1_funct_1 @ X30)
% 0.66/0.83          | ~ (v1_funct_2 @ X30 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X29))
% 0.66/0.83          | ~ (m1_subset_1 @ X30 @ 
% 0.66/0.83               (k1_zfmisc_1 @ 
% 0.66/0.83                (k2_zfmisc_1 @ (u1_struct_0 @ X26) @ (u1_struct_0 @ X29))))
% 0.66/0.83          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 0.66/0.83          | ~ (r1_tmap_1 @ X26 @ X29 @ X30 @ X28)
% 0.66/0.83          | (r1_tmap_1 @ X27 @ X29 @ (k2_tmap_1 @ X26 @ X29 @ X30 @ X27) @ X28)
% 0.66/0.83          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 0.66/0.83          | ~ (m1_pre_topc @ X27 @ X26)
% 0.66/0.83          | (v2_struct_0 @ X27)
% 0.66/0.83          | ~ (l1_pre_topc @ X26)
% 0.66/0.83          | ~ (v2_pre_topc @ X26)
% 0.66/0.83          | (v2_struct_0 @ X26))),
% 0.66/0.83      inference('simplify', [status(thm)], ['310'])).
% 0.66/0.83  thf('312', plain,
% 0.66/0.83      (![X0 : $i, X1 : $i]:
% 0.66/0.83         ((v2_struct_0 @ sk_D)
% 0.66/0.83          | ~ (v2_pre_topc @ sk_D)
% 0.66/0.83          | ~ (l1_pre_topc @ sk_D)
% 0.66/0.83          | (v2_struct_0 @ X0)
% 0.66/0.83          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.66/0.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.66/0.83          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.66/0.83             (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.66/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X0) @ 
% 0.66/0.83             X1)
% 0.66/0.83          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.66/0.83               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X1)
% 0.66/0.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.66/0.83          | ~ (v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.66/0.83               (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.66/0.83          | ~ (v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))
% 0.66/0.83          | ~ (l1_pre_topc @ sk_B)
% 0.66/0.83          | ~ (v2_pre_topc @ sk_B)
% 0.66/0.83          | (v2_struct_0 @ sk_B))),
% 0.66/0.83      inference('sup-', [status(thm)], ['309', '311'])).
% 0.66/0.83  thf('313', plain, ((v2_pre_topc @ sk_D)),
% 0.66/0.83      inference('demod', [status(thm)], ['138', '139', '140'])).
% 0.66/0.83  thf('314', plain, ((l1_pre_topc @ sk_D)),
% 0.66/0.83      inference('demod', [status(thm)], ['144', '145'])).
% 0.66/0.83  thf('315', plain,
% 0.66/0.83      ((v1_funct_2 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ 
% 0.66/0.83        (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.66/0.83      inference('clc', [status(thm)], ['121', '122'])).
% 0.66/0.83  thf('316', plain, ((v1_funct_1 @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D))),
% 0.66/0.83      inference('demod', [status(thm)], ['218', '219'])).
% 0.66/0.83  thf('317', plain, ((l1_pre_topc @ sk_B)),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('318', plain, ((v2_pre_topc @ sk_B)),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('319', plain,
% 0.66/0.83      (![X0 : $i, X1 : $i]:
% 0.66/0.83         ((v2_struct_0 @ sk_D)
% 0.66/0.83          | (v2_struct_0 @ X0)
% 0.66/0.83          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.66/0.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.66/0.83          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.66/0.83             (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.66/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X0) @ 
% 0.66/0.83             X1)
% 0.66/0.83          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 0.66/0.83               (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X1)
% 0.66/0.83          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.66/0.83          | (v2_struct_0 @ sk_B))),
% 0.66/0.83      inference('demod', [status(thm)],
% 0.66/0.83                ['312', '313', '314', '315', '316', '317', '318'])).
% 0.66/0.83  thf('320', plain,
% 0.66/0.83      (![X0 : $i]:
% 0.66/0.83         ((v2_struct_0 @ sk_B)
% 0.66/0.83          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.66/0.83          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.66/0.83             (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.66/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X0) @ 
% 0.66/0.83             sk_F)
% 0.66/0.83          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.66/0.83          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.66/0.83          | (v2_struct_0 @ X0)
% 0.66/0.83          | (v2_struct_0 @ sk_D))),
% 0.66/0.83      inference('sup-', [status(thm)], ['308', '319'])).
% 0.66/0.83  thf('321', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('322', plain,
% 0.66/0.83      (![X0 : $i]:
% 0.66/0.83         ((v2_struct_0 @ sk_B)
% 0.66/0.83          | (r1_tmap_1 @ X0 @ sk_B @ 
% 0.66/0.83             (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.66/0.83              (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ X0) @ 
% 0.66/0.83             sk_F)
% 0.66/0.83          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.66/0.83          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.66/0.83          | (v2_struct_0 @ X0)
% 0.66/0.83          | (v2_struct_0 @ sk_D))),
% 0.66/0.83      inference('demod', [status(thm)], ['320', '321'])).
% 0.66/0.83  thf('323', plain,
% 0.66/0.83      (((v2_struct_0 @ sk_D)
% 0.66/0.83        | (v2_struct_0 @ sk_C)
% 0.66/0.83        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.66/0.83        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.66/0.83           (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.66/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) @ 
% 0.66/0.83           sk_F)
% 0.66/0.83        | (v2_struct_0 @ sk_B))),
% 0.66/0.83      inference('sup-', [status(thm)], ['307', '322'])).
% 0.66/0.83  thf('324', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('325', plain,
% 0.66/0.83      (((v2_struct_0 @ sk_D)
% 0.66/0.83        | (v2_struct_0 @ sk_C)
% 0.66/0.83        | (r1_tmap_1 @ sk_C @ sk_B @ 
% 0.66/0.83           (k2_tmap_1 @ sk_D @ sk_B @ 
% 0.66/0.83            (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_D) @ sk_C) @ 
% 0.66/0.83           sk_F)
% 0.66/0.83        | (v2_struct_0 @ sk_B))),
% 0.66/0.83      inference('demod', [status(thm)], ['323', '324'])).
% 0.66/0.83  thf('326', plain,
% 0.66/0.83      (((r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.66/0.83         sk_F)
% 0.66/0.83        | (v2_struct_0 @ sk_A)
% 0.66/0.83        | (v2_struct_0 @ sk_C)
% 0.66/0.83        | (v2_struct_0 @ sk_D)
% 0.66/0.83        | (v2_struct_0 @ sk_B)
% 0.66/0.83        | (v2_struct_0 @ sk_B)
% 0.66/0.83        | (v2_struct_0 @ sk_C)
% 0.66/0.83        | (v2_struct_0 @ sk_D))),
% 0.66/0.83      inference('sup+', [status(thm)], ['304', '325'])).
% 0.66/0.83  thf('327', plain,
% 0.66/0.83      (((v2_struct_0 @ sk_B)
% 0.66/0.83        | (v2_struct_0 @ sk_D)
% 0.66/0.83        | (v2_struct_0 @ sk_C)
% 0.66/0.83        | (v2_struct_0 @ sk_A)
% 0.66/0.83        | (r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.66/0.83           sk_F))),
% 0.66/0.83      inference('simplify', [status(thm)], ['326'])).
% 0.66/0.83  thf('328', plain,
% 0.66/0.83      (~ (r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.66/0.83          sk_G)),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('329', plain, (((sk_F) = (sk_G))),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('330', plain,
% 0.66/0.83      (~ (r1_tmap_1 @ sk_C @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_E @ sk_C) @ 
% 0.66/0.83          sk_F)),
% 0.66/0.83      inference('demod', [status(thm)], ['328', '329'])).
% 0.66/0.83  thf('331', plain,
% 0.66/0.83      (((v2_struct_0 @ sk_A)
% 0.66/0.83        | (v2_struct_0 @ sk_C)
% 0.66/0.83        | (v2_struct_0 @ sk_D)
% 0.66/0.83        | (v2_struct_0 @ sk_B))),
% 0.66/0.83      inference('sup-', [status(thm)], ['327', '330'])).
% 0.66/0.83  thf('332', plain, (~ (v2_struct_0 @ sk_B)),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('333', plain,
% 0.66/0.83      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.66/0.83      inference('sup-', [status(thm)], ['331', '332'])).
% 0.66/0.83  thf('334', plain, (~ (v2_struct_0 @ sk_D)),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('335', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.66/0.83      inference('clc', [status(thm)], ['333', '334'])).
% 0.66/0.83  thf('336', plain, (~ (v2_struct_0 @ sk_A)),
% 0.66/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.83  thf('337', plain, ((v2_struct_0 @ sk_C)),
% 0.66/0.83      inference('clc', [status(thm)], ['335', '336'])).
% 0.66/0.83  thf('338', plain, ($false), inference('demod', [status(thm)], ['0', '337'])).
% 0.66/0.83  
% 0.66/0.83  % SZS output end Refutation
% 0.66/0.83  
% 0.66/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
