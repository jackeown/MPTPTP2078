%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kpJPv8KqpA

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:04 EST 2020

% Result     : Theorem 6.02s
% Output     : Refutation 6.02s
% Verified   : 
% Statistics : Number of formulae       :  265 (1541 expanded)
%              Number of leaves         :   29 ( 441 expanded)
%              Depth                    :   30
%              Number of atoms          : 4109 (77593 expanded)
%              Number of equality atoms :   68 (2578 expanded)
%              Maximal formula depth    :   32 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_pre_topc_type,type,(
    v1_pre_topc: $i > $o )).

thf(sk_H_type,type,(
    sk_H: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_tsep_1_type,type,(
    k1_tsep_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(t125_tmap_1,conjecture,(
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
                    & ( m1_pre_topc @ D @ A ) )
                 => ! [E: $i] :
                      ( ( ~ ( v2_struct_0 @ E )
                        & ( m1_pre_topc @ E @ A ) )
                     => ( ( A
                          = ( k1_tsep_1 @ A @ D @ E ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                               => ! [H: $i] :
                                    ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) )
                                   => ( ( ( F = G )
                                        & ( F = H ) )
                                     => ( ( r1_tmap_1 @ A @ B @ C @ F )
                                      <=> ( ( r1_tmap_1 @ D @ B @ ( k2_tmap_1 @ A @ B @ C @ D ) @ G )
                                          & ( r1_tmap_1 @ E @ B @ ( k2_tmap_1 @ A @ B @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ) )).

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
                      & ( m1_pre_topc @ D @ A ) )
                   => ! [E: $i] :
                        ( ( ~ ( v2_struct_0 @ E )
                          & ( m1_pre_topc @ E @ A ) )
                       => ( ( A
                            = ( k1_tsep_1 @ A @ D @ E ) )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                                 => ! [H: $i] :
                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) )
                                     => ( ( ( F = G )
                                          & ( F = H ) )
                                       => ( ( r1_tmap_1 @ A @ B @ C @ F )
                                        <=> ( ( r1_tmap_1 @ D @ B @ ( k2_tmap_1 @ A @ B @ C @ D ) @ G )
                                            & ( r1_tmap_1 @ E @ B @ ( k2_tmap_1 @ A @ B @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t125_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    sk_F = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_H = sk_G ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('7',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tsep_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_pre_topc @ A )
        & ~ ( v2_struct_0 @ B )
        & ( m1_pre_topc @ B @ A )
        & ~ ( v2_struct_0 @ C )
        & ( m1_pre_topc @ C @ A ) )
     => ( ~ ( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) )
        & ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_pre_topc @ X9 @ X10 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_pre_topc @ X10 )
      | ( v2_struct_0 @ X10 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_pre_topc @ X11 @ X10 )
      | ( m1_pre_topc @ ( k1_tsep_1 @ X10 @ X9 @ X11 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tsep_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ X0 ) @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( m1_pre_topc @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_A ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E )
    | ( m1_pre_topc @ sk_A @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
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
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
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
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_A )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['7','29'])).

thf('31',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
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

thf('33',plain,(
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

thf('34',plain,(
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
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35','36','37','38','39','40'])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_D ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference('sup+',[status(thm)],['30','46'])).

thf('48',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['48'])).

thf('50',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t123_tmap_1,axiom,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) )
                         => ! [G: $i] :
                              ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) )
                             => ! [H: $i] :
                                  ( ( m1_subset_1 @ H @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) )
                                 => ( ( ( H = F )
                                      & ( H = G ) )
                                   => ( ( r1_tmap_1 @ ( k1_tsep_1 @ A @ C @ D ) @ B @ E @ H )
                                    <=> ( ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ F )
                                        & ( r1_tmap_1 @ D @ B @ ( k3_tmap_1 @ A @ B @ ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) )).

thf('54',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) ) )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) @ X12 @ X18 @ X17 )
      | ( r1_tmap_1 @ X16 @ X12 @ ( k3_tmap_1 @ X14 @ X12 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) @ X16 @ X18 ) @ X15 )
      | ( X17 != X19 )
      | ( X17 != X15 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( m1_pre_topc @ X16 @ X14 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t123_tmap_1])).

thf('55',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X14 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X13 ) )
      | ( r1_tmap_1 @ X16 @ X12 @ ( k3_tmap_1 @ X14 @ X12 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) @ X16 @ X18 ) @ X19 )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) @ X12 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 @ X1 @ X2 )
      | ( r1_tmap_1 @ sk_D @ X0 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_D @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('62',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tmap_1 @ sk_A @ X0 @ X1 @ X2 )
      | ( r1_tmap_1 @ sk_D @ X0 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','58','59','60','61','62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ X0 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['52','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ X0 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('72',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['51','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_H @ ( u1_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    sk_H = sk_G ),
    inference('sup+',[status(thm)],['3','4'])).

thf('79',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_G )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['72','73','76','79'])).

thf('81',plain,
    ( ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup+',[status(thm)],['47','80'])).

thf('82',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35','36','37','38','39','40'])).

thf('88',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_C @ ( u1_struct_0 @ sk_E ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference('sup+',[status(thm)],['85','92'])).

thf('94',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('95',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) ) )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) @ X12 @ X18 @ X17 )
      | ( r1_tmap_1 @ X13 @ X12 @ ( k3_tmap_1 @ X14 @ X12 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) @ X13 @ X18 ) @ X19 )
      | ( X17 != X19 )
      | ( X17 != X15 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( m1_pre_topc @ X16 @ X14 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t123_tmap_1])).

thf('98',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X14 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X13 ) )
      | ( r1_tmap_1 @ X13 @ X12 @ ( k3_tmap_1 @ X14 @ X12 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) @ X13 @ X18 ) @ X19 )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) @ X12 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 @ X1 @ X2 )
      | ( r1_tmap_1 @ sk_E @ X0 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_E @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','98'])).

thf('100',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tmap_1 @ sk_A @ X0 @ X1 @ X2 )
      | ( r1_tmap_1 @ sk_E @ X0 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['99','100','101','102','103','104','105','106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) @ X0 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['95','108'])).

thf('110',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) @ X0 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['109','110','111','112','113'])).

thf('115',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['94','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('118',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('119',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) @ sk_G )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['115','116','117','118'])).

thf('120',plain,
    ( ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup+',[status(thm)],['93','119'])).

thf('121',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    sk_H = sk_G ),
    inference('sup+',[status(thm)],['3','4'])).

thf('124',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('126',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['121','125'])).

thf('127',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('128',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['82','128'])).

thf('130',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['1'])).

thf('140',plain,(
    r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ),
    inference('sat_resolution*',[status(thm)],['138','139'])).

thf('141',plain,(
    r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G ),
    inference(simpl_trail,[status(thm)],['6','140'])).

thf('142',plain,
    ( ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference('sup+',[status(thm)],['30','46'])).

thf('143',plain,
    ( ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference('sup+',[status(thm)],['85','92'])).

thf('144',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ~ ( l1_pre_topc @ X12 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) ) )
      | ~ ( r1_tmap_1 @ X16 @ X12 @ ( k3_tmap_1 @ X14 @ X12 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) @ X16 @ X18 ) @ X15 )
      | ~ ( r1_tmap_1 @ X13 @ X12 @ ( k3_tmap_1 @ X14 @ X12 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) @ X13 @ X18 ) @ X19 )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) @ X12 @ X18 @ X17 )
      | ( X17 != X19 )
      | ( X17 != X15 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( m1_pre_topc @ X16 @ X14 )
      | ( v2_struct_0 @ X16 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t123_tmap_1])).

thf('147',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ~ ( l1_pre_topc @ X14 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_pre_topc @ X16 @ X14 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_2 @ X18 @ ( u1_struct_0 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) ) @ ( u1_struct_0 @ X12 ) ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X13 ) )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) @ X12 @ X18 @ X19 )
      | ~ ( r1_tmap_1 @ X13 @ X12 @ ( k3_tmap_1 @ X14 @ X12 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) @ X13 @ X18 ) @ X19 )
      | ~ ( r1_tmap_1 @ X16 @ X12 @ ( k3_tmap_1 @ X14 @ X12 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) @ X16 @ X18 ) @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ ( k1_tsep_1 @ X14 @ X16 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ( v2_struct_0 @ X13 )
      | ~ ( l1_pre_topc @ X12 )
      | ~ ( v2_pre_topc @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(simplify,[status(thm)],['146'])).

thf('148',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_pre_topc @ sk_E @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) )
      | ~ ( r1_tmap_1 @ sk_D @ X0 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_D @ X1 ) @ X2 )
      | ~ ( r1_tmap_1 @ sk_E @ X0 @ ( k3_tmap_1 @ sk_A @ X0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ sk_E @ X1 ) @ X2 )
      | ( r1_tmap_1 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( m1_pre_topc @ sk_D @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['145','147'])).

thf('149',plain,(
    m1_pre_topc @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( sk_A
    = ( k1_tsep_1 @ sk_A @ sk_D @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tmap_1 @ sk_D @ X0 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1 ) @ X2 )
      | ~ ( r1_tmap_1 @ sk_E @ X0 @ ( k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1 ) @ X2 )
      | ( r1_tmap_1 @ sk_A @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_E ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['148','149','150','151','152','153','154','155','156','157'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) @ X0 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['144','158'])).

thf('160',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,(
    v1_funct_2 @ sk_C @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C ) @ X0 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['159','160','161','162','163'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ X0 )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['143','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ X0 )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['142','166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
    | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
    | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['141','168'])).

thf('170',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
   <= ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ) ),
    inference(split,[status(esa)],['48'])).

thf('171',plain,
    ( ( ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D )
      = ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference('sup+',[status(thm)],['30','46'])).

thf('172',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['174'])).

thf('176',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_E ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ X0 )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('177',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_G )
      | ~ ( m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('180',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('181',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_E )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C ) @ sk_G )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['177','178','179','180'])).

thf('182',plain,
    ( ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference('sup+',[status(thm)],['171','181'])).

thf('183',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['2','5'])).

thf('185',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['122','123','124'])).

thf('186',plain,
    ( ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
      | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ) )
   <= ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['184','185'])).

thf('187',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B )
      | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) )
   <= ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ) ),
    inference('sup-',[status(thm)],['183','186'])).

thf('188',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['174'])).

thf('189',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ) ),
    inference(demod,[status(thm)],['187','188'])).

thf('190',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ) ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
    | ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference('sup-',[status(thm)],['195','196'])).

thf('198',plain,
    ( ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['174'])).

thf('199',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(split,[status(esa)],['199'])).

thf('201',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('203',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['198','202'])).

thf('204',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_E )
      | ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G ) )
   <= ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(simplify,[status(thm)],['120'])).

thf('205',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
   <= ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(split,[status(esa)],['199'])).

thf('206',plain,(
    sk_H = sk_G ),
    inference('sup+',[status(thm)],['3','4'])).

thf('207',plain,
    ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H ) ),
    inference(demod,[status(thm)],['205','206'])).

thf('208',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ) ),
    inference('sup-',[status(thm)],['204','207'])).

thf('209',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_E ) )
   <= ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ) ),
    inference('sup-',[status(thm)],['208','209'])).

thf('211',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,
    ( ( ( v2_struct_0 @ sk_E )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ) ),
    inference(clc,[status(thm)],['210','211'])).

thf('213',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( v2_struct_0 @ sk_D )
   <= ( ~ ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
      & ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ) ),
    inference(clc,[status(thm)],['212','213'])).

thf('215',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,
    ( ( r1_tmap_1 @ sk_E @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_H )
    | ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(split,[status(esa)],['174'])).

thf('218',plain,(
    r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['197','203','216','217'])).

thf('219',plain,(
    r1_tmap_1 @ sk_D @ sk_B @ ( k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_G ),
    inference(simpl_trail,[status(thm)],['170','218'])).

thf('220',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('222',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_E ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('223',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(demod,[status(thm)],['169','219','220','221','222'])).

thf('224',plain,
    ( ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference(demod,[status(thm)],['200','201'])).

thf('225',plain,(
    ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['138'])).

thf('226',plain,(
    ~ ( r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G ) ),
    inference(simpl_trail,[status(thm)],['224','225'])).

thf('227',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_E ) ),
    inference('sup-',[status(thm)],['223','226'])).

thf('228',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,
    ( ( v2_struct_0 @ sk_E )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['227','228'])).

thf('230',plain,(
    ~ ( v2_struct_0 @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_D ) ),
    inference(clc,[status(thm)],['229','230'])).

thf('232',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v2_struct_0 @ sk_D ),
    inference(clc,[status(thm)],['231','232'])).

thf('234',plain,(
    $false ),
    inference(demod,[status(thm)],['0','233'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.kpJPv8KqpA
% 0.15/0.37  % Computer   : n011.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 17:36:57 EST 2020
% 0.22/0.37  % CPUTime    : 
% 0.22/0.37  % Running portfolio for 600 s
% 0.22/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.22/0.37  % Number of cores: 8
% 0.22/0.37  % Python version: Python 3.6.8
% 0.22/0.37  % Running in FO mode
% 6.02/6.22  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 6.02/6.22  % Solved by: fo/fo7.sh
% 6.02/6.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.02/6.22  % done 1138 iterations in 5.749s
% 6.02/6.22  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 6.02/6.22  % SZS output start Refutation
% 6.02/6.22  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.02/6.22  thf(sk_B_type, type, sk_B: $i).
% 6.02/6.22  thf(sk_C_type, type, sk_C: $i).
% 6.02/6.22  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 6.02/6.22  thf(sk_A_type, type, sk_A: $i).
% 6.02/6.22  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 6.02/6.22  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 6.02/6.22  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 6.02/6.22  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 6.02/6.22  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.02/6.22  thf(sk_E_type, type, sk_E: $i).
% 6.02/6.22  thf(sk_D_type, type, sk_D: $i).
% 6.02/6.22  thf(v1_pre_topc_type, type, v1_pre_topc: $i > $o).
% 6.02/6.22  thf(sk_H_type, type, sk_H: $i).
% 6.02/6.22  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 6.02/6.22  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 6.02/6.22  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 6.02/6.22  thf(sk_F_type, type, sk_F: $i).
% 6.02/6.22  thf(k1_tsep_1_type, type, k1_tsep_1: $i > $i > $i > $i).
% 6.02/6.22  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 6.02/6.22  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 6.02/6.22  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.02/6.22  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 6.02/6.22  thf(sk_G_type, type, sk_G: $i).
% 6.02/6.22  thf(t125_tmap_1, conjecture,
% 6.02/6.22    (![A:$i]:
% 6.02/6.22     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.02/6.22       ( ![B:$i]:
% 6.02/6.22         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 6.02/6.22             ( l1_pre_topc @ B ) ) =>
% 6.02/6.22           ( ![C:$i]:
% 6.02/6.22             ( ( ( v1_funct_1 @ C ) & 
% 6.02/6.22                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 6.02/6.22                 ( m1_subset_1 @
% 6.02/6.22                   C @ 
% 6.02/6.22                   ( k1_zfmisc_1 @
% 6.02/6.22                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.02/6.22               ( ![D:$i]:
% 6.02/6.22                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 6.02/6.22                   ( ![E:$i]:
% 6.02/6.22                     ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 6.02/6.22                       ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) =>
% 6.02/6.22                         ( ![F:$i]:
% 6.02/6.22                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) ) =>
% 6.02/6.22                             ( ![G:$i]:
% 6.02/6.22                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 6.02/6.22                                 ( ![H:$i]:
% 6.02/6.22                                   ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) ) =>
% 6.02/6.22                                     ( ( ( ( F ) = ( G ) ) & ( ( F ) = ( H ) ) ) =>
% 6.02/6.22                                       ( ( r1_tmap_1 @ A @ B @ C @ F ) <=>
% 6.02/6.22                                         ( ( r1_tmap_1 @
% 6.02/6.22                                             D @ B @ 
% 6.02/6.22                                             ( k2_tmap_1 @ A @ B @ C @ D ) @ G ) & 
% 6.02/6.22                                           ( r1_tmap_1 @
% 6.02/6.22                                             E @ B @ 
% 6.02/6.22                                             ( k2_tmap_1 @ A @ B @ C @ E ) @ H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 6.02/6.22  thf(zf_stmt_0, negated_conjecture,
% 6.02/6.22    (~( ![A:$i]:
% 6.02/6.22        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 6.02/6.22            ( l1_pre_topc @ A ) ) =>
% 6.02/6.22          ( ![B:$i]:
% 6.02/6.22            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 6.02/6.22                ( l1_pre_topc @ B ) ) =>
% 6.02/6.22              ( ![C:$i]:
% 6.02/6.22                ( ( ( v1_funct_1 @ C ) & 
% 6.02/6.22                    ( v1_funct_2 @
% 6.02/6.22                      C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 6.02/6.22                    ( m1_subset_1 @
% 6.02/6.22                      C @ 
% 6.02/6.22                      ( k1_zfmisc_1 @
% 6.02/6.22                        ( k2_zfmisc_1 @
% 6.02/6.22                          ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.02/6.22                  ( ![D:$i]:
% 6.02/6.22                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 6.02/6.22                      ( ![E:$i]:
% 6.02/6.22                        ( ( ( ~( v2_struct_0 @ E ) ) & ( m1_pre_topc @ E @ A ) ) =>
% 6.02/6.22                          ( ( ( A ) = ( k1_tsep_1 @ A @ D @ E ) ) =>
% 6.02/6.22                            ( ![F:$i]:
% 6.02/6.22                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ A ) ) =>
% 6.02/6.22                                ( ![G:$i]:
% 6.02/6.22                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 6.02/6.22                                    ( ![H:$i]:
% 6.02/6.22                                      ( ( m1_subset_1 @ H @ ( u1_struct_0 @ E ) ) =>
% 6.02/6.22                                        ( ( ( ( F ) = ( G ) ) & 
% 6.02/6.22                                            ( ( F ) = ( H ) ) ) =>
% 6.02/6.22                                          ( ( r1_tmap_1 @ A @ B @ C @ F ) <=>
% 6.02/6.22                                            ( ( r1_tmap_1 @
% 6.02/6.22                                                D @ B @ 
% 6.02/6.22                                                ( k2_tmap_1 @ A @ B @ C @ D ) @ 
% 6.02/6.22                                                G ) & 
% 6.02/6.22                                              ( r1_tmap_1 @
% 6.02/6.22                                                E @ B @ 
% 6.02/6.22                                                ( k2_tmap_1 @ A @ B @ C @ E ) @ 
% 6.02/6.22                                                H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 6.02/6.22    inference('cnf.neg', [status(esa)], [t125_tmap_1])).
% 6.02/6.22  thf('0', plain, (~ (v2_struct_0 @ sk_D)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('1', plain,
% 6.02/6.22      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 6.02/6.22         sk_H)
% 6.02/6.22        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('2', plain,
% 6.02/6.22      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 6.02/6.22         sk_H))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 6.02/6.22      inference('split', [status(esa)], ['1'])).
% 6.02/6.22  thf('3', plain, (((sk_F) = (sk_H))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('4', plain, (((sk_F) = (sk_G))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('5', plain, (((sk_H) = (sk_G))),
% 6.02/6.22      inference('sup+', [status(thm)], ['3', '4'])).
% 6.02/6.22  thf('6', plain,
% 6.02/6.22      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 6.02/6.22         sk_G))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 6.02/6.22      inference('demod', [status(thm)], ['2', '5'])).
% 6.02/6.22  thf('7', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('8', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('9', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf(dt_k1_tsep_1, axiom,
% 6.02/6.22    (![A:$i,B:$i,C:$i]:
% 6.02/6.22     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_pre_topc @ A ) & 
% 6.02/6.22         ( ~( v2_struct_0 @ B ) ) & ( m1_pre_topc @ B @ A ) & 
% 6.02/6.22         ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 6.02/6.22       ( ( ~( v2_struct_0 @ ( k1_tsep_1 @ A @ B @ C ) ) ) & 
% 6.02/6.22         ( v1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) ) & 
% 6.02/6.22         ( m1_pre_topc @ ( k1_tsep_1 @ A @ B @ C ) @ A ) ) ))).
% 6.02/6.22  thf('10', plain,
% 6.02/6.22      (![X9 : $i, X10 : $i, X11 : $i]:
% 6.02/6.22         (~ (m1_pre_topc @ X9 @ X10)
% 6.02/6.22          | (v2_struct_0 @ X9)
% 6.02/6.22          | ~ (l1_pre_topc @ X10)
% 6.02/6.22          | (v2_struct_0 @ X10)
% 6.02/6.22          | (v2_struct_0 @ X11)
% 6.02/6.22          | ~ (m1_pre_topc @ X11 @ X10)
% 6.02/6.22          | (m1_pre_topc @ (k1_tsep_1 @ X10 @ X9 @ X11) @ X10))),
% 6.02/6.22      inference('cnf', [status(esa)], [dt_k1_tsep_1])).
% 6.02/6.22  thf('11', plain,
% 6.02/6.22      (![X0 : $i]:
% 6.02/6.22         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 6.02/6.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ X0)
% 6.02/6.22          | (v2_struct_0 @ sk_A)
% 6.02/6.22          | ~ (l1_pre_topc @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_D))),
% 6.02/6.22      inference('sup-', [status(thm)], ['9', '10'])).
% 6.02/6.22  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('13', plain,
% 6.02/6.22      (![X0 : $i]:
% 6.02/6.22         ((m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ X0) @ sk_A)
% 6.02/6.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ X0)
% 6.02/6.22          | (v2_struct_0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_D))),
% 6.02/6.22      inference('demod', [status(thm)], ['11', '12'])).
% 6.02/6.22  thf('14', plain,
% 6.02/6.22      (((v2_struct_0 @ sk_D)
% 6.02/6.22        | (v2_struct_0 @ sk_A)
% 6.02/6.22        | (v2_struct_0 @ sk_E)
% 6.02/6.22        | (m1_pre_topc @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ sk_A))),
% 6.02/6.22      inference('sup-', [status(thm)], ['8', '13'])).
% 6.02/6.22  thf('15', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('16', plain,
% 6.02/6.22      (((v2_struct_0 @ sk_D)
% 6.02/6.22        | (v2_struct_0 @ sk_A)
% 6.02/6.22        | (v2_struct_0 @ sk_E)
% 6.02/6.22        | (m1_pre_topc @ sk_A @ sk_A))),
% 6.02/6.22      inference('demod', [status(thm)], ['14', '15'])).
% 6.02/6.22  thf('17', plain,
% 6.02/6.22      ((m1_subset_1 @ sk_C @ 
% 6.02/6.22        (k1_zfmisc_1 @ 
% 6.02/6.22         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf(d5_tmap_1, axiom,
% 6.02/6.22    (![A:$i]:
% 6.02/6.22     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.02/6.22       ( ![B:$i]:
% 6.02/6.22         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 6.02/6.22             ( l1_pre_topc @ B ) ) =>
% 6.02/6.22           ( ![C:$i]:
% 6.02/6.22             ( ( m1_pre_topc @ C @ A ) =>
% 6.02/6.22               ( ![D:$i]:
% 6.02/6.22                 ( ( m1_pre_topc @ D @ A ) =>
% 6.02/6.22                   ( ![E:$i]:
% 6.02/6.22                     ( ( ( v1_funct_1 @ E ) & 
% 6.02/6.22                         ( v1_funct_2 @
% 6.02/6.22                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 6.02/6.22                         ( m1_subset_1 @
% 6.02/6.22                           E @ 
% 6.02/6.22                           ( k1_zfmisc_1 @
% 6.02/6.22                             ( k2_zfmisc_1 @
% 6.02/6.22                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.02/6.22                       ( ( m1_pre_topc @ D @ C ) =>
% 6.02/6.22                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 6.02/6.22                           ( k2_partfun1 @
% 6.02/6.22                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 6.02/6.22                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 6.02/6.22  thf('18', plain,
% 6.02/6.22      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 6.02/6.22         ((v2_struct_0 @ X4)
% 6.02/6.22          | ~ (v2_pre_topc @ X4)
% 6.02/6.22          | ~ (l1_pre_topc @ X4)
% 6.02/6.22          | ~ (m1_pre_topc @ X5 @ X6)
% 6.02/6.22          | ~ (m1_pre_topc @ X5 @ X7)
% 6.02/6.22          | ((k3_tmap_1 @ X6 @ X4 @ X7 @ X5 @ X8)
% 6.02/6.22              = (k2_partfun1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4) @ X8 @ 
% 6.02/6.22                 (u1_struct_0 @ X5)))
% 6.02/6.22          | ~ (m1_subset_1 @ X8 @ 
% 6.02/6.22               (k1_zfmisc_1 @ 
% 6.02/6.22                (k2_zfmisc_1 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4))))
% 6.02/6.22          | ~ (v1_funct_2 @ X8 @ (u1_struct_0 @ X7) @ (u1_struct_0 @ X4))
% 6.02/6.22          | ~ (v1_funct_1 @ X8)
% 6.02/6.22          | ~ (m1_pre_topc @ X7 @ X6)
% 6.02/6.22          | ~ (l1_pre_topc @ X6)
% 6.02/6.22          | ~ (v2_pre_topc @ X6)
% 6.02/6.22          | (v2_struct_0 @ X6))),
% 6.02/6.22      inference('cnf', [status(esa)], [d5_tmap_1])).
% 6.02/6.22  thf('19', plain,
% 6.02/6.22      (![X0 : $i, X1 : $i]:
% 6.02/6.22         ((v2_struct_0 @ X0)
% 6.02/6.22          | ~ (v2_pre_topc @ X0)
% 6.02/6.22          | ~ (l1_pre_topc @ X0)
% 6.02/6.22          | ~ (m1_pre_topc @ sk_A @ X0)
% 6.02/6.22          | ~ (v1_funct_1 @ sk_C)
% 6.02/6.22          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 6.02/6.22          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C)
% 6.02/6.22              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.02/6.22                 sk_C @ (u1_struct_0 @ X1)))
% 6.02/6.22          | ~ (m1_pre_topc @ X1 @ sk_A)
% 6.02/6.22          | ~ (m1_pre_topc @ X1 @ X0)
% 6.02/6.22          | ~ (l1_pre_topc @ sk_B)
% 6.02/6.22          | ~ (v2_pre_topc @ sk_B)
% 6.02/6.22          | (v2_struct_0 @ sk_B))),
% 6.02/6.22      inference('sup-', [status(thm)], ['17', '18'])).
% 6.02/6.22  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('21', plain,
% 6.02/6.22      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('22', plain, ((l1_pre_topc @ sk_B)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('23', plain, ((v2_pre_topc @ sk_B)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('24', plain,
% 6.02/6.22      (![X0 : $i, X1 : $i]:
% 6.02/6.22         ((v2_struct_0 @ X0)
% 6.02/6.22          | ~ (v2_pre_topc @ X0)
% 6.02/6.22          | ~ (l1_pre_topc @ X0)
% 6.02/6.22          | ~ (m1_pre_topc @ sk_A @ X0)
% 6.02/6.22          | ((k3_tmap_1 @ X0 @ sk_B @ sk_A @ X1 @ sk_C)
% 6.02/6.22              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.02/6.22                 sk_C @ (u1_struct_0 @ X1)))
% 6.02/6.22          | ~ (m1_pre_topc @ X1 @ sk_A)
% 6.02/6.22          | ~ (m1_pre_topc @ X1 @ X0)
% 6.02/6.22          | (v2_struct_0 @ sk_B))),
% 6.02/6.22      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 6.02/6.22  thf('25', plain,
% 6.02/6.22      (![X0 : $i]:
% 6.02/6.22         ((v2_struct_0 @ sk_E)
% 6.02/6.22          | (v2_struct_0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | (v2_struct_0 @ sk_B)
% 6.02/6.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 6.02/6.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 6.02/6.22          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 6.02/6.22              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.02/6.22                 sk_C @ (u1_struct_0 @ X0)))
% 6.02/6.22          | ~ (l1_pre_topc @ sk_A)
% 6.02/6.22          | ~ (v2_pre_topc @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_A))),
% 6.02/6.22      inference('sup-', [status(thm)], ['16', '24'])).
% 6.02/6.22  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('28', plain,
% 6.02/6.22      (![X0 : $i]:
% 6.02/6.22         ((v2_struct_0 @ sk_E)
% 6.02/6.22          | (v2_struct_0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | (v2_struct_0 @ sk_B)
% 6.02/6.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 6.02/6.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 6.02/6.22          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 6.02/6.22              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.02/6.22                 sk_C @ (u1_struct_0 @ X0)))
% 6.02/6.22          | (v2_struct_0 @ sk_A))),
% 6.02/6.22      inference('demod', [status(thm)], ['25', '26', '27'])).
% 6.02/6.22  thf('29', plain,
% 6.02/6.22      (![X0 : $i]:
% 6.02/6.22         (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 6.02/6.22            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.02/6.22               sk_C @ (u1_struct_0 @ X0)))
% 6.02/6.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_B)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | (v2_struct_0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_E))),
% 6.02/6.22      inference('simplify', [status(thm)], ['28'])).
% 6.02/6.22  thf('30', plain,
% 6.02/6.22      (((v2_struct_0 @ sk_E)
% 6.02/6.22        | (v2_struct_0 @ sk_A)
% 6.02/6.22        | (v2_struct_0 @ sk_D)
% 6.02/6.22        | (v2_struct_0 @ sk_B)
% 6.02/6.22        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C)
% 6.02/6.22            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.02/6.22               sk_C @ (u1_struct_0 @ sk_D))))),
% 6.02/6.22      inference('sup-', [status(thm)], ['7', '29'])).
% 6.02/6.22  thf('31', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('32', plain,
% 6.02/6.22      ((m1_subset_1 @ sk_C @ 
% 6.02/6.22        (k1_zfmisc_1 @ 
% 6.02/6.22         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf(d4_tmap_1, axiom,
% 6.02/6.22    (![A:$i]:
% 6.02/6.22     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.02/6.22       ( ![B:$i]:
% 6.02/6.22         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 6.02/6.22             ( l1_pre_topc @ B ) ) =>
% 6.02/6.22           ( ![C:$i]:
% 6.02/6.22             ( ( ( v1_funct_1 @ C ) & 
% 6.02/6.22                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 6.02/6.22                 ( m1_subset_1 @
% 6.02/6.22                   C @ 
% 6.02/6.22                   ( k1_zfmisc_1 @
% 6.02/6.22                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.02/6.22               ( ![D:$i]:
% 6.02/6.22                 ( ( m1_pre_topc @ D @ A ) =>
% 6.02/6.22                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 6.02/6.22                     ( k2_partfun1 @
% 6.02/6.22                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 6.02/6.22                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 6.02/6.22  thf('33', plain,
% 6.02/6.22      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 6.02/6.22         ((v2_struct_0 @ X0)
% 6.02/6.22          | ~ (v2_pre_topc @ X0)
% 6.02/6.22          | ~ (l1_pre_topc @ X0)
% 6.02/6.22          | ~ (m1_pre_topc @ X1 @ X2)
% 6.02/6.22          | ((k2_tmap_1 @ X2 @ X0 @ X3 @ X1)
% 6.02/6.22              = (k2_partfun1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0) @ X3 @ 
% 6.02/6.22                 (u1_struct_0 @ X1)))
% 6.02/6.22          | ~ (m1_subset_1 @ X3 @ 
% 6.02/6.22               (k1_zfmisc_1 @ 
% 6.02/6.22                (k2_zfmisc_1 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))))
% 6.02/6.22          | ~ (v1_funct_2 @ X3 @ (u1_struct_0 @ X2) @ (u1_struct_0 @ X0))
% 6.02/6.22          | ~ (v1_funct_1 @ X3)
% 6.02/6.22          | ~ (l1_pre_topc @ X2)
% 6.02/6.22          | ~ (v2_pre_topc @ X2)
% 6.02/6.22          | (v2_struct_0 @ X2))),
% 6.02/6.22      inference('cnf', [status(esa)], [d4_tmap_1])).
% 6.02/6.22  thf('34', plain,
% 6.02/6.22      (![X0 : $i]:
% 6.02/6.22         ((v2_struct_0 @ sk_A)
% 6.02/6.22          | ~ (v2_pre_topc @ sk_A)
% 6.02/6.22          | ~ (l1_pre_topc @ sk_A)
% 6.02/6.22          | ~ (v1_funct_1 @ sk_C)
% 6.02/6.22          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 6.02/6.22          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 6.02/6.22              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.02/6.22                 sk_C @ (u1_struct_0 @ X0)))
% 6.02/6.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 6.02/6.22          | ~ (l1_pre_topc @ sk_B)
% 6.02/6.22          | ~ (v2_pre_topc @ sk_B)
% 6.02/6.22          | (v2_struct_0 @ sk_B))),
% 6.02/6.22      inference('sup-', [status(thm)], ['32', '33'])).
% 6.02/6.22  thf('35', plain, ((v2_pre_topc @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('36', plain, ((l1_pre_topc @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('38', plain,
% 6.02/6.22      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('39', plain, ((l1_pre_topc @ sk_B)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('40', plain, ((v2_pre_topc @ sk_B)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('41', plain,
% 6.02/6.22      (![X0 : $i]:
% 6.02/6.22         ((v2_struct_0 @ sk_A)
% 6.02/6.22          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 6.02/6.22              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.02/6.22                 sk_C @ (u1_struct_0 @ X0)))
% 6.02/6.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_B))),
% 6.02/6.22      inference('demod', [status(thm)],
% 6.02/6.22                ['34', '35', '36', '37', '38', '39', '40'])).
% 6.02/6.22  thf('42', plain,
% 6.02/6.22      (((v2_struct_0 @ sk_B)
% 6.02/6.22        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 6.02/6.22            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.02/6.22               sk_C @ (u1_struct_0 @ sk_D)))
% 6.02/6.22        | (v2_struct_0 @ sk_A))),
% 6.02/6.22      inference('sup-', [status(thm)], ['31', '41'])).
% 6.02/6.22  thf('43', plain, (~ (v2_struct_0 @ sk_B)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('44', plain,
% 6.02/6.22      (((v2_struct_0 @ sk_A)
% 6.02/6.22        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 6.02/6.22            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.02/6.22               sk_C @ (u1_struct_0 @ sk_D))))),
% 6.02/6.22      inference('clc', [status(thm)], ['42', '43'])).
% 6.02/6.22  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('46', plain,
% 6.02/6.22      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 6.02/6.22         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 6.02/6.22            (u1_struct_0 @ sk_D)))),
% 6.02/6.22      inference('clc', [status(thm)], ['44', '45'])).
% 6.02/6.22  thf('47', plain,
% 6.02/6.22      ((((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 6.02/6.22          = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))
% 6.02/6.22        | (v2_struct_0 @ sk_B)
% 6.02/6.22        | (v2_struct_0 @ sk_D)
% 6.02/6.22        | (v2_struct_0 @ sk_A)
% 6.02/6.22        | (v2_struct_0 @ sk_E))),
% 6.02/6.22      inference('sup+', [status(thm)], ['30', '46'])).
% 6.02/6.22  thf('48', plain,
% 6.02/6.22      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 6.02/6.22         sk_G)
% 6.02/6.22        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('49', plain,
% 6.02/6.22      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('split', [status(esa)], ['48'])).
% 6.02/6.22  thf('50', plain, (((sk_F) = (sk_G))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('51', plain,
% 6.02/6.22      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('demod', [status(thm)], ['49', '50'])).
% 6.02/6.22  thf('52', plain,
% 6.02/6.22      ((m1_subset_1 @ sk_C @ 
% 6.02/6.22        (k1_zfmisc_1 @ 
% 6.02/6.22         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('53', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf(t123_tmap_1, axiom,
% 6.02/6.22    (![A:$i]:
% 6.02/6.22     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 6.02/6.22       ( ![B:$i]:
% 6.02/6.22         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 6.02/6.22             ( l1_pre_topc @ B ) ) =>
% 6.02/6.22           ( ![C:$i]:
% 6.02/6.22             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 6.02/6.22               ( ![D:$i]:
% 6.02/6.22                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 6.02/6.22                   ( ![E:$i]:
% 6.02/6.22                     ( ( ( v1_funct_1 @ E ) & 
% 6.02/6.22                         ( v1_funct_2 @
% 6.02/6.22                           E @ ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 6.02/6.22                           ( u1_struct_0 @ B ) ) & 
% 6.02/6.22                         ( m1_subset_1 @
% 6.02/6.22                           E @ 
% 6.02/6.22                           ( k1_zfmisc_1 @
% 6.02/6.22                             ( k2_zfmisc_1 @
% 6.02/6.22                               ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) @ 
% 6.02/6.22                               ( u1_struct_0 @ B ) ) ) ) ) =>
% 6.02/6.22                       ( ![F:$i]:
% 6.02/6.22                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ C ) ) =>
% 6.02/6.22                           ( ![G:$i]:
% 6.02/6.22                             ( ( m1_subset_1 @ G @ ( u1_struct_0 @ D ) ) =>
% 6.02/6.22                               ( ![H:$i]:
% 6.02/6.22                                 ( ( m1_subset_1 @
% 6.02/6.22                                     H @ 
% 6.02/6.22                                     ( u1_struct_0 @ ( k1_tsep_1 @ A @ C @ D ) ) ) =>
% 6.02/6.22                                   ( ( ( ( H ) = ( F ) ) & ( ( H ) = ( G ) ) ) =>
% 6.02/6.22                                     ( ( r1_tmap_1 @
% 6.02/6.22                                         ( k1_tsep_1 @ A @ C @ D ) @ B @ E @ H ) <=>
% 6.02/6.22                                       ( ( r1_tmap_1 @
% 6.02/6.22                                           C @ B @ 
% 6.02/6.22                                           ( k3_tmap_1 @
% 6.02/6.22                                             A @ B @ 
% 6.02/6.22                                             ( k1_tsep_1 @ A @ C @ D ) @ C @ E ) @ 
% 6.02/6.22                                           F ) & 
% 6.02/6.22                                         ( r1_tmap_1 @
% 6.02/6.22                                           D @ B @ 
% 6.02/6.22                                           ( k3_tmap_1 @
% 6.02/6.22                                             A @ B @ 
% 6.02/6.22                                             ( k1_tsep_1 @ A @ C @ D ) @ D @ E ) @ 
% 6.02/6.22                                           G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 6.02/6.22  thf('54', plain,
% 6.02/6.22      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, 
% 6.02/6.22         X19 : $i]:
% 6.02/6.22         ((v2_struct_0 @ X12)
% 6.02/6.22          | ~ (v2_pre_topc @ X12)
% 6.02/6.22          | ~ (l1_pre_topc @ X12)
% 6.02/6.22          | (v2_struct_0 @ X13)
% 6.02/6.22          | ~ (m1_pre_topc @ X13 @ X14)
% 6.02/6.22          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 6.02/6.22          | ~ (m1_subset_1 @ X17 @ 
% 6.02/6.22               (u1_struct_0 @ (k1_tsep_1 @ X14 @ X16 @ X13)))
% 6.02/6.22          | ~ (r1_tmap_1 @ (k1_tsep_1 @ X14 @ X16 @ X13) @ X12 @ X18 @ X17)
% 6.02/6.22          | (r1_tmap_1 @ X16 @ X12 @ 
% 6.02/6.22             (k3_tmap_1 @ X14 @ X12 @ (k1_tsep_1 @ X14 @ X16 @ X13) @ X16 @ X18) @ 
% 6.02/6.22             X15)
% 6.02/6.22          | ((X17) != (X19))
% 6.02/6.22          | ((X17) != (X15))
% 6.02/6.22          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X13))
% 6.02/6.22          | ~ (m1_subset_1 @ X18 @ 
% 6.02/6.22               (k1_zfmisc_1 @ 
% 6.02/6.22                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X14 @ X16 @ X13)) @ 
% 6.02/6.22                 (u1_struct_0 @ X12))))
% 6.02/6.22          | ~ (v1_funct_2 @ X18 @ 
% 6.02/6.22               (u1_struct_0 @ (k1_tsep_1 @ X14 @ X16 @ X13)) @ 
% 6.02/6.22               (u1_struct_0 @ X12))
% 6.02/6.22          | ~ (v1_funct_1 @ X18)
% 6.02/6.22          | ~ (m1_pre_topc @ X16 @ X14)
% 6.02/6.22          | (v2_struct_0 @ X16)
% 6.02/6.22          | ~ (l1_pre_topc @ X14)
% 6.02/6.22          | ~ (v2_pre_topc @ X14)
% 6.02/6.22          | (v2_struct_0 @ X14))),
% 6.02/6.22      inference('cnf', [status(esa)], [t123_tmap_1])).
% 6.02/6.22  thf('55', plain,
% 6.02/6.22      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 6.02/6.22         ((v2_struct_0 @ X14)
% 6.02/6.22          | ~ (v2_pre_topc @ X14)
% 6.02/6.22          | ~ (l1_pre_topc @ X14)
% 6.02/6.22          | (v2_struct_0 @ X16)
% 6.02/6.22          | ~ (m1_pre_topc @ X16 @ X14)
% 6.02/6.22          | ~ (v1_funct_1 @ X18)
% 6.02/6.22          | ~ (v1_funct_2 @ X18 @ 
% 6.02/6.22               (u1_struct_0 @ (k1_tsep_1 @ X14 @ X16 @ X13)) @ 
% 6.02/6.22               (u1_struct_0 @ X12))
% 6.02/6.22          | ~ (m1_subset_1 @ X18 @ 
% 6.02/6.22               (k1_zfmisc_1 @ 
% 6.02/6.22                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X14 @ X16 @ X13)) @ 
% 6.02/6.22                 (u1_struct_0 @ X12))))
% 6.02/6.22          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X13))
% 6.02/6.22          | (r1_tmap_1 @ X16 @ X12 @ 
% 6.02/6.22             (k3_tmap_1 @ X14 @ X12 @ (k1_tsep_1 @ X14 @ X16 @ X13) @ X16 @ X18) @ 
% 6.02/6.22             X19)
% 6.02/6.22          | ~ (r1_tmap_1 @ (k1_tsep_1 @ X14 @ X16 @ X13) @ X12 @ X18 @ X19)
% 6.02/6.22          | ~ (m1_subset_1 @ X19 @ 
% 6.02/6.22               (u1_struct_0 @ (k1_tsep_1 @ X14 @ X16 @ X13)))
% 6.02/6.22          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X16))
% 6.02/6.22          | ~ (m1_pre_topc @ X13 @ X14)
% 6.02/6.22          | (v2_struct_0 @ X13)
% 6.02/6.22          | ~ (l1_pre_topc @ X12)
% 6.02/6.22          | ~ (v2_pre_topc @ X12)
% 6.02/6.22          | (v2_struct_0 @ X12))),
% 6.02/6.22      inference('simplify', [status(thm)], ['54'])).
% 6.02/6.22  thf('56', plain,
% 6.02/6.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.02/6.22         (~ (m1_subset_1 @ X1 @ 
% 6.02/6.22             (k1_zfmisc_1 @ 
% 6.02/6.22              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 6.02/6.22          | (v2_struct_0 @ X0)
% 6.02/6.22          | ~ (v2_pre_topc @ X0)
% 6.02/6.22          | ~ (l1_pre_topc @ X0)
% 6.02/6.22          | (v2_struct_0 @ sk_E)
% 6.02/6.22          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 6.02/6.22          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 6.02/6.22          | ~ (m1_subset_1 @ X2 @ 
% 6.02/6.22               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 6.02/6.22          | ~ (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0 @ X1 @ X2)
% 6.02/6.22          | (r1_tmap_1 @ sk_D @ X0 @ 
% 6.02/6.22             (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 6.02/6.22              sk_D @ X1) @ 
% 6.02/6.22             X2)
% 6.02/6.22          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_E))
% 6.02/6.22          | ~ (v1_funct_2 @ X1 @ 
% 6.02/6.22               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 6.02/6.22               (u1_struct_0 @ X0))
% 6.02/6.22          | ~ (v1_funct_1 @ X1)
% 6.02/6.22          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | ~ (l1_pre_topc @ sk_A)
% 6.02/6.22          | ~ (v2_pre_topc @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_A))),
% 6.02/6.22      inference('sup-', [status(thm)], ['53', '55'])).
% 6.02/6.22  thf('57', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('58', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('59', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('60', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('61', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('62', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('64', plain, ((v2_pre_topc @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('65', plain,
% 6.02/6.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.02/6.22         (~ (m1_subset_1 @ X1 @ 
% 6.02/6.22             (k1_zfmisc_1 @ 
% 6.02/6.22              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 6.02/6.22          | (v2_struct_0 @ X0)
% 6.02/6.22          | ~ (v2_pre_topc @ X0)
% 6.02/6.22          | ~ (l1_pre_topc @ X0)
% 6.02/6.22          | (v2_struct_0 @ sk_E)
% 6.02/6.22          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 6.02/6.22          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_A @ X0 @ X1 @ X2)
% 6.02/6.22          | (r1_tmap_1 @ sk_D @ X0 @ 
% 6.02/6.22             (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ X2)
% 6.02/6.22          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_E))
% 6.02/6.22          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 6.02/6.22          | ~ (v1_funct_1 @ X1)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | (v2_struct_0 @ sk_A))),
% 6.02/6.22      inference('demod', [status(thm)],
% 6.02/6.22                ['56', '57', '58', '59', '60', '61', '62', '63', '64'])).
% 6.02/6.22  thf('66', plain,
% 6.02/6.22      (![X0 : $i]:
% 6.02/6.22         ((v2_struct_0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | ~ (v1_funct_1 @ sk_C)
% 6.02/6.22          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 6.02/6.22          | (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ X0)
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 6.02/6.22          | (v2_struct_0 @ sk_E)
% 6.02/6.22          | ~ (l1_pre_topc @ sk_B)
% 6.02/6.22          | ~ (v2_pre_topc @ sk_B)
% 6.02/6.22          | (v2_struct_0 @ sk_B))),
% 6.02/6.22      inference('sup-', [status(thm)], ['52', '65'])).
% 6.02/6.22  thf('67', plain, ((v1_funct_1 @ sk_C)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('68', plain,
% 6.02/6.22      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('69', plain, ((l1_pre_topc @ sk_B)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('70', plain, ((v2_pre_topc @ sk_B)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('71', plain,
% 6.02/6.22      (![X0 : $i]:
% 6.02/6.22         ((v2_struct_0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 6.02/6.22          | (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ X0)
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 6.02/6.22          | (v2_struct_0 @ sk_E)
% 6.02/6.22          | (v2_struct_0 @ sk_B))),
% 6.02/6.22      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 6.02/6.22  thf('72', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_B)
% 6.02/6.22         | (v2_struct_0 @ sk_E)
% 6.02/6.22         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 6.02/6.22         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))
% 6.02/6.22         | (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_G)
% 6.02/6.22         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_A)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('sup-', [status(thm)], ['51', '71'])).
% 6.02/6.22  thf('73', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('74', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_A))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('75', plain, (((sk_F) = (sk_G))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('76', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 6.02/6.22      inference('demod', [status(thm)], ['74', '75'])).
% 6.02/6.22  thf('77', plain, ((m1_subset_1 @ sk_H @ (u1_struct_0 @ sk_E))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('78', plain, (((sk_H) = (sk_G))),
% 6.02/6.22      inference('sup+', [status(thm)], ['3', '4'])).
% 6.02/6.22  thf('79', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))),
% 6.02/6.22      inference('demod', [status(thm)], ['77', '78'])).
% 6.02/6.22  thf('80', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_B)
% 6.02/6.22         | (v2_struct_0 @ sk_E)
% 6.02/6.22         | (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_G)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_A)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('demod', [status(thm)], ['72', '73', '76', '79'])).
% 6.02/6.22  thf('81', plain,
% 6.02/6.22      ((((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 6.02/6.22          sk_G)
% 6.02/6.22         | (v2_struct_0 @ sk_E)
% 6.02/6.22         | (v2_struct_0 @ sk_A)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_B)
% 6.02/6.22         | (v2_struct_0 @ sk_A)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_E)
% 6.02/6.22         | (v2_struct_0 @ sk_B)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('sup+', [status(thm)], ['47', '80'])).
% 6.02/6.22  thf('82', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_B)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_A)
% 6.02/6.22         | (v2_struct_0 @ sk_E)
% 6.02/6.22         | (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('simplify', [status(thm)], ['81'])).
% 6.02/6.22  thf('83', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('84', plain,
% 6.02/6.22      (![X0 : $i]:
% 6.02/6.22         (((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ X0 @ sk_C)
% 6.02/6.22            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.02/6.22               sk_C @ (u1_struct_0 @ X0)))
% 6.02/6.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_B)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | (v2_struct_0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_E))),
% 6.02/6.22      inference('simplify', [status(thm)], ['28'])).
% 6.02/6.22  thf('85', plain,
% 6.02/6.22      (((v2_struct_0 @ sk_E)
% 6.02/6.22        | (v2_struct_0 @ sk_A)
% 6.02/6.22        | (v2_struct_0 @ sk_D)
% 6.02/6.22        | (v2_struct_0 @ sk_B)
% 6.02/6.22        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C)
% 6.02/6.22            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.02/6.22               sk_C @ (u1_struct_0 @ sk_E))))),
% 6.02/6.22      inference('sup-', [status(thm)], ['83', '84'])).
% 6.02/6.22  thf('86', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('87', plain,
% 6.02/6.22      (![X0 : $i]:
% 6.02/6.22         ((v2_struct_0 @ sk_A)
% 6.02/6.22          | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 6.02/6.22              = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.02/6.22                 sk_C @ (u1_struct_0 @ X0)))
% 6.02/6.22          | ~ (m1_pre_topc @ X0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_B))),
% 6.02/6.22      inference('demod', [status(thm)],
% 6.02/6.22                ['34', '35', '36', '37', '38', '39', '40'])).
% 6.02/6.22  thf('88', plain,
% 6.02/6.22      (((v2_struct_0 @ sk_B)
% 6.02/6.22        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 6.02/6.22            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.02/6.22               sk_C @ (u1_struct_0 @ sk_E)))
% 6.02/6.22        | (v2_struct_0 @ sk_A))),
% 6.02/6.22      inference('sup-', [status(thm)], ['86', '87'])).
% 6.02/6.22  thf('89', plain, (~ (v2_struct_0 @ sk_B)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('90', plain,
% 6.02/6.22      (((v2_struct_0 @ sk_A)
% 6.02/6.22        | ((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 6.02/6.22            = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ 
% 6.02/6.22               sk_C @ (u1_struct_0 @ sk_E))))),
% 6.02/6.22      inference('clc', [status(thm)], ['88', '89'])).
% 6.02/6.22  thf('91', plain, (~ (v2_struct_0 @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('92', plain,
% 6.02/6.22      (((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 6.02/6.22         = (k2_partfun1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B) @ sk_C @ 
% 6.02/6.22            (u1_struct_0 @ sk_E)))),
% 6.02/6.22      inference('clc', [status(thm)], ['90', '91'])).
% 6.02/6.22  thf('93', plain,
% 6.02/6.22      ((((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 6.02/6.22          = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))
% 6.02/6.22        | (v2_struct_0 @ sk_B)
% 6.02/6.22        | (v2_struct_0 @ sk_D)
% 6.02/6.22        | (v2_struct_0 @ sk_A)
% 6.02/6.22        | (v2_struct_0 @ sk_E))),
% 6.02/6.22      inference('sup+', [status(thm)], ['85', '92'])).
% 6.02/6.22  thf('94', plain,
% 6.02/6.22      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('demod', [status(thm)], ['49', '50'])).
% 6.02/6.22  thf('95', plain,
% 6.02/6.22      ((m1_subset_1 @ sk_C @ 
% 6.02/6.22        (k1_zfmisc_1 @ 
% 6.02/6.22         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('96', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('97', plain,
% 6.02/6.22      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, 
% 6.02/6.22         X19 : $i]:
% 6.02/6.22         ((v2_struct_0 @ X12)
% 6.02/6.22          | ~ (v2_pre_topc @ X12)
% 6.02/6.22          | ~ (l1_pre_topc @ X12)
% 6.02/6.22          | (v2_struct_0 @ X13)
% 6.02/6.22          | ~ (m1_pre_topc @ X13 @ X14)
% 6.02/6.22          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 6.02/6.22          | ~ (m1_subset_1 @ X17 @ 
% 6.02/6.22               (u1_struct_0 @ (k1_tsep_1 @ X14 @ X16 @ X13)))
% 6.02/6.22          | ~ (r1_tmap_1 @ (k1_tsep_1 @ X14 @ X16 @ X13) @ X12 @ X18 @ X17)
% 6.02/6.22          | (r1_tmap_1 @ X13 @ X12 @ 
% 6.02/6.22             (k3_tmap_1 @ X14 @ X12 @ (k1_tsep_1 @ X14 @ X16 @ X13) @ X13 @ X18) @ 
% 6.02/6.22             X19)
% 6.02/6.22          | ((X17) != (X19))
% 6.02/6.22          | ((X17) != (X15))
% 6.02/6.22          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X13))
% 6.02/6.22          | ~ (m1_subset_1 @ X18 @ 
% 6.02/6.22               (k1_zfmisc_1 @ 
% 6.02/6.22                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X14 @ X16 @ X13)) @ 
% 6.02/6.22                 (u1_struct_0 @ X12))))
% 6.02/6.22          | ~ (v1_funct_2 @ X18 @ 
% 6.02/6.22               (u1_struct_0 @ (k1_tsep_1 @ X14 @ X16 @ X13)) @ 
% 6.02/6.22               (u1_struct_0 @ X12))
% 6.02/6.22          | ~ (v1_funct_1 @ X18)
% 6.02/6.22          | ~ (m1_pre_topc @ X16 @ X14)
% 6.02/6.22          | (v2_struct_0 @ X16)
% 6.02/6.22          | ~ (l1_pre_topc @ X14)
% 6.02/6.22          | ~ (v2_pre_topc @ X14)
% 6.02/6.22          | (v2_struct_0 @ X14))),
% 6.02/6.22      inference('cnf', [status(esa)], [t123_tmap_1])).
% 6.02/6.22  thf('98', plain,
% 6.02/6.22      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 6.02/6.22         ((v2_struct_0 @ X14)
% 6.02/6.22          | ~ (v2_pre_topc @ X14)
% 6.02/6.22          | ~ (l1_pre_topc @ X14)
% 6.02/6.22          | (v2_struct_0 @ X16)
% 6.02/6.22          | ~ (m1_pre_topc @ X16 @ X14)
% 6.02/6.22          | ~ (v1_funct_1 @ X18)
% 6.02/6.22          | ~ (v1_funct_2 @ X18 @ 
% 6.02/6.22               (u1_struct_0 @ (k1_tsep_1 @ X14 @ X16 @ X13)) @ 
% 6.02/6.22               (u1_struct_0 @ X12))
% 6.02/6.22          | ~ (m1_subset_1 @ X18 @ 
% 6.02/6.22               (k1_zfmisc_1 @ 
% 6.02/6.22                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X14 @ X16 @ X13)) @ 
% 6.02/6.22                 (u1_struct_0 @ X12))))
% 6.02/6.22          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X13))
% 6.02/6.22          | (r1_tmap_1 @ X13 @ X12 @ 
% 6.02/6.22             (k3_tmap_1 @ X14 @ X12 @ (k1_tsep_1 @ X14 @ X16 @ X13) @ X13 @ X18) @ 
% 6.02/6.22             X19)
% 6.02/6.22          | ~ (r1_tmap_1 @ (k1_tsep_1 @ X14 @ X16 @ X13) @ X12 @ X18 @ X19)
% 6.02/6.22          | ~ (m1_subset_1 @ X19 @ 
% 6.02/6.22               (u1_struct_0 @ (k1_tsep_1 @ X14 @ X16 @ X13)))
% 6.02/6.22          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X16))
% 6.02/6.22          | ~ (m1_pre_topc @ X13 @ X14)
% 6.02/6.22          | (v2_struct_0 @ X13)
% 6.02/6.22          | ~ (l1_pre_topc @ X12)
% 6.02/6.22          | ~ (v2_pre_topc @ X12)
% 6.02/6.22          | (v2_struct_0 @ X12))),
% 6.02/6.22      inference('simplify', [status(thm)], ['97'])).
% 6.02/6.22  thf('99', plain,
% 6.02/6.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.02/6.22         (~ (m1_subset_1 @ X1 @ 
% 6.02/6.22             (k1_zfmisc_1 @ 
% 6.02/6.22              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 6.02/6.22          | (v2_struct_0 @ X0)
% 6.02/6.22          | ~ (v2_pre_topc @ X0)
% 6.02/6.22          | ~ (l1_pre_topc @ X0)
% 6.02/6.22          | (v2_struct_0 @ sk_E)
% 6.02/6.22          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 6.02/6.22          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 6.02/6.22          | ~ (m1_subset_1 @ X2 @ 
% 6.02/6.22               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 6.02/6.22          | ~ (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0 @ X1 @ X2)
% 6.02/6.22          | (r1_tmap_1 @ sk_E @ X0 @ 
% 6.02/6.22             (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 6.02/6.22              sk_E @ X1) @ 
% 6.02/6.22             X2)
% 6.02/6.22          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_E))
% 6.02/6.22          | ~ (v1_funct_2 @ X1 @ 
% 6.02/6.22               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 6.02/6.22               (u1_struct_0 @ X0))
% 6.02/6.22          | ~ (v1_funct_1 @ X1)
% 6.02/6.22          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | ~ (l1_pre_topc @ sk_A)
% 6.02/6.22          | ~ (v2_pre_topc @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_A))),
% 6.02/6.22      inference('sup-', [status(thm)], ['96', '98'])).
% 6.02/6.22  thf('100', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('101', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('102', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('103', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('104', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('105', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('107', plain, ((v2_pre_topc @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('108', plain,
% 6.02/6.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.02/6.22         (~ (m1_subset_1 @ X1 @ 
% 6.02/6.22             (k1_zfmisc_1 @ 
% 6.02/6.22              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 6.02/6.22          | (v2_struct_0 @ X0)
% 6.02/6.22          | ~ (v2_pre_topc @ X0)
% 6.02/6.22          | ~ (l1_pre_topc @ X0)
% 6.02/6.22          | (v2_struct_0 @ sk_E)
% 6.02/6.22          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 6.02/6.22          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_A @ X0 @ X1 @ X2)
% 6.02/6.22          | (r1_tmap_1 @ sk_E @ X0 @ 
% 6.02/6.22             (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1) @ X2)
% 6.02/6.22          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_E))
% 6.02/6.22          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 6.02/6.22          | ~ (v1_funct_1 @ X1)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | (v2_struct_0 @ sk_A))),
% 6.02/6.22      inference('demod', [status(thm)],
% 6.02/6.22                ['99', '100', '101', '102', '103', '104', '105', '106', '107'])).
% 6.02/6.22  thf('109', plain,
% 6.02/6.22      (![X0 : $i]:
% 6.02/6.22         ((v2_struct_0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | ~ (v1_funct_1 @ sk_C)
% 6.02/6.22          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 6.02/6.22          | (r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C) @ X0)
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 6.02/6.22          | (v2_struct_0 @ sk_E)
% 6.02/6.22          | ~ (l1_pre_topc @ sk_B)
% 6.02/6.22          | ~ (v2_pre_topc @ sk_B)
% 6.02/6.22          | (v2_struct_0 @ sk_B))),
% 6.02/6.22      inference('sup-', [status(thm)], ['95', '108'])).
% 6.02/6.22  thf('110', plain, ((v1_funct_1 @ sk_C)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('111', plain,
% 6.02/6.22      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('112', plain, ((l1_pre_topc @ sk_B)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('113', plain, ((v2_pre_topc @ sk_B)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('114', plain,
% 6.02/6.22      (![X0 : $i]:
% 6.02/6.22         ((v2_struct_0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 6.02/6.22          | (r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C) @ X0)
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 6.02/6.22          | (v2_struct_0 @ sk_E)
% 6.02/6.22          | (v2_struct_0 @ sk_B))),
% 6.02/6.22      inference('demod', [status(thm)], ['109', '110', '111', '112', '113'])).
% 6.02/6.22  thf('115', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_B)
% 6.02/6.22         | (v2_struct_0 @ sk_E)
% 6.02/6.22         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 6.02/6.22         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))
% 6.02/6.22         | (r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C) @ sk_G)
% 6.02/6.22         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_A)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('sup-', [status(thm)], ['94', '114'])).
% 6.02/6.22  thf('116', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('117', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 6.02/6.22      inference('demod', [status(thm)], ['74', '75'])).
% 6.02/6.22  thf('118', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))),
% 6.02/6.22      inference('demod', [status(thm)], ['77', '78'])).
% 6.02/6.22  thf('119', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_B)
% 6.02/6.22         | (v2_struct_0 @ sk_E)
% 6.02/6.22         | (r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C) @ sk_G)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_A)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('demod', [status(thm)], ['115', '116', '117', '118'])).
% 6.02/6.22  thf('120', plain,
% 6.02/6.22      ((((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 6.02/6.22          sk_G)
% 6.02/6.22         | (v2_struct_0 @ sk_E)
% 6.02/6.22         | (v2_struct_0 @ sk_A)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_B)
% 6.02/6.22         | (v2_struct_0 @ sk_A)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_E)
% 6.02/6.22         | (v2_struct_0 @ sk_B)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('sup+', [status(thm)], ['93', '119'])).
% 6.02/6.22  thf('121', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_B)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_A)
% 6.02/6.22         | (v2_struct_0 @ sk_E)
% 6.02/6.22         | (r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_G)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('simplify', [status(thm)], ['120'])).
% 6.02/6.22  thf('122', plain,
% 6.02/6.22      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 6.02/6.22           sk_H)
% 6.02/6.22        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 6.02/6.22        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('123', plain, (((sk_H) = (sk_G))),
% 6.02/6.22      inference('sup+', [status(thm)], ['3', '4'])).
% 6.02/6.22  thf('124', plain, (((sk_F) = (sk_G))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('125', plain,
% 6.02/6.22      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 6.02/6.22           sk_G)
% 6.02/6.22        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 6.02/6.22        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))),
% 6.02/6.22      inference('demod', [status(thm)], ['122', '123', '124'])).
% 6.02/6.22  thf('126', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_E)
% 6.02/6.22         | (v2_struct_0 @ sk_A)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_B)
% 6.02/6.22         | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 6.02/6.22         | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('sup-', [status(thm)], ['121', '125'])).
% 6.02/6.22  thf('127', plain,
% 6.02/6.22      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('demod', [status(thm)], ['49', '50'])).
% 6.02/6.22  thf('128', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_E)
% 6.02/6.22         | (v2_struct_0 @ sk_A)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_B)
% 6.02/6.22         | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('demod', [status(thm)], ['126', '127'])).
% 6.02/6.22  thf('129', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_E)
% 6.02/6.22         | (v2_struct_0 @ sk_A)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_B)
% 6.02/6.22         | (v2_struct_0 @ sk_B)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_A)
% 6.02/6.22         | (v2_struct_0 @ sk_E)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('sup-', [status(thm)], ['82', '128'])).
% 6.02/6.22  thf('130', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_B)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_A)
% 6.02/6.22         | (v2_struct_0 @ sk_E)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('simplify', [status(thm)], ['129'])).
% 6.02/6.22  thf('131', plain, (~ (v2_struct_0 @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('132', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('sup-', [status(thm)], ['130', '131'])).
% 6.02/6.22  thf('133', plain, (~ (v2_struct_0 @ sk_E)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('134', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('clc', [status(thm)], ['132', '133'])).
% 6.02/6.22  thf('135', plain, (~ (v2_struct_0 @ sk_B)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('136', plain,
% 6.02/6.22      (((v2_struct_0 @ sk_D)) <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('clc', [status(thm)], ['134', '135'])).
% 6.02/6.22  thf('137', plain, (~ (v2_struct_0 @ sk_D)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('138', plain, (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 6.02/6.22      inference('sup-', [status(thm)], ['136', '137'])).
% 6.02/6.22  thf('139', plain,
% 6.02/6.22      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 6.02/6.22         sk_H)) | 
% 6.02/6.22       ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 6.02/6.22      inference('split', [status(esa)], ['1'])).
% 6.02/6.22  thf('140', plain,
% 6.02/6.22      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 6.02/6.22         sk_H))),
% 6.02/6.22      inference('sat_resolution*', [status(thm)], ['138', '139'])).
% 6.02/6.22  thf('141', plain,
% 6.02/6.22      ((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 6.02/6.22        sk_G)),
% 6.02/6.22      inference('simpl_trail', [status(thm)], ['6', '140'])).
% 6.02/6.22  thf('142', plain,
% 6.02/6.22      ((((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 6.02/6.22          = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))
% 6.02/6.22        | (v2_struct_0 @ sk_B)
% 6.02/6.22        | (v2_struct_0 @ sk_D)
% 6.02/6.22        | (v2_struct_0 @ sk_A)
% 6.02/6.22        | (v2_struct_0 @ sk_E))),
% 6.02/6.22      inference('sup+', [status(thm)], ['30', '46'])).
% 6.02/6.22  thf('143', plain,
% 6.02/6.22      ((((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 6.02/6.22          = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C))
% 6.02/6.22        | (v2_struct_0 @ sk_B)
% 6.02/6.22        | (v2_struct_0 @ sk_D)
% 6.02/6.22        | (v2_struct_0 @ sk_A)
% 6.02/6.22        | (v2_struct_0 @ sk_E))),
% 6.02/6.22      inference('sup+', [status(thm)], ['85', '92'])).
% 6.02/6.22  thf('144', plain,
% 6.02/6.22      ((m1_subset_1 @ sk_C @ 
% 6.02/6.22        (k1_zfmisc_1 @ 
% 6.02/6.22         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('145', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('146', plain,
% 6.02/6.22      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i, 
% 6.02/6.22         X19 : $i]:
% 6.02/6.22         ((v2_struct_0 @ X12)
% 6.02/6.22          | ~ (v2_pre_topc @ X12)
% 6.02/6.22          | ~ (l1_pre_topc @ X12)
% 6.02/6.22          | (v2_struct_0 @ X13)
% 6.02/6.22          | ~ (m1_pre_topc @ X13 @ X14)
% 6.02/6.22          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 6.02/6.22          | ~ (m1_subset_1 @ X17 @ 
% 6.02/6.22               (u1_struct_0 @ (k1_tsep_1 @ X14 @ X16 @ X13)))
% 6.02/6.22          | ~ (r1_tmap_1 @ X16 @ X12 @ 
% 6.02/6.22               (k3_tmap_1 @ X14 @ X12 @ (k1_tsep_1 @ X14 @ X16 @ X13) @ X16 @ 
% 6.02/6.22                X18) @ 
% 6.02/6.22               X15)
% 6.02/6.22          | ~ (r1_tmap_1 @ X13 @ X12 @ 
% 6.02/6.22               (k3_tmap_1 @ X14 @ X12 @ (k1_tsep_1 @ X14 @ X16 @ X13) @ X13 @ 
% 6.02/6.22                X18) @ 
% 6.02/6.22               X19)
% 6.02/6.22          | (r1_tmap_1 @ (k1_tsep_1 @ X14 @ X16 @ X13) @ X12 @ X18 @ X17)
% 6.02/6.22          | ((X17) != (X19))
% 6.02/6.22          | ((X17) != (X15))
% 6.02/6.22          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X13))
% 6.02/6.22          | ~ (m1_subset_1 @ X18 @ 
% 6.02/6.22               (k1_zfmisc_1 @ 
% 6.02/6.22                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X14 @ X16 @ X13)) @ 
% 6.02/6.22                 (u1_struct_0 @ X12))))
% 6.02/6.22          | ~ (v1_funct_2 @ X18 @ 
% 6.02/6.22               (u1_struct_0 @ (k1_tsep_1 @ X14 @ X16 @ X13)) @ 
% 6.02/6.22               (u1_struct_0 @ X12))
% 6.02/6.22          | ~ (v1_funct_1 @ X18)
% 6.02/6.22          | ~ (m1_pre_topc @ X16 @ X14)
% 6.02/6.22          | (v2_struct_0 @ X16)
% 6.02/6.22          | ~ (l1_pre_topc @ X14)
% 6.02/6.22          | ~ (v2_pre_topc @ X14)
% 6.02/6.22          | (v2_struct_0 @ X14))),
% 6.02/6.22      inference('cnf', [status(esa)], [t123_tmap_1])).
% 6.02/6.22  thf('147', plain,
% 6.02/6.22      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 6.02/6.22         ((v2_struct_0 @ X14)
% 6.02/6.22          | ~ (v2_pre_topc @ X14)
% 6.02/6.22          | ~ (l1_pre_topc @ X14)
% 6.02/6.22          | (v2_struct_0 @ X16)
% 6.02/6.22          | ~ (m1_pre_topc @ X16 @ X14)
% 6.02/6.22          | ~ (v1_funct_1 @ X18)
% 6.02/6.22          | ~ (v1_funct_2 @ X18 @ 
% 6.02/6.22               (u1_struct_0 @ (k1_tsep_1 @ X14 @ X16 @ X13)) @ 
% 6.02/6.22               (u1_struct_0 @ X12))
% 6.02/6.22          | ~ (m1_subset_1 @ X18 @ 
% 6.02/6.22               (k1_zfmisc_1 @ 
% 6.02/6.22                (k2_zfmisc_1 @ (u1_struct_0 @ (k1_tsep_1 @ X14 @ X16 @ X13)) @ 
% 6.02/6.22                 (u1_struct_0 @ X12))))
% 6.02/6.22          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X13))
% 6.02/6.22          | (r1_tmap_1 @ (k1_tsep_1 @ X14 @ X16 @ X13) @ X12 @ X18 @ X19)
% 6.02/6.22          | ~ (r1_tmap_1 @ X13 @ X12 @ 
% 6.02/6.22               (k3_tmap_1 @ X14 @ X12 @ (k1_tsep_1 @ X14 @ X16 @ X13) @ X13 @ 
% 6.02/6.22                X18) @ 
% 6.02/6.22               X19)
% 6.02/6.22          | ~ (r1_tmap_1 @ X16 @ X12 @ 
% 6.02/6.22               (k3_tmap_1 @ X14 @ X12 @ (k1_tsep_1 @ X14 @ X16 @ X13) @ X16 @ 
% 6.02/6.22                X18) @ 
% 6.02/6.22               X19)
% 6.02/6.22          | ~ (m1_subset_1 @ X19 @ 
% 6.02/6.22               (u1_struct_0 @ (k1_tsep_1 @ X14 @ X16 @ X13)))
% 6.02/6.22          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X16))
% 6.02/6.22          | ~ (m1_pre_topc @ X13 @ X14)
% 6.02/6.22          | (v2_struct_0 @ X13)
% 6.02/6.22          | ~ (l1_pre_topc @ X12)
% 6.02/6.22          | ~ (v2_pre_topc @ X12)
% 6.02/6.22          | (v2_struct_0 @ X12))),
% 6.02/6.22      inference('simplify', [status(thm)], ['146'])).
% 6.02/6.22  thf('148', plain,
% 6.02/6.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.02/6.22         (~ (m1_subset_1 @ X1 @ 
% 6.02/6.22             (k1_zfmisc_1 @ 
% 6.02/6.22              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 6.02/6.22          | (v2_struct_0 @ X0)
% 6.02/6.22          | ~ (v2_pre_topc @ X0)
% 6.02/6.22          | ~ (l1_pre_topc @ X0)
% 6.02/6.22          | (v2_struct_0 @ sk_E)
% 6.02/6.22          | ~ (m1_pre_topc @ sk_E @ sk_A)
% 6.02/6.22          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 6.02/6.22          | ~ (m1_subset_1 @ X2 @ 
% 6.02/6.22               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)))
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_D @ X0 @ 
% 6.02/6.22               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 6.02/6.22                sk_D @ X1) @ 
% 6.02/6.22               X2)
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_E @ X0 @ 
% 6.02/6.22               (k3_tmap_1 @ sk_A @ X0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ 
% 6.02/6.22                sk_E @ X1) @ 
% 6.02/6.22               X2)
% 6.02/6.22          | (r1_tmap_1 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E) @ X0 @ X1 @ X2)
% 6.02/6.22          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_E))
% 6.02/6.22          | ~ (v1_funct_2 @ X1 @ 
% 6.02/6.22               (u1_struct_0 @ (k1_tsep_1 @ sk_A @ sk_D @ sk_E)) @ 
% 6.02/6.22               (u1_struct_0 @ X0))
% 6.02/6.22          | ~ (v1_funct_1 @ X1)
% 6.02/6.22          | ~ (m1_pre_topc @ sk_D @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | ~ (l1_pre_topc @ sk_A)
% 6.02/6.22          | ~ (v2_pre_topc @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_A))),
% 6.02/6.22      inference('sup-', [status(thm)], ['145', '147'])).
% 6.02/6.22  thf('149', plain, ((m1_pre_topc @ sk_E @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('150', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('151', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('152', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('153', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('154', plain, (((sk_A) = (k1_tsep_1 @ sk_A @ sk_D @ sk_E))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('155', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('156', plain, ((l1_pre_topc @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('157', plain, ((v2_pre_topc @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('158', plain,
% 6.02/6.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 6.02/6.22         (~ (m1_subset_1 @ X1 @ 
% 6.02/6.22             (k1_zfmisc_1 @ 
% 6.02/6.22              (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))))
% 6.02/6.22          | (v2_struct_0 @ X0)
% 6.02/6.22          | ~ (v2_pre_topc @ X0)
% 6.02/6.22          | ~ (l1_pre_topc @ X0)
% 6.02/6.22          | (v2_struct_0 @ sk_E)
% 6.02/6.22          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 6.02/6.22          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_D @ X0 @ 
% 6.02/6.22               (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_D @ X1) @ X2)
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_E @ X0 @ 
% 6.02/6.22               (k3_tmap_1 @ sk_A @ X0 @ sk_A @ sk_E @ X1) @ X2)
% 6.02/6.22          | (r1_tmap_1 @ sk_A @ X0 @ X1 @ X2)
% 6.02/6.22          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_E))
% 6.02/6.22          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 6.02/6.22          | ~ (v1_funct_1 @ X1)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | (v2_struct_0 @ sk_A))),
% 6.02/6.22      inference('demod', [status(thm)],
% 6.02/6.22                ['148', '149', '150', '151', '152', '153', '154', '155', 
% 6.02/6.22                 '156', '157'])).
% 6.02/6.22  thf('159', plain,
% 6.02/6.22      (![X0 : $i]:
% 6.02/6.22         ((v2_struct_0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | ~ (v1_funct_1 @ sk_C)
% 6.02/6.22          | ~ (v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 6.02/6.22          | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22               (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C) @ X0)
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22               (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ X0)
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 6.02/6.22          | (v2_struct_0 @ sk_E)
% 6.02/6.22          | ~ (l1_pre_topc @ sk_B)
% 6.02/6.22          | ~ (v2_pre_topc @ sk_B)
% 6.02/6.22          | (v2_struct_0 @ sk_B))),
% 6.02/6.22      inference('sup-', [status(thm)], ['144', '158'])).
% 6.02/6.22  thf('160', plain, ((v1_funct_1 @ sk_C)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('161', plain,
% 6.02/6.22      ((v1_funct_2 @ sk_C @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('162', plain, ((l1_pre_topc @ sk_B)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('163', plain, ((v2_pre_topc @ sk_B)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('164', plain,
% 6.02/6.22      (![X0 : $i]:
% 6.02/6.22         ((v2_struct_0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 6.02/6.22          | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22               (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_E @ sk_C) @ X0)
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22               (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ X0)
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 6.02/6.22          | (v2_struct_0 @ sk_E)
% 6.02/6.22          | (v2_struct_0 @ sk_B))),
% 6.02/6.22      inference('demod', [status(thm)], ['159', '160', '161', '162', '163'])).
% 6.02/6.22  thf('165', plain,
% 6.02/6.22      (![X0 : $i]:
% 6.02/6.22         (~ (r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ X0)
% 6.02/6.22          | (v2_struct_0 @ sk_E)
% 6.02/6.22          | (v2_struct_0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | (v2_struct_0 @ sk_B)
% 6.02/6.22          | (v2_struct_0 @ sk_B)
% 6.02/6.22          | (v2_struct_0 @ sk_E)
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22               (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ X0)
% 6.02/6.22          | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | (v2_struct_0 @ sk_A))),
% 6.02/6.22      inference('sup-', [status(thm)], ['143', '164'])).
% 6.02/6.22  thf('166', plain,
% 6.02/6.22      (![X0 : $i]:
% 6.02/6.22         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 6.02/6.22          | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22               (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ X0)
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 6.02/6.22          | (v2_struct_0 @ sk_B)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | (v2_struct_0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_E)
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ X0))),
% 6.02/6.22      inference('simplify', [status(thm)], ['165'])).
% 6.02/6.22  thf('167', plain,
% 6.02/6.22      (![X0 : $i]:
% 6.02/6.22         (~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 6.02/6.22          | (v2_struct_0 @ sk_E)
% 6.02/6.22          | (v2_struct_0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | (v2_struct_0 @ sk_B)
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ X0)
% 6.02/6.22          | (v2_struct_0 @ sk_E)
% 6.02/6.22          | (v2_struct_0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | (v2_struct_0 @ sk_B)
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.02/6.22          | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E)))),
% 6.02/6.22      inference('sup-', [status(thm)], ['142', '166'])).
% 6.02/6.22  thf('168', plain,
% 6.02/6.22      (![X0 : $i]:
% 6.02/6.22         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 6.02/6.22          | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ X0)
% 6.02/6.22          | (v2_struct_0 @ sk_B)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | (v2_struct_0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_E)
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0))),
% 6.02/6.22      inference('simplify', [status(thm)], ['167'])).
% 6.02/6.22  thf('169', plain,
% 6.02/6.22      ((~ (r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 6.02/6.22           sk_G)
% 6.02/6.22        | (v2_struct_0 @ sk_E)
% 6.02/6.22        | (v2_struct_0 @ sk_A)
% 6.02/6.22        | (v2_struct_0 @ sk_D)
% 6.02/6.22        | (v2_struct_0 @ sk_B)
% 6.02/6.22        | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 6.02/6.22        | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))
% 6.02/6.22        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 6.02/6.22        | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E)))),
% 6.02/6.22      inference('sup-', [status(thm)], ['141', '168'])).
% 6.02/6.22  thf('170', plain,
% 6.02/6.22      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 6.02/6.22         sk_G))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)))),
% 6.02/6.22      inference('split', [status(esa)], ['48'])).
% 6.02/6.22  thf('171', plain,
% 6.02/6.22      ((((k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D)
% 6.02/6.22          = (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C))
% 6.02/6.22        | (v2_struct_0 @ sk_B)
% 6.02/6.22        | (v2_struct_0 @ sk_D)
% 6.02/6.22        | (v2_struct_0 @ sk_A)
% 6.02/6.22        | (v2_struct_0 @ sk_E))),
% 6.02/6.22      inference('sup+', [status(thm)], ['30', '46'])).
% 6.02/6.22  thf('172', plain,
% 6.02/6.22      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 6.02/6.22         sk_G)
% 6.02/6.22        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('173', plain, (((sk_F) = (sk_G))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('174', plain,
% 6.02/6.22      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 6.02/6.22         sk_G)
% 6.02/6.22        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))),
% 6.02/6.22      inference('demod', [status(thm)], ['172', '173'])).
% 6.02/6.22  thf('175', plain,
% 6.02/6.22      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 6.02/6.22      inference('split', [status(esa)], ['174'])).
% 6.02/6.22  thf('176', plain,
% 6.02/6.22      (![X0 : $i]:
% 6.02/6.22         ((v2_struct_0 @ sk_A)
% 6.02/6.22          | (v2_struct_0 @ sk_D)
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_E))
% 6.02/6.22          | (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22             (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ X0)
% 6.02/6.22          | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ X0)
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 6.02/6.22          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 6.02/6.22          | (v2_struct_0 @ sk_E)
% 6.02/6.22          | (v2_struct_0 @ sk_B))),
% 6.02/6.22      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 6.02/6.22  thf('177', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_B)
% 6.02/6.22         | (v2_struct_0 @ sk_E)
% 6.02/6.22         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))
% 6.02/6.22         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))
% 6.02/6.22         | (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_G)
% 6.02/6.22         | ~ (m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_A)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 6.02/6.22      inference('sup-', [status(thm)], ['175', '176'])).
% 6.02/6.22  thf('178', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('179', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 6.02/6.22      inference('demod', [status(thm)], ['74', '75'])).
% 6.02/6.22  thf('180', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))),
% 6.02/6.22      inference('demod', [status(thm)], ['77', '78'])).
% 6.02/6.22  thf('181', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_B)
% 6.02/6.22         | (v2_struct_0 @ sk_E)
% 6.02/6.22         | (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22            (k3_tmap_1 @ sk_A @ sk_B @ sk_A @ sk_D @ sk_C) @ sk_G)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_A)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 6.02/6.22      inference('demod', [status(thm)], ['177', '178', '179', '180'])).
% 6.02/6.22  thf('182', plain,
% 6.02/6.22      ((((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 6.02/6.22          sk_G)
% 6.02/6.22         | (v2_struct_0 @ sk_E)
% 6.02/6.22         | (v2_struct_0 @ sk_A)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_B)
% 6.02/6.22         | (v2_struct_0 @ sk_A)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_E)
% 6.02/6.22         | (v2_struct_0 @ sk_B)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 6.02/6.22      inference('sup+', [status(thm)], ['171', '181'])).
% 6.02/6.22  thf('183', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_B)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_A)
% 6.02/6.22         | (v2_struct_0 @ sk_E)
% 6.02/6.22         | (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 6.02/6.22      inference('simplify', [status(thm)], ['182'])).
% 6.02/6.22  thf('184', plain,
% 6.02/6.22      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 6.02/6.22         sk_G))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 6.02/6.22      inference('demod', [status(thm)], ['2', '5'])).
% 6.02/6.22  thf('185', plain,
% 6.02/6.22      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 6.02/6.22           sk_G)
% 6.02/6.22        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 6.02/6.22        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))),
% 6.02/6.22      inference('demod', [status(thm)], ['122', '123', '124'])).
% 6.02/6.22  thf('186', plain,
% 6.02/6.22      (((~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)
% 6.02/6.22         | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22              (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 6.02/6.22      inference('sup-', [status(thm)], ['184', '185'])).
% 6.02/6.22  thf('187', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_E)
% 6.02/6.22         | (v2_struct_0 @ sk_A)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_B)
% 6.02/6.22         | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 6.02/6.22             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 6.02/6.22      inference('sup-', [status(thm)], ['183', '186'])).
% 6.02/6.22  thf('188', plain,
% 6.02/6.22      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 6.02/6.22      inference('split', [status(esa)], ['174'])).
% 6.02/6.22  thf('189', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_E)
% 6.02/6.22         | (v2_struct_0 @ sk_A)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_B)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 6.02/6.22             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 6.02/6.22      inference('demod', [status(thm)], ['187', '188'])).
% 6.02/6.22  thf('190', plain, (~ (v2_struct_0 @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('191', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 6.02/6.22             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 6.02/6.22      inference('sup-', [status(thm)], ['189', '190'])).
% 6.02/6.22  thf('192', plain, (~ (v2_struct_0 @ sk_B)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('193', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 6.02/6.22             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 6.02/6.22      inference('clc', [status(thm)], ['191', '192'])).
% 6.02/6.22  thf('194', plain, (~ (v2_struct_0 @ sk_E)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('195', plain,
% 6.02/6.22      (((v2_struct_0 @ sk_D))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 6.02/6.22             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 6.02/6.22      inference('clc', [status(thm)], ['193', '194'])).
% 6.02/6.22  thf('196', plain, (~ (v2_struct_0 @ sk_D)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('197', plain,
% 6.02/6.22      (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)) | 
% 6.02/6.22       ~
% 6.02/6.22       ((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 6.02/6.22         sk_H))),
% 6.02/6.22      inference('sup-', [status(thm)], ['195', '196'])).
% 6.02/6.22  thf('198', plain,
% 6.02/6.22      (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)))),
% 6.02/6.22      inference('split', [status(esa)], ['174'])).
% 6.02/6.22  thf('199', plain,
% 6.02/6.22      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 6.02/6.22           sk_H)
% 6.02/6.22        | ~ (r1_tmap_1 @ sk_D @ sk_B @ 
% 6.02/6.22             (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_G)
% 6.02/6.22        | ~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('200', plain,
% 6.02/6.22      ((~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))
% 6.02/6.22         <= (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('split', [status(esa)], ['199'])).
% 6.02/6.22  thf('201', plain, (((sk_F) = (sk_G))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('202', plain,
% 6.02/6.22      ((~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 6.02/6.22         <= (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('demod', [status(thm)], ['200', '201'])).
% 6.02/6.22  thf('203', plain,
% 6.02/6.22      (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)) | 
% 6.02/6.22       ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 6.02/6.22      inference('sup-', [status(thm)], ['198', '202'])).
% 6.02/6.22  thf('204', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_B)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_A)
% 6.02/6.22         | (v2_struct_0 @ sk_E)
% 6.02/6.22         | (r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22            (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_G)))
% 6.02/6.22         <= (((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('simplify', [status(thm)], ['120'])).
% 6.02/6.22  thf('205', plain,
% 6.02/6.22      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 6.02/6.22           sk_H))
% 6.02/6.22         <= (~
% 6.02/6.22             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 6.02/6.22      inference('split', [status(esa)], ['199'])).
% 6.02/6.22  thf('206', plain, (((sk_H) = (sk_G))),
% 6.02/6.22      inference('sup+', [status(thm)], ['3', '4'])).
% 6.02/6.22  thf('207', plain,
% 6.02/6.22      ((~ (r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 6.02/6.22           sk_G))
% 6.02/6.22         <= (~
% 6.02/6.22             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)))),
% 6.02/6.22      inference('demod', [status(thm)], ['205', '206'])).
% 6.02/6.22  thf('208', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_E)
% 6.02/6.22         | (v2_struct_0 @ sk_A)
% 6.02/6.22         | (v2_struct_0 @ sk_D)
% 6.02/6.22         | (v2_struct_0 @ sk_B)))
% 6.02/6.22         <= (~
% 6.02/6.22             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 6.02/6.22             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('sup-', [status(thm)], ['204', '207'])).
% 6.02/6.22  thf('209', plain, (~ (v2_struct_0 @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('210', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_E)))
% 6.02/6.22         <= (~
% 6.02/6.22             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 6.02/6.22             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('sup-', [status(thm)], ['208', '209'])).
% 6.02/6.22  thf('211', plain, (~ (v2_struct_0 @ sk_B)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('212', plain,
% 6.02/6.22      ((((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D)))
% 6.02/6.22         <= (~
% 6.02/6.22             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 6.02/6.22             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('clc', [status(thm)], ['210', '211'])).
% 6.02/6.22  thf('213', plain, (~ (v2_struct_0 @ sk_E)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('214', plain,
% 6.02/6.22      (((v2_struct_0 @ sk_D))
% 6.02/6.22         <= (~
% 6.02/6.22             ((r1_tmap_1 @ sk_E @ sk_B @ 
% 6.02/6.22               (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_H)) & 
% 6.02/6.22             ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('clc', [status(thm)], ['212', '213'])).
% 6.02/6.22  thf('215', plain, (~ (v2_struct_0 @ sk_D)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('216', plain,
% 6.02/6.22      (((r1_tmap_1 @ sk_E @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 6.02/6.22         sk_H)) | 
% 6.02/6.22       ~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 6.02/6.22      inference('sup-', [status(thm)], ['214', '215'])).
% 6.02/6.22  thf('217', plain,
% 6.02/6.22      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 6.02/6.22         sk_G)) | 
% 6.02/6.22       ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))),
% 6.02/6.22      inference('split', [status(esa)], ['174'])).
% 6.02/6.22  thf('218', plain,
% 6.02/6.22      (((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 6.02/6.22         sk_G))),
% 6.02/6.22      inference('sat_resolution*', [status(thm)], ['197', '203', '216', '217'])).
% 6.02/6.22  thf('219', plain,
% 6.02/6.22      ((r1_tmap_1 @ sk_D @ sk_B @ (k2_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 6.02/6.22        sk_G)),
% 6.02/6.22      inference('simpl_trail', [status(thm)], ['170', '218'])).
% 6.02/6.22  thf('220', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_D))),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('221', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_A))),
% 6.02/6.22      inference('demod', [status(thm)], ['74', '75'])).
% 6.02/6.22  thf('222', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_E))),
% 6.02/6.22      inference('demod', [status(thm)], ['77', '78'])).
% 6.02/6.22  thf('223', plain,
% 6.02/6.22      (((v2_struct_0 @ sk_E)
% 6.02/6.22        | (v2_struct_0 @ sk_A)
% 6.02/6.22        | (v2_struct_0 @ sk_D)
% 6.02/6.22        | (v2_struct_0 @ sk_B)
% 6.02/6.22        | (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))),
% 6.02/6.22      inference('demod', [status(thm)], ['169', '219', '220', '221', '222'])).
% 6.02/6.22  thf('224', plain,
% 6.02/6.22      ((~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G))
% 6.02/6.22         <= (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F)))),
% 6.02/6.22      inference('demod', [status(thm)], ['200', '201'])).
% 6.02/6.22  thf('225', plain, (~ ((r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_F))),
% 6.02/6.22      inference('sat_resolution*', [status(thm)], ['138'])).
% 6.02/6.22  thf('226', plain, (~ (r1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_G)),
% 6.02/6.22      inference('simpl_trail', [status(thm)], ['224', '225'])).
% 6.02/6.22  thf('227', plain,
% 6.02/6.22      (((v2_struct_0 @ sk_B)
% 6.02/6.22        | (v2_struct_0 @ sk_D)
% 6.02/6.22        | (v2_struct_0 @ sk_A)
% 6.02/6.22        | (v2_struct_0 @ sk_E))),
% 6.02/6.22      inference('sup-', [status(thm)], ['223', '226'])).
% 6.02/6.22  thf('228', plain, (~ (v2_struct_0 @ sk_A)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('229', plain,
% 6.02/6.22      (((v2_struct_0 @ sk_E) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 6.02/6.22      inference('sup-', [status(thm)], ['227', '228'])).
% 6.02/6.22  thf('230', plain, (~ (v2_struct_0 @ sk_E)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('231', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_D))),
% 6.02/6.22      inference('clc', [status(thm)], ['229', '230'])).
% 6.02/6.22  thf('232', plain, (~ (v2_struct_0 @ sk_B)),
% 6.02/6.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.02/6.22  thf('233', plain, ((v2_struct_0 @ sk_D)),
% 6.02/6.22      inference('clc', [status(thm)], ['231', '232'])).
% 6.02/6.22  thf('234', plain, ($false), inference('demod', [status(thm)], ['0', '233'])).
% 6.02/6.22  
% 6.02/6.22  % SZS output end Refutation
% 6.02/6.22  
% 6.02/6.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
