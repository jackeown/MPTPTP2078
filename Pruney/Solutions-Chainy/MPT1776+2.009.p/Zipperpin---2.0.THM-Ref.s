%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N0t6oCtPDa

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:24 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 791 expanded)
%              Number of leaves         :   31 ( 236 expanded)
%              Depth                    :   28
%              Number of atoms          : 2142 (31441 expanded)
%              Number of equality atoms :   28 ( 438 expanded)
%              Maximal formula depth    :   26 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_F_type,type,(
    sk_F: $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t87_tmap_1,conjecture,(
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
                & ( m1_pre_topc @ C @ B ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) )
                     => ( ( ( v1_tsep_1 @ C @ B )
                          & ( m1_pre_topc @ C @ B )
                          & ( m1_pre_topc @ C @ D ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( F = G )
                                 => ( ( r1_tmap_1 @ D @ A @ E @ F )
                                  <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) )).

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
                  & ( m1_pre_topc @ C @ B ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( m1_pre_topc @ D @ B ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) )
                       => ( ( ( v1_tsep_1 @ C @ B )
                            & ( m1_pre_topc @ C @ B )
                            & ( m1_pre_topc @ C @ D ) )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                                 => ( ( F = G )
                                   => ( ( r1_tmap_1 @ D @ A @ E @ F )
                                    <=> ( r1_tmap_1 @ C @ A @ ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['17'])).

thf('19',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','28'])).

thf('30',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf('34',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
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

thf('36',plain,(
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

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('40',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('46',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','43','48','49','50','51','52'])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['34','53'])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['4'])).

thf('66',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_tmap_1,axiom,(
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
                    & ( v1_tsep_1 @ D @ B )
                    & ( m1_pre_topc @ D @ B ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                         => ( ( E = F )
                           => ( ( r1_tmap_1 @ B @ A @ C @ E )
                            <=> ( r1_tmap_1 @ D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) )).

thf('70',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( v1_tsep_1 @ X19 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r1_tmap_1 @ X19 @ X21 @ ( k2_tmap_1 @ X18 @ X21 @ X22 @ X19 ) @ X20 )
      | ( r1_tmap_1 @ X18 @ X21 @ X22 @ X23 )
      | ( X23 != X20 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('71',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ( r1_tmap_1 @ X18 @ X21 @ X22 @ X20 )
      | ~ ( r1_tmap_1 @ X19 @ X21 @ ( k2_tmap_1 @ X18 @ X21 @ X22 @ X19 ) @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( v1_tsep_1 @ X19 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['69','71'])).

thf('73',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('74',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['46','47'])).

thf('75',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['72','73','74','75','76','77','78'])).

thf('80',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( v1_tsep_1 @ sk_C @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['68','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('83',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('86',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_pre_topc @ X16 @ X17 )
      | ( r1_tarski @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_pre_topc @ X17 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('87',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['46','47'])).

thf('89',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['87','88'])).

thf(t19_tsep_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( ( v1_tsep_1 @ B @ A )
            & ( m1_pre_topc @ B @ A ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( m1_pre_topc @ C @ A ) )
             => ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) )
               => ( ( v1_tsep_1 @ B @ C )
                  & ( m1_pre_topc @ B @ C ) ) ) ) ) ) )).

thf('90',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_tsep_1 @ X13 @ X14 )
      | ~ ( m1_pre_topc @ X13 @ X14 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) )
      | ( v1_tsep_1 @ X13 @ X15 )
      | ~ ( m1_pre_topc @ X15 @ X14 )
      | ( v2_struct_0 @ X15 )
      | ~ ( l1_pre_topc @ X14 )
      | ~ ( v2_pre_topc @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t19_tsep_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v1_tsep_1 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_tsep_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ sk_B )
    | ~ ( m1_pre_topc @ sk_C @ sk_B )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['84','91'])).

thf('93',plain,(
    v1_tsep_1 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['92','93','94','95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_tsep_1 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['80','81','82','83','101'])).

thf('103',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['10'])).

thf('104',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
      & ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['8'])).

thf('112',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ),
    inference('sat_resolution*',[status(thm)],['14','18','110','111'])).

thf('113',plain,(
    r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ),
    inference(simpl_trail,[status(thm)],['5','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ~ ( l1_pre_topc @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( v1_tsep_1 @ X19 @ X18 )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r1_tmap_1 @ X18 @ X21 @ X22 @ X23 )
      | ( r1_tmap_1 @ X19 @ X21 @ ( k2_tmap_1 @ X18 @ X21 @ X22 @ X19 ) @ X20 )
      | ( X23 != X20 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('116',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X18 ) @ ( u1_struct_0 @ X21 ) ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ( r1_tmap_1 @ X19 @ X21 @ ( k2_tmap_1 @ X18 @ X21 @ X22 @ X19 ) @ X20 )
      | ~ ( r1_tmap_1 @ X18 @ X21 @ X22 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_pre_topc @ X19 @ X18 )
      | ~ ( v1_tsep_1 @ X19 @ X18 )
      | ( v2_struct_0 @ X19 )
      | ~ ( l1_pre_topc @ X18 )
      | ~ ( v2_pre_topc @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['114','116'])).

thf('118',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('119',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['46','47'])).

thf('120',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_tsep_1 @ X0 @ sk_D )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['117','118','119','120','121','122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v1_tsep_1 @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['113','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_F )
      | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( v1_tsep_1 @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v1_tsep_1 @ sk_C @ sk_D )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_F )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['3','127'])).

thf('129',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['99','100'])).

thf('130',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_F )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('133',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('134',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('136',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(split,[status(esa)],['17'])).

thf('137',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sat_resolution*',[status(thm)],['14','18','110','137'])).

thf('139',plain,(
    ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['134','138'])).

thf('140',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['131','139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['142','143'])).

thf('145',plain,(
    $false ),
    inference(demod,[status(thm)],['0','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N0t6oCtPDa
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 79 iterations in 0.033s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.49  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(sk_G_type, type, sk_G: $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.21/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.21/0.49  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.21/0.49  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.21/0.49  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.21/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.49  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.21/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(t87_tmap_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.49             ( l1_pre_topc @ B ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.49                   ( ![E:$i]:
% 0.21/0.49                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.49                         ( v1_funct_2 @
% 0.21/0.49                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.49                         ( m1_subset_1 @
% 0.21/0.49                           E @ 
% 0.21/0.49                           ( k1_zfmisc_1 @
% 0.21/0.49                             ( k2_zfmisc_1 @
% 0.21/0.49                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.49                       ( ( ( v1_tsep_1 @ C @ B ) & ( m1_pre_topc @ C @ B ) & 
% 0.21/0.49                           ( m1_pre_topc @ C @ D ) ) =>
% 0.21/0.49                         ( ![F:$i]:
% 0.21/0.49                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.49                             ( ![G:$i]:
% 0.21/0.49                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.49                                 ( ( ( F ) = ( G ) ) =>
% 0.21/0.49                                   ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.21/0.49                                     ( r1_tmap_1 @
% 0.21/0.49                                       C @ A @ 
% 0.21/0.49                                       ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.21/0.49            ( l1_pre_topc @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.49                ( l1_pre_topc @ B ) ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.21/0.49                  ( ![D:$i]:
% 0.21/0.49                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.49                      ( ![E:$i]:
% 0.21/0.49                        ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.49                            ( v1_funct_2 @
% 0.21/0.49                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.49                            ( m1_subset_1 @
% 0.21/0.49                              E @ 
% 0.21/0.49                              ( k1_zfmisc_1 @
% 0.21/0.49                                ( k2_zfmisc_1 @
% 0.21/0.49                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.49                          ( ( ( v1_tsep_1 @ C @ B ) & 
% 0.21/0.49                              ( m1_pre_topc @ C @ B ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.21/0.49                            ( ![F:$i]:
% 0.21/0.49                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.49                                ( ![G:$i]:
% 0.21/0.49                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.49                                    ( ( ( F ) = ( G ) ) =>
% 0.21/0.49                                      ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.21/0.49                                        ( r1_tmap_1 @
% 0.21/0.49                                          C @ A @ 
% 0.21/0.49                                          ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t87_tmap_1])).
% 0.21/0.49  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('2', plain, (((sk_F) = (sk_G))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('3', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.21/0.49        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.21/0.49         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.21/0.49      inference('split', [status(esa)], ['4'])).
% 0.21/0.49  thf('6', plain,
% 0.21/0.49      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.21/0.49        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('7', plain, (((sk_F) = (sk_G))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('8', plain,
% 0.21/0.49      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.21/0.49        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.21/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.21/0.49         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)))),
% 0.21/0.49      inference('split', [status(esa)], ['8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.21/0.49        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.21/0.49         <= (~
% 0.21/0.49             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.49      inference('split', [status(esa)], ['10'])).
% 0.21/0.49  thf('12', plain, (((sk_F) = (sk_G))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('13', plain,
% 0.21/0.49      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.21/0.49         <= (~
% 0.21/0.49             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      (~
% 0.21/0.49       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)) | 
% 0.21/0.49       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.21/0.49      inference('sup-', [status(thm)], ['9', '13'])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.21/0.49        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('16', plain, (((sk_F) = (sk_G))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)
% 0.21/0.49        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.21/0.49      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      (~
% 0.21/0.49       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)) | 
% 0.21/0.49       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.21/0.49      inference('split', [status(esa)], ['17'])).
% 0.21/0.49  thf('19', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('20', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ 
% 0.21/0.49        (k1_zfmisc_1 @ 
% 0.21/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d5_tmap_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.49             ( l1_pre_topc @ B ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_pre_topc @ C @ A ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( m1_pre_topc @ D @ A ) =>
% 0.21/0.49                   ( ![E:$i]:
% 0.21/0.49                     ( ( ( v1_funct_1 @ E ) & 
% 0.21/0.49                         ( v1_funct_2 @
% 0.21/0.49                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.49                         ( m1_subset_1 @
% 0.21/0.49                           E @ 
% 0.21/0.49                           ( k1_zfmisc_1 @
% 0.21/0.49                             ( k2_zfmisc_1 @
% 0.21/0.49                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.49                       ( ( m1_pre_topc @ D @ C ) =>
% 0.21/0.49                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.21/0.49                           ( k2_partfun1 @
% 0.21/0.49                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.21/0.49                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('22', plain,
% 0.21/0.49      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X8)
% 0.21/0.49          | ~ (v2_pre_topc @ X8)
% 0.21/0.49          | ~ (l1_pre_topc @ X8)
% 0.21/0.49          | ~ (m1_pre_topc @ X9 @ X10)
% 0.21/0.49          | ~ (m1_pre_topc @ X9 @ X11)
% 0.21/0.49          | ((k3_tmap_1 @ X10 @ X8 @ X11 @ X9 @ X12)
% 0.21/0.49              = (k2_partfun1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8) @ 
% 0.21/0.49                 X12 @ (u1_struct_0 @ X9)))
% 0.21/0.49          | ~ (m1_subset_1 @ X12 @ 
% 0.21/0.49               (k1_zfmisc_1 @ 
% 0.21/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))))
% 0.21/0.49          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))
% 0.21/0.49          | ~ (v1_funct_1 @ X12)
% 0.21/0.49          | ~ (m1_pre_topc @ X11 @ X10)
% 0.21/0.49          | ~ (l1_pre_topc @ X10)
% 0.21/0.49          | ~ (v2_pre_topc @ X10)
% 0.21/0.49          | (v2_struct_0 @ X10))),
% 0.21/0.49      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.21/0.49  thf('23', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X0)
% 0.21/0.49          | ~ (v2_pre_topc @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ X0)
% 0.21/0.49          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.21/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49                 sk_E @ (u1_struct_0 @ X1)))
% 0.21/0.49          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.49          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49          | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.49  thf('24', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('27', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('28', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X0)
% 0.21/0.49          | ~ (v2_pre_topc @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ X0)
% 0.21/0.49          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.49          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.21/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49                 sk_E @ (u1_struct_0 @ X1)))
% 0.21/0.49          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.21/0.49          | ~ (m1_pre_topc @ X1 @ X0)
% 0.21/0.49          | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.21/0.49  thf('29', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.49          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.21/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49                 sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.49          | ~ (l1_pre_topc @ sk_B)
% 0.21/0.49          | ~ (v2_pre_topc @ sk_B)
% 0.21/0.49          | (v2_struct_0 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '28'])).
% 0.21/0.49  thf('30', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('31', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('32', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.49          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.21/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49                 sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.49          | (v2_struct_0 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_B)
% 0.21/0.49        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.21/0.49            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49               sk_E @ (u1_struct_0 @ sk_C)))
% 0.21/0.49        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['19', '32'])).
% 0.21/0.49  thf('34', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ 
% 0.21/0.49        (k1_zfmisc_1 @ 
% 0.21/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(d4_tmap_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.49             ( l1_pre_topc @ B ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.49                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.21/0.49                 ( m1_subset_1 @
% 0.21/0.49                   C @ 
% 0.21/0.49                   ( k1_zfmisc_1 @
% 0.21/0.49                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( m1_pre_topc @ D @ A ) =>
% 0.21/0.49                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.21/0.49                     ( k2_partfun1 @
% 0.21/0.49                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.21/0.49                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('36', plain,
% 0.21/0.49      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X4)
% 0.21/0.49          | ~ (v2_pre_topc @ X4)
% 0.21/0.49          | ~ (l1_pre_topc @ X4)
% 0.21/0.49          | ~ (m1_pre_topc @ X5 @ X6)
% 0.21/0.49          | ((k2_tmap_1 @ X6 @ X4 @ X7 @ X5)
% 0.21/0.49              = (k2_partfun1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4) @ X7 @ 
% 0.21/0.49                 (u1_struct_0 @ X5)))
% 0.21/0.49          | ~ (m1_subset_1 @ X7 @ 
% 0.21/0.49               (k1_zfmisc_1 @ 
% 0.21/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.21/0.49          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.21/0.49          | ~ (v1_funct_1 @ X7)
% 0.21/0.49          | ~ (l1_pre_topc @ X6)
% 0.21/0.49          | ~ (v2_pre_topc @ X6)
% 0.21/0.49          | (v2_struct_0 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_D)
% 0.21/0.49          | ~ (v2_pre_topc @ sk_D)
% 0.21/0.49          | ~ (l1_pre_topc @ sk_D)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.21/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49                 sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49          | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.49  thf('38', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(cc1_pre_topc, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X0 @ X1)
% 0.21/0.49          | (v2_pre_topc @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ X1)
% 0.21/0.49          | ~ (v2_pre_topc @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.21/0.49  thf('40', plain,
% 0.21/0.49      ((~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B) | (v2_pre_topc @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.49  thf('41', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('42', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('43', plain, ((v2_pre_topc @ sk_D)),
% 0.21/0.49      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.49  thf('44', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(dt_m1_pre_topc, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.21/0.49  thf('46', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.49  thf('47', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('48', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.49      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.49  thf('49', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('51', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('52', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_D)
% 0.21/0.49          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.21/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49                 sk_E @ (u1_struct_0 @ X0)))
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.49          | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)],
% 0.21/0.49                ['37', '43', '48', '49', '50', '51', '52'])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.21/0.49            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49               sk_E @ (u1_struct_0 @ sk_C)))
% 0.21/0.49        | (v2_struct_0 @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['34', '53'])).
% 0.21/0.49  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_D)
% 0.21/0.49        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.21/0.49            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.21/0.49               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.21/0.49      inference('clc', [status(thm)], ['54', '55'])).
% 0.21/0.49  thf('57', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      (((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.21/0.49         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_E @ 
% 0.21/0.49            (u1_struct_0 @ sk_C)))),
% 0.21/0.49      inference('clc', [status(thm)], ['56', '57'])).
% 0.21/0.49  thf('59', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_B)
% 0.21/0.49        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.21/0.49            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['33', '58', '59'])).
% 0.21/0.49  thf('61', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A)
% 0.21/0.49        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.21/0.49            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)))),
% 0.21/0.49      inference('clc', [status(thm)], ['60', '61'])).
% 0.21/0.49  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.21/0.49         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))),
% 0.21/0.49      inference('clc', [status(thm)], ['62', '63'])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.21/0.49         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.49      inference('split', [status(esa)], ['4'])).
% 0.21/0.49  thf('66', plain, (((sk_F) = (sk_G))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('67', plain,
% 0.21/0.49      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.21/0.49         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.49      inference('demod', [status(thm)], ['65', '66'])).
% 0.21/0.49  thf('68', plain,
% 0.21/0.49      (((r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.21/0.49         sk_F))
% 0.21/0.49         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['64', '67'])).
% 0.21/0.49  thf('69', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ 
% 0.21/0.49        (k1_zfmisc_1 @ 
% 0.21/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t67_tmap_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.21/0.49             ( l1_pre_topc @ B ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.49                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.49                 ( m1_subset_1 @
% 0.21/0.49                   C @ 
% 0.21/0.49                   ( k1_zfmisc_1 @
% 0.21/0.49                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.21/0.49               ( ![D:$i]:
% 0.21/0.49                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.21/0.49                     ( m1_pre_topc @ D @ B ) ) =>
% 0.21/0.49                   ( ![E:$i]:
% 0.21/0.49                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.49                       ( ![F:$i]:
% 0.21/0.49                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.21/0.49                           ( ( ( E ) = ( F ) ) =>
% 0.21/0.49                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.21/0.49                               ( r1_tmap_1 @
% 0.21/0.49                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X18)
% 0.21/0.49          | ~ (v2_pre_topc @ X18)
% 0.21/0.49          | ~ (l1_pre_topc @ X18)
% 0.21/0.49          | (v2_struct_0 @ X19)
% 0.21/0.49          | ~ (v1_tsep_1 @ X19 @ X18)
% 0.21/0.49          | ~ (m1_pre_topc @ X19 @ X18)
% 0.21/0.49          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.21/0.49          | ~ (r1_tmap_1 @ X19 @ X21 @ (k2_tmap_1 @ X18 @ X21 @ X22 @ X19) @ 
% 0.21/0.49               X20)
% 0.21/0.49          | (r1_tmap_1 @ X18 @ X21 @ X22 @ X23)
% 0.21/0.49          | ((X23) != (X20))
% 0.21/0.49          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X18))
% 0.21/0.49          | ~ (m1_subset_1 @ X22 @ 
% 0.21/0.49               (k1_zfmisc_1 @ 
% 0.21/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X21))))
% 0.21/0.49          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X21))
% 0.21/0.49          | ~ (v1_funct_1 @ X22)
% 0.21/0.49          | ~ (l1_pre_topc @ X21)
% 0.21/0.49          | ~ (v2_pre_topc @ X21)
% 0.21/0.49          | (v2_struct_0 @ X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [t67_tmap_1])).
% 0.21/0.49  thf('71', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X21)
% 0.21/0.49          | ~ (v2_pre_topc @ X21)
% 0.21/0.49          | ~ (l1_pre_topc @ X21)
% 0.21/0.49          | ~ (v1_funct_1 @ X22)
% 0.21/0.49          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X21))
% 0.21/0.49          | ~ (m1_subset_1 @ X22 @ 
% 0.21/0.49               (k1_zfmisc_1 @ 
% 0.21/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X21))))
% 0.21/0.49          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.21/0.49          | (r1_tmap_1 @ X18 @ X21 @ X22 @ X20)
% 0.21/0.49          | ~ (r1_tmap_1 @ X19 @ X21 @ (k2_tmap_1 @ X18 @ X21 @ X22 @ X19) @ 
% 0.21/0.49               X20)
% 0.21/0.49          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.21/0.49          | ~ (m1_pre_topc @ X19 @ X18)
% 0.21/0.49          | ~ (v1_tsep_1 @ X19 @ X18)
% 0.21/0.49          | (v2_struct_0 @ X19)
% 0.21/0.49          | ~ (l1_pre_topc @ X18)
% 0.21/0.49          | ~ (v2_pre_topc @ X18)
% 0.21/0.49          | (v2_struct_0 @ X18))),
% 0.21/0.49      inference('simplify', [status(thm)], ['70'])).
% 0.21/0.49  thf('72', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_D)
% 0.21/0.49          | ~ (v2_pre_topc @ sk_D)
% 0.21/0.49          | ~ (l1_pre_topc @ sk_D)
% 0.21/0.49          | (v2_struct_0 @ X0)
% 0.21/0.49          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.49          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.21/0.49               X1)
% 0.21/0.49          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.21/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49          | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['69', '71'])).
% 0.21/0.49  thf('73', plain, ((v2_pre_topc @ sk_D)),
% 0.21/0.49      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.49  thf('74', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.49      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.49  thf('75', plain,
% 0.21/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('76', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('77', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('78', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('79', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_D)
% 0.21/0.49          | (v2_struct_0 @ X0)
% 0.21/0.49          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.49          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.21/0.49               X1)
% 0.21/0.49          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.21/0.49          | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)],
% 0.21/0.49                ['72', '73', '74', '75', '76', '77', '78'])).
% 0.21/0.49  thf('80', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_A)
% 0.21/0.49         | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.21/0.49         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.21/0.49         | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.21/0.49         | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.21/0.49         | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.21/0.49         | (v2_struct_0 @ sk_C)
% 0.21/0.49         | (v2_struct_0 @ sk_D)))
% 0.21/0.49         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['68', '79'])).
% 0.21/0.49  thf('81', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('82', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.21/0.49      inference('demod', [status(thm)], ['1', '2'])).
% 0.21/0.49  thf('83', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('84', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('85', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(t35_borsuk_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_pre_topc @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.21/0.49           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.49  thf('86', plain,
% 0.21/0.49      (![X16 : $i, X17 : $i]:
% 0.21/0.49         (~ (m1_pre_topc @ X16 @ X17)
% 0.21/0.49          | (r1_tarski @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X17))
% 0.21/0.49          | ~ (l1_pre_topc @ X17))),
% 0.21/0.49      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.21/0.49  thf('87', plain,
% 0.21/0.49      ((~ (l1_pre_topc @ sk_D)
% 0.21/0.49        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['85', '86'])).
% 0.21/0.49  thf('88', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.49      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.49  thf('89', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.21/0.49      inference('demod', [status(thm)], ['87', '88'])).
% 0.21/0.49  thf(t19_tsep_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.21/0.49               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) =>
% 0.21/0.49                 ( ( v1_tsep_1 @ B @ C ) & ( m1_pre_topc @ B @ C ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('90', plain,
% 0.21/0.49      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.49         (~ (v1_tsep_1 @ X13 @ X14)
% 0.21/0.49          | ~ (m1_pre_topc @ X13 @ X14)
% 0.21/0.49          | ~ (r1_tarski @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X15))
% 0.21/0.49          | (v1_tsep_1 @ X13 @ X15)
% 0.21/0.49          | ~ (m1_pre_topc @ X15 @ X14)
% 0.21/0.49          | (v2_struct_0 @ X15)
% 0.21/0.49          | ~ (l1_pre_topc @ X14)
% 0.21/0.49          | ~ (v2_pre_topc @ X14)
% 0.21/0.49          | (v2_struct_0 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [t19_tsep_1])).
% 0.21/0.49  thf('91', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X0)
% 0.21/0.49          | ~ (v2_pre_topc @ X0)
% 0.21/0.49          | ~ (l1_pre_topc @ X0)
% 0.21/0.49          | (v2_struct_0 @ sk_D)
% 0.21/0.49          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.21/0.49          | (v1_tsep_1 @ sk_C @ sk_D)
% 0.21/0.49          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.21/0.49          | ~ (v1_tsep_1 @ sk_C @ X0))),
% 0.21/0.49      inference('sup-', [status(thm)], ['89', '90'])).
% 0.21/0.49  thf('92', plain,
% 0.21/0.49      ((~ (v1_tsep_1 @ sk_C @ sk_B)
% 0.21/0.49        | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.21/0.49        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.21/0.49        | (v2_struct_0 @ sk_D)
% 0.21/0.49        | ~ (l1_pre_topc @ sk_B)
% 0.21/0.49        | ~ (v2_pre_topc @ sk_B)
% 0.21/0.49        | (v2_struct_0 @ sk_B))),
% 0.21/0.49      inference('sup-', [status(thm)], ['84', '91'])).
% 0.21/0.49  thf('93', plain, ((v1_tsep_1 @ sk_C @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('94', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('95', plain, ((l1_pre_topc @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('96', plain, ((v2_pre_topc @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('97', plain,
% 0.21/0.49      (((v1_tsep_1 @ sk_C @ sk_D) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 0.21/0.49      inference('demod', [status(thm)], ['92', '93', '94', '95', '96'])).
% 0.21/0.49  thf('98', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('99', plain, (((v2_struct_0 @ sk_B) | (v1_tsep_1 @ sk_C @ sk_D))),
% 0.21/0.49      inference('clc', [status(thm)], ['97', '98'])).
% 0.21/0.49  thf('100', plain, (~ (v2_struct_0 @ sk_B)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('101', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.21/0.49      inference('clc', [status(thm)], ['99', '100'])).
% 0.21/0.49  thf('102', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_A)
% 0.21/0.49         | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.21/0.49         | (v2_struct_0 @ sk_C)
% 0.21/0.49         | (v2_struct_0 @ sk_D)))
% 0.21/0.49         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.49      inference('demod', [status(thm)], ['80', '81', '82', '83', '101'])).
% 0.21/0.49  thf('103', plain,
% 0.21/0.49      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.21/0.49         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.21/0.49      inference('split', [status(esa)], ['10'])).
% 0.21/0.49  thf('104', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A)))
% 0.21/0.49         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.21/0.49             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['102', '103'])).
% 0.21/0.49  thf('105', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('106', plain,
% 0.21/0.49      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C)))
% 0.21/0.49         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.21/0.49             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.49      inference('clc', [status(thm)], ['104', '105'])).
% 0.21/0.49  thf('107', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('108', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_C))
% 0.21/0.49         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) & 
% 0.21/0.49             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.49      inference('clc', [status(thm)], ['106', '107'])).
% 0.21/0.49  thf('109', plain, (~ (v2_struct_0 @ sk_C)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('110', plain,
% 0.21/0.49      (~
% 0.21/0.49       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.21/0.49       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.21/0.49      inference('sup-', [status(thm)], ['108', '109'])).
% 0.21/0.49  thf('111', plain,
% 0.21/0.49      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) | 
% 0.21/0.49       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.21/0.49      inference('split', [status(esa)], ['8'])).
% 0.21/0.49  thf('112', plain, (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['14', '18', '110', '111'])).
% 0.21/0.49  thf('113', plain, ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['5', '112'])).
% 0.21/0.49  thf('114', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_E @ 
% 0.21/0.49        (k1_zfmisc_1 @ 
% 0.21/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('115', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X18)
% 0.21/0.49          | ~ (v2_pre_topc @ X18)
% 0.21/0.49          | ~ (l1_pre_topc @ X18)
% 0.21/0.49          | (v2_struct_0 @ X19)
% 0.21/0.49          | ~ (v1_tsep_1 @ X19 @ X18)
% 0.21/0.49          | ~ (m1_pre_topc @ X19 @ X18)
% 0.21/0.49          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.21/0.49          | ~ (r1_tmap_1 @ X18 @ X21 @ X22 @ X23)
% 0.21/0.49          | (r1_tmap_1 @ X19 @ X21 @ (k2_tmap_1 @ X18 @ X21 @ X22 @ X19) @ X20)
% 0.21/0.49          | ((X23) != (X20))
% 0.21/0.49          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X18))
% 0.21/0.49          | ~ (m1_subset_1 @ X22 @ 
% 0.21/0.49               (k1_zfmisc_1 @ 
% 0.21/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X21))))
% 0.21/0.49          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X21))
% 0.21/0.49          | ~ (v1_funct_1 @ X22)
% 0.21/0.49          | ~ (l1_pre_topc @ X21)
% 0.21/0.49          | ~ (v2_pre_topc @ X21)
% 0.21/0.49          | (v2_struct_0 @ X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [t67_tmap_1])).
% 0.21/0.49  thf('116', plain,
% 0.21/0.49      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.49         ((v2_struct_0 @ X21)
% 0.21/0.49          | ~ (v2_pre_topc @ X21)
% 0.21/0.49          | ~ (l1_pre_topc @ X21)
% 0.21/0.49          | ~ (v1_funct_1 @ X22)
% 0.21/0.49          | ~ (v1_funct_2 @ X22 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X21))
% 0.21/0.49          | ~ (m1_subset_1 @ X22 @ 
% 0.21/0.49               (k1_zfmisc_1 @ 
% 0.21/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X18) @ (u1_struct_0 @ X21))))
% 0.21/0.49          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.21/0.49          | (r1_tmap_1 @ X19 @ X21 @ (k2_tmap_1 @ X18 @ X21 @ X22 @ X19) @ X20)
% 0.21/0.49          | ~ (r1_tmap_1 @ X18 @ X21 @ X22 @ X20)
% 0.21/0.49          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 0.21/0.49          | ~ (m1_pre_topc @ X19 @ X18)
% 0.21/0.49          | ~ (v1_tsep_1 @ X19 @ X18)
% 0.21/0.49          | (v2_struct_0 @ X19)
% 0.21/0.49          | ~ (l1_pre_topc @ X18)
% 0.21/0.49          | ~ (v2_pre_topc @ X18)
% 0.21/0.49          | (v2_struct_0 @ X18))),
% 0.21/0.49      inference('simplify', [status(thm)], ['115'])).
% 0.21/0.49  thf('117', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_D)
% 0.21/0.49          | ~ (v2_pre_topc @ sk_D)
% 0.21/0.49          | ~ (l1_pre_topc @ sk_D)
% 0.21/0.49          | (v2_struct_0 @ X0)
% 0.21/0.49          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.49          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.21/0.49          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.21/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.21/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.21/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.21/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.21/0.49          | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['114', '116'])).
% 0.21/0.49  thf('118', plain, ((v2_pre_topc @ sk_D)),
% 0.21/0.49      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.21/0.49  thf('119', plain, ((l1_pre_topc @ sk_D)),
% 0.21/0.49      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.49  thf('120', plain,
% 0.21/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('121', plain, ((v1_funct_1 @ sk_E)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('122', plain, ((l1_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('123', plain, ((v2_pre_topc @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('124', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_D)
% 0.21/0.49          | (v2_struct_0 @ X0)
% 0.21/0.49          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.21/0.49          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.21/0.49          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.21/0.49          | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)],
% 0.21/0.49                ['117', '118', '119', '120', '121', '122', '123'])).
% 0.21/0.49  thf('125', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.21/0.49          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.21/0.49             sk_F)
% 0.21/0.49          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.49          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.21/0.49          | (v2_struct_0 @ X0)
% 0.21/0.49          | (v2_struct_0 @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['113', '124'])).
% 0.21/0.49  thf('126', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('127', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         ((v2_struct_0 @ sk_A)
% 0.21/0.49          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.21/0.49             sk_F)
% 0.21/0.49          | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.21/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.21/0.49          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.21/0.49          | (v2_struct_0 @ X0)
% 0.21/0.49          | (v2_struct_0 @ sk_D))),
% 0.21/0.49      inference('demod', [status(thm)], ['125', '126'])).
% 0.21/0.49  thf('128', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_D)
% 0.21/0.49        | (v2_struct_0 @ sk_C)
% 0.21/0.49        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.21/0.49        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.21/0.49        | (r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.21/0.49           sk_F)
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '127'])).
% 0.21/0.49  thf('129', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.21/0.49      inference('clc', [status(thm)], ['99', '100'])).
% 0.21/0.49  thf('130', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('131', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_D)
% 0.21/0.49        | (v2_struct_0 @ sk_C)
% 0.21/0.49        | (r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.21/0.49           sk_F)
% 0.21/0.49        | (v2_struct_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['128', '129', '130'])).
% 0.21/0.49  thf('132', plain,
% 0.21/0.49      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.21/0.49         <= (~
% 0.21/0.49             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('133', plain,
% 0.21/0.49      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.21/0.49         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))),
% 0.21/0.49      inference('clc', [status(thm)], ['62', '63'])).
% 0.21/0.49  thf('134', plain,
% 0.21/0.49      ((~ (r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.21/0.49           sk_F))
% 0.21/0.49         <= (~
% 0.21/0.49             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.49      inference('demod', [status(thm)], ['132', '133'])).
% 0.21/0.49  thf('135', plain,
% 0.21/0.49      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.21/0.49         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.21/0.49      inference('demod', [status(thm)], ['65', '66'])).
% 0.21/0.49  thf('136', plain,
% 0.21/0.49      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.21/0.49         <= (~
% 0.21/0.49             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F)))),
% 0.21/0.49      inference('split', [status(esa)], ['17'])).
% 0.21/0.49  thf('137', plain,
% 0.21/0.49      (~
% 0.21/0.49       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.21/0.49       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.21/0.49      inference('sup-', [status(thm)], ['135', '136'])).
% 0.21/0.49  thf('138', plain,
% 0.21/0.49      (~
% 0.21/0.49       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.21/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['14', '18', '110', '137'])).
% 0.21/0.49  thf('139', plain,
% 0.21/0.49      (~ (r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.21/0.49          sk_F)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['134', '138'])).
% 0.21/0.49  thf('140', plain,
% 0.21/0.49      (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 0.21/0.49      inference('sup-', [status(thm)], ['131', '139'])).
% 0.21/0.49  thf('141', plain, (~ (v2_struct_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('142', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.21/0.49      inference('clc', [status(thm)], ['140', '141'])).
% 0.21/0.49  thf('143', plain, (~ (v2_struct_0 @ sk_D)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('144', plain, ((v2_struct_0 @ sk_C)),
% 0.21/0.49      inference('clc', [status(thm)], ['142', '143'])).
% 0.21/0.49  thf('145', plain, ($false), inference('demod', [status(thm)], ['0', '144'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
