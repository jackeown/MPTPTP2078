%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j5er5A8ZQ5

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:24 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  169 ( 739 expanded)
%              Number of leaves         :   32 ( 224 expanded)
%              Depth                    :   24
%              Number of atoms          : 1979 (28927 expanded)
%              Number of equality atoms :   26 ( 399 expanded)
%              Maximal formula depth    :   26 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_tsep_1_type,type,(
    v1_tsep_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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

thf('1',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v2_pre_topc @ X11 )
      | ~ ( l1_pre_topc @ X11 )
      | ~ ( m1_pre_topc @ X12 @ X13 )
      | ~ ( m1_pre_topc @ X12 @ X14 )
      | ( ( k3_tmap_1 @ X13 @ X11 @ X14 @ X12 @ X15 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X11 ) @ X15 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X15 @ ( u1_struct_0 @ X14 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( m1_pre_topc @ X14 @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_tmap_1])).

thf('9',plain,(
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
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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
    inference(demod,[status(thm)],['9','10','11','12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','14'])).

thf('16',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','18'])).

thf('20',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( v2_struct_0 @ X7 )
      | ~ ( v2_pre_topc @ X7 )
      | ~ ( l1_pre_topc @ X7 )
      | ~ ( m1_pre_topc @ X8 @ X9 )
      | ( ( k2_tmap_1 @ X9 @ X7 @ X10 @ X8 )
        = ( k2_partfun1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) @ X10 @ ( u1_struct_0 @ X8 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( v1_funct_2 @ X10 @ ( u1_struct_0 @ X9 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( l1_pre_topc @ X9 )
      | ~ ( v2_pre_topc @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d4_tmap_1])).

thf('23',plain,(
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
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_pre_topc @ X3 @ X4 )
      | ( v2_pre_topc @ X3 )
      | ~ ( l1_pre_topc @ X4 )
      | ~ ( v2_pre_topc @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('26',plain,
    ( ~ ( v2_pre_topc @ sk_B )
    | ~ ( l1_pre_topc @ sk_B )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('31',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_pre_topc @ X5 @ X6 )
      | ( l1_pre_topc @ X5 )
      | ~ ( l1_pre_topc @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('32',plain,
    ( ~ ( l1_pre_topc @ sk_B )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','29','34','35','36','37','38'])).

thf('40',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','39'])).

thf('41',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['19','44','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_F )
   <= ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['4','50'])).

thf('52',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['52'])).

thf('54',plain,(
    m1_subset_1 @ sk_G @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['1'])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( v1_tsep_1 @ X22 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r1_tmap_1 @ X21 @ X24 @ X25 @ X26 )
      | ( r1_tmap_1 @ X22 @ X24 @ ( k2_tmap_1 @ X21 @ X24 @ X25 @ X22 ) @ X23 )
      | ( X26 != X23 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('60',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ( r1_tmap_1 @ X22 @ X24 @ ( k2_tmap_1 @ X21 @ X24 @ X25 @ X22 ) @ X23 )
      | ~ ( r1_tmap_1 @ X21 @ X24 @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( v1_tsep_1 @ X22 @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
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
    inference('sup-',[status(thm)],['58','60'])).

thf('62',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('63',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['32','33'])).

thf('64',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
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
    inference(demod,[status(thm)],['61','62','63','64','65','66','67'])).

thf('69',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_F )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_D )
        | ~ ( v1_tsep_1 @ X0 @ sk_D )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['57','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ sk_F )
        | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ X0 ) )
        | ~ ( m1_pre_topc @ X0 @ sk_D )
        | ~ ( v1_tsep_1 @ X0 @ sk_D )
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v1_tsep_1 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_F )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['56','71'])).

thf('73',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_tsep_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( m1_subset_1 @ ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('75',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_pre_topc @ X19 @ X20 )
      | ( m1_subset_1 @ ( u1_struct_0 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[t1_tsep_1])).

thf('76',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['32','33'])).

thf('78',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('80',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['78','79'])).

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

thf('81',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v1_tsep_1 @ X16 @ X17 )
      | ~ ( m1_pre_topc @ X16 @ X17 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X16 ) @ ( u1_struct_0 @ X18 ) )
      | ( v1_tsep_1 @ X16 @ X18 )
      | ~ ( m1_pre_topc @ X18 @ X17 )
      | ( v2_struct_0 @ X18 )
      | ~ ( l1_pre_topc @ X17 )
      | ~ ( v2_pre_topc @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t19_tsep_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v1_tsep_1 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_tsep_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ sk_B )
    | ~ ( m1_pre_topc @ sk_C @ sk_B )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['73','82'])).

thf('84',plain,(
    v1_tsep_1 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['83','84','85','86','87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_tsep_1 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_F )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['72','92','93'])).

thf('95',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('96',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['52'])).

thf('97',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['94','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['1'])).

thf('108',plain,(
    r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['53','106','107'])).

thf('109',plain,(
    r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['51','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ~ ( l1_pre_topc @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( v1_tsep_1 @ X22 @ X21 )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r1_tmap_1 @ X22 @ X24 @ ( k2_tmap_1 @ X21 @ X24 @ X25 @ X22 ) @ X23 )
      | ( r1_tmap_1 @ X21 @ X24 @ X25 @ X26 )
      | ( X26 != X23 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t67_tmap_1])).

thf('112',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X24 )
      | ~ ( v2_pre_topc @ X24 )
      | ~ ( l1_pre_topc @ X24 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_2 @ X25 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X21 ) @ ( u1_struct_0 @ X24 ) ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ( r1_tmap_1 @ X21 @ X24 @ X25 @ X23 )
      | ~ ( r1_tmap_1 @ X22 @ X24 @ ( k2_tmap_1 @ X21 @ X24 @ X25 @ X22 ) @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_pre_topc @ X22 @ X21 )
      | ~ ( v1_tsep_1 @ X22 @ X21 )
      | ( v2_struct_0 @ X22 )
      | ~ ( l1_pre_topc @ X21 )
      | ~ ( v2_pre_topc @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
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
    inference('sup-',[status(thm)],['110','112'])).

thf('114',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('115',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['32','33'])).

thf('116',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
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
    inference(demod,[status(thm)],['113','114','115','116','117','118','119'])).

thf('121',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ~ ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['109','120'])).

thf('122',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('124',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['90','91'])).

thf('126',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['121','122','123','124','125'])).

thf('127',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['52'])).

thf('128',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['53','106'])).

thf('129',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['126','129'])).

thf('131',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    $false ),
    inference(demod,[status(thm)],['0','134'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.j5er5A8ZQ5
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:46:17 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 92 iterations in 0.042s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.49  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.19/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.49  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.49  thf(sk_F_type, type, sk_F: $i).
% 0.19/0.49  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.49  thf(sk_G_type, type, sk_G: $i).
% 0.19/0.49  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.19/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.49  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.19/0.49  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.19/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.19/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.19/0.49  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.49  thf(t87_tmap_1, conjecture,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.49             ( l1_pre_topc @ B ) ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.19/0.49               ( ![D:$i]:
% 0.19/0.49                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.19/0.49                   ( ![E:$i]:
% 0.19/0.49                     ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.49                         ( v1_funct_2 @
% 0.19/0.49                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.49                         ( m1_subset_1 @
% 0.19/0.49                           E @ 
% 0.19/0.49                           ( k1_zfmisc_1 @
% 0.19/0.49                             ( k2_zfmisc_1 @
% 0.19/0.49                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.19/0.49                       ( ( ( v1_tsep_1 @ C @ B ) & ( m1_pre_topc @ C @ B ) & 
% 0.19/0.49                           ( m1_pre_topc @ C @ D ) ) =>
% 0.19/0.49                         ( ![F:$i]:
% 0.19/0.49                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.19/0.49                             ( ![G:$i]:
% 0.19/0.49                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.49                                 ( ( ( F ) = ( G ) ) =>
% 0.19/0.49                                   ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.19/0.49                                     ( r1_tmap_1 @
% 0.19/0.49                                       C @ A @ 
% 0.19/0.49                                       ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i]:
% 0.19/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.19/0.49            ( l1_pre_topc @ A ) ) =>
% 0.19/0.49          ( ![B:$i]:
% 0.19/0.49            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.49                ( l1_pre_topc @ B ) ) =>
% 0.19/0.49              ( ![C:$i]:
% 0.19/0.49                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.19/0.49                  ( ![D:$i]:
% 0.19/0.49                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.19/0.49                      ( ![E:$i]:
% 0.19/0.49                        ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.49                            ( v1_funct_2 @
% 0.19/0.49                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.49                            ( m1_subset_1 @
% 0.19/0.49                              E @ 
% 0.19/0.49                              ( k1_zfmisc_1 @
% 0.19/0.49                                ( k2_zfmisc_1 @
% 0.19/0.49                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.19/0.49                          ( ( ( v1_tsep_1 @ C @ B ) & 
% 0.19/0.49                              ( m1_pre_topc @ C @ B ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.19/0.49                            ( ![F:$i]:
% 0.19/0.49                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.19/0.49                                ( ![G:$i]:
% 0.19/0.49                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.49                                    ( ( ( F ) = ( G ) ) =>
% 0.19/0.49                                      ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.19/0.49                                        ( r1_tmap_1 @
% 0.19/0.49                                          C @ A @ 
% 0.19/0.49                                          ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t87_tmap_1])).
% 0.19/0.49  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.19/0.49        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.19/0.49         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.19/0.49      inference('split', [status(esa)], ['1'])).
% 0.19/0.49  thf('3', plain, (((sk_F) = (sk_G))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.19/0.49         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.19/0.49      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.49  thf('5', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('6', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_E @ 
% 0.19/0.49        (k1_zfmisc_1 @ 
% 0.19/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(d5_tmap_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.49             ( l1_pre_topc @ B ) ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( m1_pre_topc @ C @ A ) =>
% 0.19/0.49               ( ![D:$i]:
% 0.19/0.49                 ( ( m1_pre_topc @ D @ A ) =>
% 0.19/0.49                   ( ![E:$i]:
% 0.19/0.49                     ( ( ( v1_funct_1 @ E ) & 
% 0.19/0.49                         ( v1_funct_2 @
% 0.19/0.49                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.49                         ( m1_subset_1 @
% 0.19/0.49                           E @ 
% 0.19/0.49                           ( k1_zfmisc_1 @
% 0.19/0.49                             ( k2_zfmisc_1 @
% 0.19/0.49                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.49                       ( ( m1_pre_topc @ D @ C ) =>
% 0.19/0.49                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.19/0.49                           ( k2_partfun1 @
% 0.19/0.49                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.19/0.49                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.49         ((v2_struct_0 @ X11)
% 0.19/0.49          | ~ (v2_pre_topc @ X11)
% 0.19/0.49          | ~ (l1_pre_topc @ X11)
% 0.19/0.49          | ~ (m1_pre_topc @ X12 @ X13)
% 0.19/0.49          | ~ (m1_pre_topc @ X12 @ X14)
% 0.19/0.49          | ((k3_tmap_1 @ X13 @ X11 @ X14 @ X12 @ X15)
% 0.19/0.49              = (k2_partfun1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X11) @ 
% 0.19/0.49                 X15 @ (u1_struct_0 @ X12)))
% 0.19/0.49          | ~ (m1_subset_1 @ X15 @ 
% 0.19/0.49               (k1_zfmisc_1 @ 
% 0.19/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X11))))
% 0.19/0.49          | ~ (v1_funct_2 @ X15 @ (u1_struct_0 @ X14) @ (u1_struct_0 @ X11))
% 0.19/0.49          | ~ (v1_funct_1 @ X15)
% 0.19/0.49          | ~ (m1_pre_topc @ X14 @ X13)
% 0.19/0.49          | ~ (l1_pre_topc @ X13)
% 0.19/0.49          | ~ (v2_pre_topc @ X13)
% 0.19/0.49          | (v2_struct_0 @ X13))),
% 0.19/0.49      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((v2_struct_0 @ X0)
% 0.19/0.49          | ~ (v2_pre_topc @ X0)
% 0.19/0.49          | ~ (l1_pre_topc @ X0)
% 0.19/0.49          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.19/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.19/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49                 sk_E @ (u1_struct_0 @ X1)))
% 0.19/0.49          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.19/0.49          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.49          | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.49  thf('10', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((v2_struct_0 @ X0)
% 0.19/0.49          | ~ (v2_pre_topc @ X0)
% 0.19/0.49          | ~ (l1_pre_topc @ X0)
% 0.19/0.49          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.19/0.49          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.19/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49                 sk_E @ (u1_struct_0 @ X1)))
% 0.19/0.49          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.19/0.49          | ~ (m1_pre_topc @ X1 @ X0)
% 0.19/0.49          | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['9', '10', '11', '12', '13'])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_A)
% 0.19/0.49          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.19/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.49          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.19/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.49          | ~ (l1_pre_topc @ sk_B)
% 0.19/0.49          | ~ (v2_pre_topc @ sk_B)
% 0.19/0.49          | (v2_struct_0 @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['6', '14'])).
% 0.19/0.49  thf('16', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('17', plain, ((v2_pre_topc @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_A)
% 0.19/0.49          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.19/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.49          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.19/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.49          | (v2_struct_0 @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_B)
% 0.19/0.49        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.19/0.49            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49               sk_E @ (u1_struct_0 @ sk_C)))
% 0.19/0.49        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.19/0.49        | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['5', '18'])).
% 0.19/0.49  thf('20', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_E @ 
% 0.19/0.49        (k1_zfmisc_1 @ 
% 0.19/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(d4_tmap_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.49             ( l1_pre_topc @ B ) ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.49                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.19/0.49                 ( m1_subset_1 @
% 0.19/0.49                   C @ 
% 0.19/0.49                   ( k1_zfmisc_1 @
% 0.19/0.49                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.19/0.49               ( ![D:$i]:
% 0.19/0.49                 ( ( m1_pre_topc @ D @ A ) =>
% 0.19/0.49                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.19/0.49                     ( k2_partfun1 @
% 0.19/0.49                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.19/0.49                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.49         ((v2_struct_0 @ X7)
% 0.19/0.49          | ~ (v2_pre_topc @ X7)
% 0.19/0.49          | ~ (l1_pre_topc @ X7)
% 0.19/0.49          | ~ (m1_pre_topc @ X8 @ X9)
% 0.19/0.49          | ((k2_tmap_1 @ X9 @ X7 @ X10 @ X8)
% 0.19/0.49              = (k2_partfun1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7) @ X10 @ 
% 0.19/0.49                 (u1_struct_0 @ X8)))
% 0.19/0.49          | ~ (m1_subset_1 @ X10 @ 
% 0.19/0.49               (k1_zfmisc_1 @ 
% 0.19/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7))))
% 0.19/0.49          | ~ (v1_funct_2 @ X10 @ (u1_struct_0 @ X9) @ (u1_struct_0 @ X7))
% 0.19/0.49          | ~ (v1_funct_1 @ X10)
% 0.19/0.49          | ~ (l1_pre_topc @ X9)
% 0.19/0.49          | ~ (v2_pre_topc @ X9)
% 0.19/0.49          | (v2_struct_0 @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_D)
% 0.19/0.49          | ~ (v2_pre_topc @ sk_D)
% 0.19/0.49          | ~ (l1_pre_topc @ sk_D)
% 0.19/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.19/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.49          | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.49  thf('24', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(cc1_pre_topc, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      (![X3 : $i, X4 : $i]:
% 0.19/0.49         (~ (m1_pre_topc @ X3 @ X4)
% 0.19/0.49          | (v2_pre_topc @ X3)
% 0.19/0.49          | ~ (l1_pre_topc @ X4)
% 0.19/0.49          | ~ (v2_pre_topc @ X4))),
% 0.19/0.49      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      ((~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B) | (v2_pre_topc @ sk_D))),
% 0.19/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.49  thf('27', plain, ((v2_pre_topc @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('28', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('29', plain, ((v2_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.19/0.49  thf('30', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(dt_m1_pre_topc, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_pre_topc @ A ) =>
% 0.19/0.49       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      (![X5 : $i, X6 : $i]:
% 0.19/0.49         (~ (m1_pre_topc @ X5 @ X6) | (l1_pre_topc @ X5) | ~ (l1_pre_topc @ X6))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.19/0.49  thf('32', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.19/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.49  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('34', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['32', '33'])).
% 0.19/0.49  thf('35', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('39', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_D)
% 0.19/0.49          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.19/0.49              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49                 sk_E @ (u1_struct_0 @ X0)))
% 0.19/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.49          | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)],
% 0.19/0.49                ['23', '29', '34', '35', '36', '37', '38'])).
% 0.19/0.49  thf('40', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A)
% 0.19/0.49        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.19/0.49            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49               sk_E @ (u1_struct_0 @ sk_C)))
% 0.19/0.49        | (v2_struct_0 @ sk_D))),
% 0.19/0.49      inference('sup-', [status(thm)], ['20', '39'])).
% 0.19/0.49  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('42', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_D)
% 0.19/0.49        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.19/0.49            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.19/0.49               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.19/0.49      inference('clc', [status(thm)], ['40', '41'])).
% 0.19/0.49  thf('43', plain, (~ (v2_struct_0 @ sk_D)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      (((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.19/0.49         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_E @ 
% 0.19/0.49            (u1_struct_0 @ sk_C)))),
% 0.19/0.49      inference('clc', [status(thm)], ['42', '43'])).
% 0.19/0.49  thf('45', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('46', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_B)
% 0.19/0.49        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.19/0.49            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))
% 0.19/0.49        | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)], ['19', '44', '45'])).
% 0.19/0.49  thf('47', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('48', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A)
% 0.19/0.49        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.19/0.49            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)))),
% 0.19/0.49      inference('clc', [status(thm)], ['46', '47'])).
% 0.19/0.49  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('50', plain,
% 0.19/0.49      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.19/0.49         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))),
% 0.19/0.49      inference('clc', [status(thm)], ['48', '49'])).
% 0.19/0.49  thf('51', plain,
% 0.19/0.49      (((r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.19/0.49         sk_F))
% 0.19/0.49         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.19/0.49      inference('demod', [status(thm)], ['4', '50'])).
% 0.19/0.49  thf('52', plain,
% 0.19/0.49      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.19/0.49        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('53', plain,
% 0.19/0.49      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) | 
% 0.19/0.49       ~
% 0.19/0.49       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.19/0.49      inference('split', [status(esa)], ['52'])).
% 0.19/0.49  thf('54', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('55', plain, (((sk_F) = (sk_G))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('56', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.19/0.49      inference('demod', [status(thm)], ['54', '55'])).
% 0.19/0.49  thf('57', plain,
% 0.19/0.49      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.19/0.49         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.19/0.49      inference('split', [status(esa)], ['1'])).
% 0.19/0.49  thf('58', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_E @ 
% 0.19/0.49        (k1_zfmisc_1 @ 
% 0.19/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t67_tmap_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.19/0.49             ( l1_pre_topc @ B ) ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.49                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.19/0.49                 ( m1_subset_1 @
% 0.19/0.49                   C @ 
% 0.19/0.49                   ( k1_zfmisc_1 @
% 0.19/0.49                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.19/0.49               ( ![D:$i]:
% 0.19/0.49                 ( ( ( ~( v2_struct_0 @ D ) ) & ( v1_tsep_1 @ D @ B ) & 
% 0.19/0.49                     ( m1_pre_topc @ D @ B ) ) =>
% 0.19/0.49                   ( ![E:$i]:
% 0.19/0.49                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.19/0.49                       ( ![F:$i]:
% 0.19/0.49                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.19/0.49                           ( ( ( E ) = ( F ) ) =>
% 0.19/0.49                             ( ( r1_tmap_1 @ B @ A @ C @ E ) <=>
% 0.19/0.49                               ( r1_tmap_1 @
% 0.19/0.49                                 D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf('59', plain,
% 0.19/0.49      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.19/0.49         ((v2_struct_0 @ X21)
% 0.19/0.49          | ~ (v2_pre_topc @ X21)
% 0.19/0.49          | ~ (l1_pre_topc @ X21)
% 0.19/0.49          | (v2_struct_0 @ X22)
% 0.19/0.49          | ~ (v1_tsep_1 @ X22 @ X21)
% 0.19/0.49          | ~ (m1_pre_topc @ X22 @ X21)
% 0.19/0.49          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.19/0.49          | ~ (r1_tmap_1 @ X21 @ X24 @ X25 @ X26)
% 0.19/0.49          | (r1_tmap_1 @ X22 @ X24 @ (k2_tmap_1 @ X21 @ X24 @ X25 @ X22) @ X23)
% 0.19/0.49          | ((X26) != (X23))
% 0.19/0.49          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X21))
% 0.19/0.49          | ~ (m1_subset_1 @ X25 @ 
% 0.19/0.49               (k1_zfmisc_1 @ 
% 0.19/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X24))))
% 0.19/0.49          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X24))
% 0.19/0.49          | ~ (v1_funct_1 @ X25)
% 0.19/0.49          | ~ (l1_pre_topc @ X24)
% 0.19/0.49          | ~ (v2_pre_topc @ X24)
% 0.19/0.49          | (v2_struct_0 @ X24))),
% 0.19/0.49      inference('cnf', [status(esa)], [t67_tmap_1])).
% 0.19/0.49  thf('60', plain,
% 0.19/0.49      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.49         ((v2_struct_0 @ X24)
% 0.19/0.49          | ~ (v2_pre_topc @ X24)
% 0.19/0.49          | ~ (l1_pre_topc @ X24)
% 0.19/0.49          | ~ (v1_funct_1 @ X25)
% 0.19/0.49          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X24))
% 0.19/0.49          | ~ (m1_subset_1 @ X25 @ 
% 0.19/0.49               (k1_zfmisc_1 @ 
% 0.19/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X24))))
% 0.19/0.49          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 0.19/0.49          | (r1_tmap_1 @ X22 @ X24 @ (k2_tmap_1 @ X21 @ X24 @ X25 @ X22) @ X23)
% 0.19/0.49          | ~ (r1_tmap_1 @ X21 @ X24 @ X25 @ X23)
% 0.19/0.49          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.19/0.49          | ~ (m1_pre_topc @ X22 @ X21)
% 0.19/0.49          | ~ (v1_tsep_1 @ X22 @ X21)
% 0.19/0.49          | (v2_struct_0 @ X22)
% 0.19/0.49          | ~ (l1_pre_topc @ X21)
% 0.19/0.49          | ~ (v2_pre_topc @ X21)
% 0.19/0.49          | (v2_struct_0 @ X21))),
% 0.19/0.49      inference('simplify', [status(thm)], ['59'])).
% 0.19/0.49  thf('61', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_D)
% 0.19/0.49          | ~ (v2_pre_topc @ sk_D)
% 0.19/0.49          | ~ (l1_pre_topc @ sk_D)
% 0.19/0.49          | (v2_struct_0 @ X0)
% 0.19/0.49          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.19/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.19/0.49          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.19/0.49          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.19/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.19/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.49          | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['58', '60'])).
% 0.19/0.49  thf('62', plain, ((v2_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.19/0.49  thf('63', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['32', '33'])).
% 0.19/0.49  thf('64', plain,
% 0.19/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('65', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('68', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_D)
% 0.19/0.49          | (v2_struct_0 @ X0)
% 0.19/0.49          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.19/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.19/0.49          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.19/0.49          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.19/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.19/0.49          | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)],
% 0.19/0.49                ['61', '62', '63', '64', '65', '66', '67'])).
% 0.19/0.49  thf('69', plain,
% 0.19/0.49      ((![X0 : $i]:
% 0.19/0.49          ((v2_struct_0 @ sk_A)
% 0.19/0.49           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.19/0.49           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.19/0.49              sk_F)
% 0.19/0.49           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.19/0.49           | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.49           | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.19/0.49           | (v2_struct_0 @ X0)
% 0.19/0.49           | (v2_struct_0 @ sk_D)))
% 0.19/0.49         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['57', '68'])).
% 0.19/0.49  thf('70', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('71', plain,
% 0.19/0.49      ((![X0 : $i]:
% 0.19/0.49          ((v2_struct_0 @ sk_A)
% 0.19/0.49           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.19/0.49              sk_F)
% 0.19/0.49           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.19/0.49           | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.49           | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.19/0.49           | (v2_struct_0 @ X0)
% 0.19/0.49           | (v2_struct_0 @ sk_D)))
% 0.19/0.49         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.19/0.49      inference('demod', [status(thm)], ['69', '70'])).
% 0.19/0.49  thf('72', plain,
% 0.19/0.49      ((((v2_struct_0 @ sk_D)
% 0.19/0.49         | (v2_struct_0 @ sk_C)
% 0.19/0.49         | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.19/0.49         | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.19/0.49         | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49            (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ sk_F)
% 0.19/0.49         | (v2_struct_0 @ sk_A)))
% 0.19/0.49         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['56', '71'])).
% 0.19/0.49  thf('73', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('74', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(t1_tsep_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( l1_pre_topc @ A ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( m1_pre_topc @ B @ A ) =>
% 0.19/0.49           ( m1_subset_1 @
% 0.19/0.49             ( u1_struct_0 @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 0.19/0.49  thf('75', plain,
% 0.19/0.49      (![X19 : $i, X20 : $i]:
% 0.19/0.49         (~ (m1_pre_topc @ X19 @ X20)
% 0.19/0.49          | (m1_subset_1 @ (u1_struct_0 @ X19) @ 
% 0.19/0.49             (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.19/0.49          | ~ (l1_pre_topc @ X20))),
% 0.19/0.49      inference('cnf', [status(esa)], [t1_tsep_1])).
% 0.19/0.49  thf('76', plain,
% 0.19/0.49      ((~ (l1_pre_topc @ sk_D)
% 0.19/0.49        | (m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.19/0.49           (k1_zfmisc_1 @ (u1_struct_0 @ sk_D))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['74', '75'])).
% 0.19/0.49  thf('77', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['32', '33'])).
% 0.19/0.49  thf('78', plain,
% 0.19/0.49      ((m1_subset_1 @ (u1_struct_0 @ sk_C) @ 
% 0.19/0.49        (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.19/0.49      inference('demod', [status(thm)], ['76', '77'])).
% 0.19/0.49  thf(t3_subset, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.49  thf('79', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.49  thf('80', plain, ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.19/0.49      inference('sup-', [status(thm)], ['78', '79'])).
% 0.19/0.49  thf(t19_tsep_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.19/0.49           ( ![C:$i]:
% 0.19/0.49             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.19/0.49               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) =>
% 0.19/0.49                 ( ( v1_tsep_1 @ B @ C ) & ( m1_pre_topc @ B @ C ) ) ) ) ) ) ) ))).
% 0.19/0.49  thf('81', plain,
% 0.19/0.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.19/0.49         (~ (v1_tsep_1 @ X16 @ X17)
% 0.19/0.49          | ~ (m1_pre_topc @ X16 @ X17)
% 0.19/0.49          | ~ (r1_tarski @ (u1_struct_0 @ X16) @ (u1_struct_0 @ X18))
% 0.19/0.49          | (v1_tsep_1 @ X16 @ X18)
% 0.19/0.49          | ~ (m1_pre_topc @ X18 @ X17)
% 0.19/0.49          | (v2_struct_0 @ X18)
% 0.19/0.49          | ~ (l1_pre_topc @ X17)
% 0.19/0.49          | ~ (v2_pre_topc @ X17)
% 0.19/0.49          | (v2_struct_0 @ X17))),
% 0.19/0.49      inference('cnf', [status(esa)], [t19_tsep_1])).
% 0.19/0.49  thf('82', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((v2_struct_0 @ X0)
% 0.19/0.49          | ~ (v2_pre_topc @ X0)
% 0.19/0.49          | ~ (l1_pre_topc @ X0)
% 0.19/0.49          | (v2_struct_0 @ sk_D)
% 0.19/0.49          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.19/0.49          | (v1_tsep_1 @ sk_C @ sk_D)
% 0.19/0.49          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.19/0.49          | ~ (v1_tsep_1 @ sk_C @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['80', '81'])).
% 0.19/0.49  thf('83', plain,
% 0.19/0.49      ((~ (v1_tsep_1 @ sk_C @ sk_B)
% 0.19/0.49        | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.19/0.49        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.19/0.49        | (v2_struct_0 @ sk_D)
% 0.19/0.49        | ~ (l1_pre_topc @ sk_B)
% 0.19/0.49        | ~ (v2_pre_topc @ sk_B)
% 0.19/0.49        | (v2_struct_0 @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['73', '82'])).
% 0.19/0.49  thf('84', plain, ((v1_tsep_1 @ sk_C @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('85', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('86', plain, ((l1_pre_topc @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('87', plain, ((v2_pre_topc @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('88', plain,
% 0.19/0.49      (((v1_tsep_1 @ sk_C @ sk_D) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 0.19/0.49      inference('demod', [status(thm)], ['83', '84', '85', '86', '87'])).
% 0.19/0.49  thf('89', plain, (~ (v2_struct_0 @ sk_D)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('90', plain, (((v2_struct_0 @ sk_B) | (v1_tsep_1 @ sk_C @ sk_D))),
% 0.19/0.49      inference('clc', [status(thm)], ['88', '89'])).
% 0.19/0.49  thf('91', plain, (~ (v2_struct_0 @ sk_B)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('92', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.19/0.49      inference('clc', [status(thm)], ['90', '91'])).
% 0.19/0.49  thf('93', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('94', plain,
% 0.19/0.49      ((((v2_struct_0 @ sk_D)
% 0.19/0.49         | (v2_struct_0 @ sk_C)
% 0.19/0.49         | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49            (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ sk_F)
% 0.19/0.49         | (v2_struct_0 @ sk_A)))
% 0.19/0.49         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.19/0.49      inference('demod', [status(thm)], ['72', '92', '93'])).
% 0.19/0.49  thf('95', plain,
% 0.19/0.49      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.19/0.49         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))),
% 0.19/0.49      inference('clc', [status(thm)], ['48', '49'])).
% 0.19/0.49  thf('96', plain,
% 0.19/0.49      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.19/0.49         <= (~
% 0.19/0.49             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.19/0.49      inference('split', [status(esa)], ['52'])).
% 0.19/0.49  thf('97', plain, (((sk_F) = (sk_G))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('98', plain,
% 0.19/0.49      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.19/0.49         <= (~
% 0.19/0.49             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.19/0.49      inference('demod', [status(thm)], ['96', '97'])).
% 0.19/0.49  thf('99', plain,
% 0.19/0.49      ((~ (r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.19/0.49           sk_F))
% 0.19/0.49         <= (~
% 0.19/0.49             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['95', '98'])).
% 0.19/0.49  thf('100', plain,
% 0.19/0.49      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.19/0.49         <= (~
% 0.19/0.49             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.19/0.49             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['94', '99'])).
% 0.19/0.49  thf('101', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('102', plain,
% 0.19/0.49      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.19/0.49         <= (~
% 0.19/0.49             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.19/0.49             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.19/0.49      inference('clc', [status(thm)], ['100', '101'])).
% 0.19/0.49  thf('103', plain, (~ (v2_struct_0 @ sk_D)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('104', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_C))
% 0.19/0.49         <= (~
% 0.19/0.49             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.19/0.49             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.19/0.49      inference('clc', [status(thm)], ['102', '103'])).
% 0.19/0.49  thf('105', plain, (~ (v2_struct_0 @ sk_C)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('106', plain,
% 0.19/0.49      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.19/0.49       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.19/0.49      inference('sup-', [status(thm)], ['104', '105'])).
% 0.19/0.49  thf('107', plain,
% 0.19/0.49      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.19/0.49       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.19/0.49      inference('split', [status(esa)], ['1'])).
% 0.19/0.49  thf('108', plain,
% 0.19/0.49      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.19/0.49         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['53', '106', '107'])).
% 0.19/0.49  thf('109', plain,
% 0.19/0.49      ((r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.19/0.49        sk_F)),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['51', '108'])).
% 0.19/0.49  thf('110', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_E @ 
% 0.19/0.49        (k1_zfmisc_1 @ 
% 0.19/0.49         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('111', plain,
% 0.19/0.49      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.19/0.49         ((v2_struct_0 @ X21)
% 0.19/0.49          | ~ (v2_pre_topc @ X21)
% 0.19/0.49          | ~ (l1_pre_topc @ X21)
% 0.19/0.49          | (v2_struct_0 @ X22)
% 0.19/0.49          | ~ (v1_tsep_1 @ X22 @ X21)
% 0.19/0.49          | ~ (m1_pre_topc @ X22 @ X21)
% 0.19/0.49          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.19/0.49          | ~ (r1_tmap_1 @ X22 @ X24 @ (k2_tmap_1 @ X21 @ X24 @ X25 @ X22) @ 
% 0.19/0.49               X23)
% 0.19/0.49          | (r1_tmap_1 @ X21 @ X24 @ X25 @ X26)
% 0.19/0.49          | ((X26) != (X23))
% 0.19/0.49          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X21))
% 0.19/0.49          | ~ (m1_subset_1 @ X25 @ 
% 0.19/0.49               (k1_zfmisc_1 @ 
% 0.19/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X24))))
% 0.19/0.49          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X24))
% 0.19/0.49          | ~ (v1_funct_1 @ X25)
% 0.19/0.49          | ~ (l1_pre_topc @ X24)
% 0.19/0.49          | ~ (v2_pre_topc @ X24)
% 0.19/0.49          | (v2_struct_0 @ X24))),
% 0.19/0.49      inference('cnf', [status(esa)], [t67_tmap_1])).
% 0.19/0.49  thf('112', plain,
% 0.19/0.49      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.49         ((v2_struct_0 @ X24)
% 0.19/0.49          | ~ (v2_pre_topc @ X24)
% 0.19/0.49          | ~ (l1_pre_topc @ X24)
% 0.19/0.49          | ~ (v1_funct_1 @ X25)
% 0.19/0.49          | ~ (v1_funct_2 @ X25 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X24))
% 0.19/0.49          | ~ (m1_subset_1 @ X25 @ 
% 0.19/0.49               (k1_zfmisc_1 @ 
% 0.19/0.49                (k2_zfmisc_1 @ (u1_struct_0 @ X21) @ (u1_struct_0 @ X24))))
% 0.19/0.49          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 0.19/0.49          | (r1_tmap_1 @ X21 @ X24 @ X25 @ X23)
% 0.19/0.49          | ~ (r1_tmap_1 @ X22 @ X24 @ (k2_tmap_1 @ X21 @ X24 @ X25 @ X22) @ 
% 0.19/0.49               X23)
% 0.19/0.49          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 0.19/0.49          | ~ (m1_pre_topc @ X22 @ X21)
% 0.19/0.49          | ~ (v1_tsep_1 @ X22 @ X21)
% 0.19/0.49          | (v2_struct_0 @ X22)
% 0.19/0.49          | ~ (l1_pre_topc @ X21)
% 0.19/0.49          | ~ (v2_pre_topc @ X21)
% 0.19/0.49          | (v2_struct_0 @ X21))),
% 0.19/0.49      inference('simplify', [status(thm)], ['111'])).
% 0.19/0.49  thf('113', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_D)
% 0.19/0.49          | ~ (v2_pre_topc @ sk_D)
% 0.19/0.49          | ~ (l1_pre_topc @ sk_D)
% 0.19/0.49          | (v2_struct_0 @ X0)
% 0.19/0.49          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.19/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.19/0.49          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.19/0.49               X1)
% 0.19/0.49          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.19/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.19/0.49          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.19/0.49          | ~ (v1_funct_1 @ sk_E)
% 0.19/0.49          | ~ (l1_pre_topc @ sk_A)
% 0.19/0.49          | ~ (v2_pre_topc @ sk_A)
% 0.19/0.49          | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['110', '112'])).
% 0.19/0.49  thf('114', plain, ((v2_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.19/0.49  thf('115', plain, ((l1_pre_topc @ sk_D)),
% 0.19/0.49      inference('demod', [status(thm)], ['32', '33'])).
% 0.19/0.49  thf('116', plain,
% 0.19/0.49      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('117', plain, ((v1_funct_1 @ sk_E)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('118', plain, ((l1_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('119', plain, ((v2_pre_topc @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('120', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((v2_struct_0 @ sk_D)
% 0.19/0.49          | (v2_struct_0 @ X0)
% 0.19/0.49          | ~ (v1_tsep_1 @ X0 @ sk_D)
% 0.19/0.49          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.19/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.19/0.49          | ~ (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.19/0.49               X1)
% 0.19/0.49          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.19/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.19/0.49          | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('demod', [status(thm)],
% 0.19/0.49                ['113', '114', '115', '116', '117', '118', '119'])).
% 0.19/0.49  thf('121', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A)
% 0.19/0.49        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.19/0.49        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.19/0.49        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.19/0.49        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.19/0.49        | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.19/0.49        | (v2_struct_0 @ sk_C)
% 0.19/0.49        | (v2_struct_0 @ sk_D))),
% 0.19/0.49      inference('sup-', [status(thm)], ['109', '120'])).
% 0.19/0.49  thf('122', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('123', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.19/0.49      inference('demod', [status(thm)], ['54', '55'])).
% 0.19/0.49  thf('124', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('125', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.19/0.49      inference('clc', [status(thm)], ['90', '91'])).
% 0.19/0.49  thf('126', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_A)
% 0.19/0.49        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.19/0.49        | (v2_struct_0 @ sk_C)
% 0.19/0.49        | (v2_struct_0 @ sk_D))),
% 0.19/0.49      inference('demod', [status(thm)], ['121', '122', '123', '124', '125'])).
% 0.19/0.49  thf('127', plain,
% 0.19/0.49      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.19/0.49         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.19/0.49      inference('split', [status(esa)], ['52'])).
% 0.19/0.49  thf('128', plain, (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['53', '106'])).
% 0.19/0.49  thf('129', plain, (~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)),
% 0.19/0.49      inference('simpl_trail', [status(thm)], ['127', '128'])).
% 0.19/0.49  thf('130', plain,
% 0.19/0.49      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_A))),
% 0.19/0.49      inference('sup-', [status(thm)], ['126', '129'])).
% 0.19/0.49  thf('131', plain, (~ (v2_struct_0 @ sk_D)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('132', plain, (((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C))),
% 0.19/0.49      inference('clc', [status(thm)], ['130', '131'])).
% 0.19/0.49  thf('133', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('134', plain, ((v2_struct_0 @ sk_C)),
% 0.19/0.49      inference('clc', [status(thm)], ['132', '133'])).
% 0.19/0.49  thf('135', plain, ($false), inference('demod', [status(thm)], ['0', '134'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
