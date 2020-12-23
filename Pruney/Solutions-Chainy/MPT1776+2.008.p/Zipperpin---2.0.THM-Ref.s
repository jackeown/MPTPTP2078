%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9vhj2R2Z0V

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:24 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 735 expanded)
%              Number of leaves         :   32 ( 222 expanded)
%              Depth                    :   25
%              Number of atoms          : 2141 (29877 expanded)
%              Number of equality atoms :   28 ( 426 expanded)
%              Maximal formula depth    :   29 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(r1_tmap_1_type,type,(
    r1_tmap_1: $i > $i > $i > $i > $o )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

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

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

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
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
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
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
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

thf('59',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ~ ( l1_pre_topc @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( r1_tmap_1 @ X20 @ X22 @ ( k2_tmap_1 @ X19 @ X22 @ X23 @ X20 ) @ X21 )
      | ( X24 != X21 )
      | ~ ( r1_tmap_1 @ X19 @ X22 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t64_tmap_1])).

thf('60',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v2_pre_topc @ X22 )
      | ~ ( l1_pre_topc @ X22 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X19 ) @ ( u1_struct_0 @ X22 ) ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r1_tmap_1 @ X19 @ X22 @ X23 @ X21 )
      | ( r1_tmap_1 @ X20 @ X22 @ ( k2_tmap_1 @ X19 @ X22 @ X23 @ X20 ) @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_pre_topc @ X20 @ X19 )
      | ( v2_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
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
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_tmap_1 @ X0 @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 ) @ X1 )
      | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1 )
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
        | ( v2_struct_0 @ X0 )
        | ( v2_struct_0 @ sk_D ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_F )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['56','71'])).

thf('73',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C )
      | ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_F )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('76',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(split,[status(esa)],['52'])).

thf('77',plain,(
    sk_F = sk_G ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_C )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['74','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_C ) )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( v2_struct_0 @ sk_C )
   <= ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
      & ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['1'])).

thf('88',plain,(
    r1_tmap_1 @ sk_C @ sk_A @ ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E ) @ sk_G ),
    inference('sat_resolution*',[status(thm)],['53','86','87'])).

thf('89',plain,(
    r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ sk_F ),
    inference(simpl_trail,[status(thm)],['51','88'])).

thf('90',plain,
    ( ( k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('91',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t86_tmap_1,axiom,(
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
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ( ( ( v1_tsep_1 @ C @ D )
                          & ( m1_pre_topc @ C @ D ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) )
                           => ! [G: $i] :
                                ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) )
                               => ( ( F = G )
                                 => ( ( r1_tmap_1 @ D @ B @ E @ F )
                                  <=> ( r1_tmap_1 @ C @ B @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) )).

thf('92',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ~ ( l1_pre_topc @ X28 )
      | ( v2_struct_0 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ~ ( v1_tsep_1 @ X31 @ X29 )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X29 ) )
      | ( X32 != X33 )
      | ~ ( r1_tmap_1 @ X31 @ X28 @ ( k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34 ) @ X33 )
      | ( r1_tmap_1 @ X29 @ X28 @ X34 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( l1_pre_topc @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t86_tmap_1])).

thf('93',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X33: $i,X34: $i] :
      ( ( v2_struct_0 @ X30 )
      | ~ ( v2_pre_topc @ X30 )
      | ~ ( l1_pre_topc @ X30 )
      | ( v2_struct_0 @ X31 )
      | ~ ( m1_pre_topc @ X31 @ X30 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ( r1_tmap_1 @ X29 @ X28 @ X34 @ X33 )
      | ~ ( r1_tmap_1 @ X31 @ X28 @ ( k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34 ) @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X29 ) )
      | ~ ( m1_pre_topc @ X31 @ X29 )
      | ~ ( v1_tsep_1 @ X31 @ X29 )
      | ~ ( m1_pre_topc @ X29 @ X30 )
      | ( v2_struct_0 @ X29 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ~ ( l1_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_tsep_1 @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( r1_tmap_1 @ X1 @ sk_A @ ( k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E ) @ X2 )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_pre_topc @ sk_C @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_pre_topc @ sk_C @ sk_D )
      | ~ ( v1_tsep_1 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ sk_B )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','99'])).

thf('101',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_borsuk_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf('107',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_pre_topc @ X17 @ X18 )
      | ( r1_tarski @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_pre_topc @ X18 ) ) ),
    inference(cnf,[status(esa)],[t35_borsuk_1])).

thf('108',plain,
    ( ~ ( l1_pre_topc @ sk_D )
    | ( r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['32','33'])).

thf('110',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['108','109'])).

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

thf('111',plain,(
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

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( v1_tsep_1 @ sk_C @ sk_D )
      | ~ ( m1_pre_topc @ sk_C @ X0 )
      | ~ ( v1_tsep_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ~ ( v1_tsep_1 @ sk_C @ sk_B )
    | ~ ( m1_pre_topc @ sk_C @ sk_B )
    | ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_pre_topc @ sk_B )
    | ~ ( v2_pre_topc @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['105','112'])).

thf('114',plain,(
    v1_tsep_1 @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    m1_pre_topc @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v1_tsep_1 @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['113','114','115','116','117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_tsep_1 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_tsep_1 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    m1_pre_topc @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tmap_1 @ sk_C @ sk_A @ ( k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D ) )
      | ( v2_struct_0 @ sk_D )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','101','102','103','104','122','123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ~ ( m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['89','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    m1_subset_1 @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('128',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_D )
    | ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['125','126','127'])).

thf('129',plain,
    ( ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F )
   <= ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['52'])).

thf('130',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['53','86'])).

thf('131',plain,(
    ~ ( r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F ) ),
    inference(simpl_trail,[status(thm)],['129','130'])).

thf('132',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['128','131'])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['132','133'])).

thf('135',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,(
    $false ),
    inference(demod,[status(thm)],['0','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9vhj2R2Z0V
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:22:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 103 iterations in 0.042s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.50  thf(sk_G_type, type, sk_G: $i).
% 0.20/0.50  thf(r1_tmap_1_type, type, r1_tmap_1: $i > $i > $i > $i > $o).
% 0.20/0.50  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.50  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.20/0.50  thf(v1_tsep_1_type, type, v1_tsep_1: $i > $i > $o).
% 0.20/0.50  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.50  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(t87_tmap_1, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50             ( l1_pre_topc @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.50                   ( ![E:$i]:
% 0.20/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.50                         ( v1_funct_2 @
% 0.20/0.50                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50                         ( m1_subset_1 @
% 0.20/0.50                           E @ 
% 0.20/0.50                           ( k1_zfmisc_1 @
% 0.20/0.50                             ( k2_zfmisc_1 @
% 0.20/0.50                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.50                       ( ( ( v1_tsep_1 @ C @ B ) & ( m1_pre_topc @ C @ B ) & 
% 0.20/0.50                           ( m1_pre_topc @ C @ D ) ) =>
% 0.20/0.50                         ( ![F:$i]:
% 0.20/0.50                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.50                             ( ![G:$i]:
% 0.20/0.50                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.50                                 ( ( ( F ) = ( G ) ) =>
% 0.20/0.50                                   ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.20/0.50                                     ( r1_tmap_1 @
% 0.20/0.50                                       C @ A @ 
% 0.20/0.50                                       ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.50            ( l1_pre_topc @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50                ( l1_pre_topc @ B ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.50                  ( ![D:$i]:
% 0.20/0.50                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.50                      ( ![E:$i]:
% 0.20/0.50                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.50                            ( v1_funct_2 @
% 0.20/0.50                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50                            ( m1_subset_1 @
% 0.20/0.50                              E @ 
% 0.20/0.50                              ( k1_zfmisc_1 @
% 0.20/0.50                                ( k2_zfmisc_1 @
% 0.20/0.50                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.50                          ( ( ( v1_tsep_1 @ C @ B ) & 
% 0.20/0.50                              ( m1_pre_topc @ C @ B ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.20/0.50                            ( ![F:$i]:
% 0.20/0.50                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.50                                ( ![G:$i]:
% 0.20/0.50                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.50                                    ( ( ( F ) = ( G ) ) =>
% 0.20/0.50                                      ( ( r1_tmap_1 @ D @ A @ E @ F ) <=>
% 0.20/0.50                                        ( r1_tmap_1 @
% 0.20/0.50                                          C @ A @ 
% 0.20/0.50                                          ( k3_tmap_1 @ B @ A @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t87_tmap_1])).
% 0.20/0.50  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.20/0.50        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.50      inference('split', [status(esa)], ['1'])).
% 0.20/0.50  thf('3', plain, (((sk_F) = (sk_G))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.50      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.50  thf('5', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('6', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_E @ 
% 0.20/0.50        (k1_zfmisc_1 @ 
% 0.20/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d5_tmap_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50             ( l1_pre_topc @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.50                   ( ![E:$i]:
% 0.20/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.50                         ( v1_funct_2 @
% 0.20/0.50                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.50                         ( m1_subset_1 @
% 0.20/0.50                           E @ 
% 0.20/0.50                           ( k1_zfmisc_1 @
% 0.20/0.50                             ( k2_zfmisc_1 @
% 0.20/0.50                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.50                       ( ( m1_pre_topc @ D @ C ) =>
% 0.20/0.50                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.50                           ( k2_partfun1 @
% 0.20/0.50                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.20/0.50                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X8)
% 0.20/0.50          | ~ (v2_pre_topc @ X8)
% 0.20/0.50          | ~ (l1_pre_topc @ X8)
% 0.20/0.50          | ~ (m1_pre_topc @ X9 @ X10)
% 0.20/0.50          | ~ (m1_pre_topc @ X9 @ X11)
% 0.20/0.50          | ((k3_tmap_1 @ X10 @ X8 @ X11 @ X9 @ X12)
% 0.20/0.50              = (k2_partfun1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8) @ 
% 0.20/0.50                 X12 @ (u1_struct_0 @ X9)))
% 0.20/0.50          | ~ (m1_subset_1 @ X12 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))))
% 0.20/0.50          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))
% 0.20/0.50          | ~ (v1_funct_1 @ X12)
% 0.20/0.50          | ~ (m1_pre_topc @ X11 @ X10)
% 0.20/0.50          | ~ (l1_pre_topc @ X10)
% 0.20/0.50          | ~ (v2_pre_topc @ X10)
% 0.20/0.50          | (v2_struct_0 @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.20/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('12', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('13', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.50          | ((k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E)
% 0.20/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['9', '10', '11', '12', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.50          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.20/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.50          | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '14'])).
% 0.20/0.50  thf('16', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('17', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_B)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.50          | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ X0 @ sk_E)
% 0.20/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.50          | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_B)
% 0.20/0.50        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.20/0.50            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50               sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.50        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['5', '18'])).
% 0.20/0.50  thf('20', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_E @ 
% 0.20/0.50        (k1_zfmisc_1 @ 
% 0.20/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d4_tmap_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50             ( l1_pre_topc @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.50                 ( m1_subset_1 @
% 0.20/0.50                   C @ 
% 0.20/0.50                   ( k1_zfmisc_1 @
% 0.20/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.50                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.20/0.50                     ( k2_partfun1 @
% 0.20/0.50                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.50                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X4)
% 0.20/0.50          | ~ (v2_pre_topc @ X4)
% 0.20/0.50          | ~ (l1_pre_topc @ X4)
% 0.20/0.50          | ~ (m1_pre_topc @ X5 @ X6)
% 0.20/0.50          | ((k2_tmap_1 @ X6 @ X4 @ X7 @ X5)
% 0.20/0.50              = (k2_partfun1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4) @ X7 @ 
% 0.20/0.50                 (u1_struct_0 @ X5)))
% 0.20/0.50          | ~ (m1_subset_1 @ X7 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.20/0.50          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.20/0.50          | ~ (v1_funct_1 @ X7)
% 0.20/0.50          | ~ (l1_pre_topc @ X6)
% 0.20/0.50          | ~ (v2_pre_topc @ X6)
% 0.20/0.50          | (v2_struct_0 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_D)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.20/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(cc1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.50          | (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X1)
% 0.20/0.50          | ~ (v2_pre_topc @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      ((~ (v2_pre_topc @ sk_B) | ~ (l1_pre_topc @ sk_B) | (v2_pre_topc @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('28', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('29', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.20/0.50  thf('30', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_m1_pre_topc, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X2 : $i, X3 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.50  thf('32', plain, ((~ (l1_pre_topc @ sk_B) | (l1_pre_topc @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.20/0.50  thf('33', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('34', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('35', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('36', plain,
% 0.20/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('38', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_D)
% 0.20/0.50          | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.20/0.50              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)],
% 0.20/0.50                ['23', '29', '34', '35', '36', '37', '38'])).
% 0.20/0.50  thf('40', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.20/0.50            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50               sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.50        | (v2_struct_0 @ sk_D))),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '39'])).
% 0.20/0.50  thf('41', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('42', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_D)
% 0.20/0.50        | ((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.20/0.50            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.50               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.20/0.50      inference('clc', [status(thm)], ['40', '41'])).
% 0.20/0.50  thf('43', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (((k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)
% 0.20/0.50         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A) @ sk_E @ 
% 0.20/0.50            (u1_struct_0 @ sk_C)))),
% 0.20/0.50      inference('clc', [status(thm)], ['42', '43'])).
% 0.20/0.50  thf('45', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('46', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_B)
% 0.20/0.50        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.20/0.50            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['19', '44', '45'])).
% 0.20/0.50  thf('47', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('48', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.20/0.50            = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C)))),
% 0.20/0.50      inference('clc', [status(thm)], ['46', '47'])).
% 0.20/0.50  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.20/0.50         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))),
% 0.20/0.50      inference('clc', [status(thm)], ['48', '49'])).
% 0.20/0.50  thf('51', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.20/0.50         sk_F))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.50      inference('demod', [status(thm)], ['4', '50'])).
% 0.20/0.50  thf('52', plain,
% 0.20/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)
% 0.20/0.50        | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('53', plain,
% 0.20/0.50      (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)) | 
% 0.20/0.50       ~
% 0.20/0.50       ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.20/0.50      inference('split', [status(esa)], ['52'])).
% 0.20/0.50  thf('54', plain, ((m1_subset_1 @ sk_G @ (u1_struct_0 @ sk_C))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('55', plain, (((sk_F) = (sk_G))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('56', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.50  thf('57', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.50      inference('split', [status(esa)], ['1'])).
% 0.20/0.50  thf('58', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_E @ 
% 0.20/0.50        (k1_zfmisc_1 @ 
% 0.20/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t64_tmap_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50             ( l1_pre_topc @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.50                 ( v1_funct_2 @ C @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.50                 ( m1_subset_1 @
% 0.20/0.50                   C @ 
% 0.20/0.50                   ( k1_zfmisc_1 @
% 0.20/0.50                     ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ B ) ) =>
% 0.20/0.50                   ( ![E:$i]:
% 0.20/0.50                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.50                       ( ![F:$i]:
% 0.20/0.50                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.50                           ( ( ( ( E ) = ( F ) ) & 
% 0.20/0.50                               ( r1_tmap_1 @ B @ A @ C @ E ) ) =>
% 0.20/0.50                             ( r1_tmap_1 @
% 0.20/0.50                               D @ A @ ( k2_tmap_1 @ B @ A @ C @ D ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('59', plain,
% 0.20/0.50      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X19)
% 0.20/0.50          | ~ (v2_pre_topc @ X19)
% 0.20/0.50          | ~ (l1_pre_topc @ X19)
% 0.20/0.50          | (v2_struct_0 @ X20)
% 0.20/0.50          | ~ (m1_pre_topc @ X20 @ X19)
% 0.20/0.50          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.20/0.50          | (r1_tmap_1 @ X20 @ X22 @ (k2_tmap_1 @ X19 @ X22 @ X23 @ X20) @ X21)
% 0.20/0.50          | ((X24) != (X21))
% 0.20/0.50          | ~ (r1_tmap_1 @ X19 @ X22 @ X23 @ X24)
% 0.20/0.50          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X19))
% 0.20/0.50          | ~ (m1_subset_1 @ X23 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X22))))
% 0.20/0.50          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X22))
% 0.20/0.50          | ~ (v1_funct_1 @ X23)
% 0.20/0.50          | ~ (l1_pre_topc @ X22)
% 0.20/0.50          | ~ (v2_pre_topc @ X22)
% 0.20/0.50          | (v2_struct_0 @ X22))),
% 0.20/0.50      inference('cnf', [status(esa)], [t64_tmap_1])).
% 0.20/0.50  thf('60', plain,
% 0.20/0.50      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X22)
% 0.20/0.50          | ~ (v2_pre_topc @ X22)
% 0.20/0.50          | ~ (l1_pre_topc @ X22)
% 0.20/0.50          | ~ (v1_funct_1 @ X23)
% 0.20/0.50          | ~ (v1_funct_2 @ X23 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X22))
% 0.20/0.50          | ~ (m1_subset_1 @ X23 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X19) @ (u1_struct_0 @ X22))))
% 0.20/0.50          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X19))
% 0.20/0.50          | ~ (r1_tmap_1 @ X19 @ X22 @ X23 @ X21)
% 0.20/0.50          | (r1_tmap_1 @ X20 @ X22 @ (k2_tmap_1 @ X19 @ X22 @ X23 @ X20) @ X21)
% 0.20/0.50          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.20/0.50          | ~ (m1_pre_topc @ X20 @ X19)
% 0.20/0.50          | (v2_struct_0 @ X20)
% 0.20/0.50          | ~ (l1_pre_topc @ X19)
% 0.20/0.50          | ~ (v2_pre_topc @ X19)
% 0.20/0.50          | (v2_struct_0 @ X19))),
% 0.20/0.50      inference('simplify', [status(thm)], ['59'])).
% 0.20/0.50  thf('61', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_D)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.50          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.20/0.50          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.20/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['58', '60'])).
% 0.20/0.50  thf('62', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.20/0.50  thf('63', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('64', plain,
% 0.20/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('65', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('67', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('68', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_D)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.50          | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ X1)
% 0.20/0.50          | ~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X1)
% 0.20/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D))
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)],
% 0.20/0.50                ['61', '62', '63', '64', '65', '66', '67'])).
% 0.20/0.50  thf('69', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          ((v2_struct_0 @ sk_A)
% 0.20/0.50           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.20/0.50           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.20/0.50              sk_F)
% 0.20/0.50           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.20/0.50           | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.50           | (v2_struct_0 @ X0)
% 0.20/0.50           | (v2_struct_0 @ sk_D)))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['57', '68'])).
% 0.20/0.50  thf('70', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('71', plain,
% 0.20/0.50      ((![X0 : $i]:
% 0.20/0.50          ((v2_struct_0 @ sk_A)
% 0.20/0.50           | (r1_tmap_1 @ X0 @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ X0) @ 
% 0.20/0.50              sk_F)
% 0.20/0.50           | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ X0))
% 0.20/0.50           | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.50           | (v2_struct_0 @ X0)
% 0.20/0.50           | (v2_struct_0 @ sk_D)))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.50      inference('demod', [status(thm)], ['69', '70'])).
% 0.20/0.50  thf('72', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_D)
% 0.20/0.50         | (v2_struct_0 @ sk_C)
% 0.20/0.50         | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.50         | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50            (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ sk_F)
% 0.20/0.50         | (v2_struct_0 @ sk_A)))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['56', '71'])).
% 0.20/0.50  thf('73', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('74', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_D)
% 0.20/0.50         | (v2_struct_0 @ sk_C)
% 0.20/0.50         | (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50            (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ sk_F)
% 0.20/0.50         | (v2_struct_0 @ sk_A)))
% 0.20/0.50         <= (((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.50      inference('demod', [status(thm)], ['72', '73'])).
% 0.20/0.50  thf('75', plain,
% 0.20/0.50      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.20/0.50         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))),
% 0.20/0.50      inference('clc', [status(thm)], ['48', '49'])).
% 0.20/0.50  thf('76', plain,
% 0.20/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.50      inference('split', [status(esa)], ['52'])).
% 0.20/0.50  thf('77', plain, (((sk_F) = (sk_G))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('78', plain,
% 0.20/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50           (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_F))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.50      inference('demod', [status(thm)], ['76', '77'])).
% 0.20/0.50  thf('79', plain,
% 0.20/0.50      ((~ (r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.20/0.50           sk_F))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['75', '78'])).
% 0.20/0.50  thf('80', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_A) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D)))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.20/0.50             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['74', '79'])).
% 0.20/0.50  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('82', plain,
% 0.20/0.50      ((((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C)))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.20/0.50             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.50      inference('clc', [status(thm)], ['80', '81'])).
% 0.20/0.50  thf('83', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('84', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_C))
% 0.20/0.50         <= (~
% 0.20/0.50             ((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) & 
% 0.20/0.50             ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.50      inference('clc', [status(thm)], ['82', '83'])).
% 0.20/0.50  thf('85', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('86', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.20/0.50       ~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.20/0.50      inference('sup-', [status(thm)], ['84', '85'])).
% 0.20/0.50  thf('87', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G)) | 
% 0.20/0.50       ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.20/0.50      inference('split', [status(esa)], ['1'])).
% 0.20/0.50  thf('88', plain,
% 0.20/0.50      (((r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50         (k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E) @ sk_G))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['53', '86', '87'])).
% 0.20/0.50  thf('89', plain,
% 0.20/0.50      ((r1_tmap_1 @ sk_C @ sk_A @ (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ 
% 0.20/0.50        sk_F)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['51', '88'])).
% 0.20/0.50  thf('90', plain,
% 0.20/0.50      (((k3_tmap_1 @ sk_B @ sk_A @ sk_D @ sk_C @ sk_E)
% 0.20/0.50         = (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C))),
% 0.20/0.50      inference('clc', [status(thm)], ['48', '49'])).
% 0.20/0.50  thf('91', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_E @ 
% 0.20/0.50        (k1_zfmisc_1 @ 
% 0.20/0.50         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t86_tmap_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.50             ( l1_pre_topc @ B ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.50               ( ![D:$i]:
% 0.20/0.50                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.50                   ( ![E:$i]:
% 0.20/0.50                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.50                         ( v1_funct_2 @
% 0.20/0.50                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.50                         ( m1_subset_1 @
% 0.20/0.50                           E @ 
% 0.20/0.50                           ( k1_zfmisc_1 @
% 0.20/0.50                             ( k2_zfmisc_1 @
% 0.20/0.50                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.50                       ( ( ( v1_tsep_1 @ C @ D ) & ( m1_pre_topc @ C @ D ) ) =>
% 0.20/0.50                         ( ![F:$i]:
% 0.20/0.50                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ D ) ) =>
% 0.20/0.50                             ( ![G:$i]:
% 0.20/0.50                               ( ( m1_subset_1 @ G @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.50                                 ( ( ( F ) = ( G ) ) =>
% 0.20/0.50                                   ( ( r1_tmap_1 @ D @ B @ E @ F ) <=>
% 0.20/0.50                                     ( r1_tmap_1 @
% 0.20/0.50                                       C @ B @ 
% 0.20/0.50                                       ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('92', plain,
% 0.20/0.50      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X28)
% 0.20/0.50          | ~ (v2_pre_topc @ X28)
% 0.20/0.50          | ~ (l1_pre_topc @ X28)
% 0.20/0.50          | (v2_struct_0 @ X29)
% 0.20/0.50          | ~ (m1_pre_topc @ X29 @ X30)
% 0.20/0.50          | ~ (v1_tsep_1 @ X31 @ X29)
% 0.20/0.50          | ~ (m1_pre_topc @ X31 @ X29)
% 0.20/0.50          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X29))
% 0.20/0.50          | ((X32) != (X33))
% 0.20/0.50          | ~ (r1_tmap_1 @ X31 @ X28 @ 
% 0.20/0.50               (k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34) @ X33)
% 0.20/0.50          | (r1_tmap_1 @ X29 @ X28 @ X34 @ X32)
% 0.20/0.50          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.20/0.50          | ~ (m1_subset_1 @ X34 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))))
% 0.20/0.50          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))
% 0.20/0.50          | ~ (v1_funct_1 @ X34)
% 0.20/0.50          | ~ (m1_pre_topc @ X31 @ X30)
% 0.20/0.50          | (v2_struct_0 @ X31)
% 0.20/0.50          | ~ (l1_pre_topc @ X30)
% 0.20/0.50          | ~ (v2_pre_topc @ X30)
% 0.20/0.50          | (v2_struct_0 @ X30))),
% 0.20/0.50      inference('cnf', [status(esa)], [t86_tmap_1])).
% 0.20/0.50  thf('93', plain,
% 0.20/0.50      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X33 : $i, X34 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X30)
% 0.20/0.50          | ~ (v2_pre_topc @ X30)
% 0.20/0.50          | ~ (l1_pre_topc @ X30)
% 0.20/0.50          | (v2_struct_0 @ X31)
% 0.20/0.50          | ~ (m1_pre_topc @ X31 @ X30)
% 0.20/0.50          | ~ (v1_funct_1 @ X34)
% 0.20/0.50          | ~ (v1_funct_2 @ X34 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))
% 0.20/0.50          | ~ (m1_subset_1 @ X34 @ 
% 0.20/0.50               (k1_zfmisc_1 @ 
% 0.20/0.50                (k2_zfmisc_1 @ (u1_struct_0 @ X29) @ (u1_struct_0 @ X28))))
% 0.20/0.50          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 0.20/0.50          | (r1_tmap_1 @ X29 @ X28 @ X34 @ X33)
% 0.20/0.50          | ~ (r1_tmap_1 @ X31 @ X28 @ 
% 0.20/0.50               (k3_tmap_1 @ X30 @ X28 @ X29 @ X31 @ X34) @ X33)
% 0.20/0.50          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X29))
% 0.20/0.50          | ~ (m1_pre_topc @ X31 @ X29)
% 0.20/0.50          | ~ (v1_tsep_1 @ X31 @ X29)
% 0.20/0.50          | ~ (m1_pre_topc @ X29 @ X30)
% 0.20/0.50          | (v2_struct_0 @ X29)
% 0.20/0.50          | ~ (l1_pre_topc @ X28)
% 0.20/0.50          | ~ (v2_pre_topc @ X28)
% 0.20/0.50          | (v2_struct_0 @ X28))),
% 0.20/0.50      inference('simplify', [status(thm)], ['92'])).
% 0.20/0.50  thf('94', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.50          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.50          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X2)
% 0.20/0.50          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))
% 0.20/0.50          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.50          | (v2_struct_0 @ X1)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['91', '93'])).
% 0.20/0.50  thf('95', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('96', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('97', plain,
% 0.20/0.50      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_A))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('98', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('99', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.50          | ~ (v1_tsep_1 @ X1 @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D))
% 0.20/0.50          | ~ (r1_tmap_1 @ X1 @ sk_A @ 
% 0.20/0.50               (k3_tmap_1 @ X0 @ sk_A @ sk_D @ X1 @ sk_E) @ X2)
% 0.20/0.50          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X2)
% 0.20/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.50          | (v2_struct_0 @ X1)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 0.20/0.50  thf('100', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50             (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_B)
% 0.20/0.50          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.50          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.50          | (v2_struct_0 @ sk_C)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.50          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.50          | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.50          | ~ (v1_tsep_1 @ sk_C @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_D @ sk_B)
% 0.20/0.50          | (v2_struct_0 @ sk_D)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['90', '99'])).
% 0.20/0.50  thf('101', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('102', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('103', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('104', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('105', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('106', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t35_borsuk_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_pre_topc @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( m1_pre_topc @ B @ A ) =>
% 0.20/0.50           ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.50  thf('107', plain,
% 0.20/0.50      (![X17 : $i, X18 : $i]:
% 0.20/0.50         (~ (m1_pre_topc @ X17 @ X18)
% 0.20/0.50          | (r1_tarski @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X18))
% 0.20/0.50          | ~ (l1_pre_topc @ X18))),
% 0.20/0.50      inference('cnf', [status(esa)], [t35_borsuk_1])).
% 0.20/0.50  thf('108', plain,
% 0.20/0.50      ((~ (l1_pre_topc @ sk_D)
% 0.20/0.50        | (r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.50  thf('109', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.50      inference('demod', [status(thm)], ['32', '33'])).
% 0.20/0.50  thf('110', plain,
% 0.20/0.50      ((r1_tarski @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D))),
% 0.20/0.50      inference('demod', [status(thm)], ['108', '109'])).
% 0.20/0.50  thf(t19_tsep_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( v1_tsep_1 @ B @ A ) & ( m1_pre_topc @ B @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.50               ( ( r1_tarski @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.50                 ( ( v1_tsep_1 @ B @ C ) & ( m1_pre_topc @ B @ C ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('111', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.50         (~ (v1_tsep_1 @ X13 @ X14)
% 0.20/0.50          | ~ (m1_pre_topc @ X13 @ X14)
% 0.20/0.50          | ~ (r1_tarski @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X15))
% 0.20/0.50          | (v1_tsep_1 @ X13 @ X15)
% 0.20/0.50          | ~ (m1_pre_topc @ X15 @ X14)
% 0.20/0.50          | (v2_struct_0 @ X15)
% 0.20/0.50          | ~ (l1_pre_topc @ X14)
% 0.20/0.50          | ~ (v2_pre_topc @ X14)
% 0.20/0.50          | (v2_struct_0 @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [t19_tsep_1])).
% 0.20/0.50  thf('112', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (v2_pre_topc @ X0)
% 0.20/0.50          | ~ (l1_pre_topc @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.50          | (v1_tsep_1 @ sk_C @ sk_D)
% 0.20/0.50          | ~ (m1_pre_topc @ sk_C @ X0)
% 0.20/0.50          | ~ (v1_tsep_1 @ sk_C @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['110', '111'])).
% 0.20/0.50  thf('113', plain,
% 0.20/0.50      ((~ (v1_tsep_1 @ sk_C @ sk_B)
% 0.20/0.50        | ~ (m1_pre_topc @ sk_C @ sk_B)
% 0.20/0.50        | (v1_tsep_1 @ sk_C @ sk_D)
% 0.20/0.50        | (v2_struct_0 @ sk_D)
% 0.20/0.50        | ~ (l1_pre_topc @ sk_B)
% 0.20/0.50        | ~ (v2_pre_topc @ sk_B)
% 0.20/0.50        | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['105', '112'])).
% 0.20/0.50  thf('114', plain, ((v1_tsep_1 @ sk_C @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('115', plain, ((m1_pre_topc @ sk_C @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('116', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('117', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('118', plain,
% 0.20/0.50      (((v1_tsep_1 @ sk_C @ sk_D) | (v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['113', '114', '115', '116', '117'])).
% 0.20/0.50  thf('119', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('120', plain, (((v2_struct_0 @ sk_B) | (v1_tsep_1 @ sk_C @ sk_D))),
% 0.20/0.50      inference('clc', [status(thm)], ['118', '119'])).
% 0.20/0.50  thf('121', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('122', plain, ((v1_tsep_1 @ sk_C @ sk_D)),
% 0.20/0.50      inference('clc', [status(thm)], ['120', '121'])).
% 0.20/0.50  thf('123', plain, ((m1_pre_topc @ sk_D @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('124', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r1_tmap_1 @ sk_C @ sk_A @ 
% 0.20/0.50             (k2_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_C) @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_B)
% 0.20/0.50          | (v2_struct_0 @ sk_C)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.50          | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D))
% 0.20/0.50          | (v2_struct_0 @ sk_D)
% 0.20/0.50          | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)],
% 0.20/0.50                ['100', '101', '102', '103', '104', '122', '123'])).
% 0.20/0.50  thf('125', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_D)
% 0.20/0.50        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))
% 0.20/0.50        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.20/0.50        | ~ (m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))
% 0.20/0.50        | (v2_struct_0 @ sk_C)
% 0.20/0.50        | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['89', '124'])).
% 0.20/0.50  thf('126', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_D))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('127', plain, ((m1_subset_1 @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.50      inference('demod', [status(thm)], ['54', '55'])).
% 0.20/0.50  thf('128', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_D)
% 0.20/0.50        | (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)
% 0.20/0.50        | (v2_struct_0 @ sk_C)
% 0.20/0.50        | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['125', '126', '127'])).
% 0.20/0.50  thf('129', plain,
% 0.20/0.50      ((~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))
% 0.20/0.50         <= (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)))),
% 0.20/0.50      inference('split', [status(esa)], ['52'])).
% 0.20/0.50  thf('130', plain, (~ ((r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F))),
% 0.20/0.50      inference('sat_resolution*', [status(thm)], ['53', '86'])).
% 0.20/0.50  thf('131', plain, (~ (r1_tmap_1 @ sk_D @ sk_A @ sk_E @ sk_F)),
% 0.20/0.50      inference('simpl_trail', [status(thm)], ['129', '130'])).
% 0.20/0.50  thf('132', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_B)
% 0.20/0.50        | (v2_struct_0 @ sk_C)
% 0.20/0.50        | (v2_struct_0 @ sk_D)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['128', '131'])).
% 0.20/0.50  thf('133', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('134', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['132', '133'])).
% 0.20/0.50  thf('135', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('136', plain, (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C))),
% 0.20/0.50      inference('clc', [status(thm)], ['134', '135'])).
% 0.20/0.50  thf('137', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('138', plain, ((v2_struct_0 @ sk_C)),
% 0.20/0.50      inference('clc', [status(thm)], ['136', '137'])).
% 0.20/0.50  thf('139', plain, ($false), inference('demod', [status(thm)], ['0', '138'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
