%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ocoWDQJPz6

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:10:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 193 expanded)
%              Number of leaves         :   27 (  70 expanded)
%              Depth                    :   17
%              Number of atoms          : 1168 (6962 expanded)
%              Number of equality atoms :   29 ( 111 expanded)
%              Maximal formula depth    :   24 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tmap_1_type,type,(
    k2_tmap_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_pre_topc_type,type,(
    m1_pre_topc: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_tmap_1_type,type,(
    k3_tmap_1: $i > $i > $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t75_tmap_1,conjecture,(
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
                     => ( ( m1_pre_topc @ C @ D )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) )
                           => ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                             => ( ( k7_relset_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ F )
                                = ( k7_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) )).

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
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ( ( m1_pre_topc @ C @ D )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) )
                             => ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) )
                               => ( ( k7_relset_1 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ E @ F )
                                  = ( k7_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t75_tmap_1])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_F @ ( u1_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t61_tmap_1,axiom,(
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
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) )
                       => ( ( k7_relset_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ E )
                          = ( k7_relset_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X13 )
      | ~ ( v2_pre_topc @ X13 )
      | ~ ( l1_pre_topc @ X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_2 @ X14 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) ) ) )
      | ~ ( r1_tarski @ X16 @ ( u1_struct_0 @ X17 ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X15 ) @ X14 @ X16 )
        = ( k7_relset_1 @ ( u1_struct_0 @ X17 ) @ ( u1_struct_0 @ X15 ) @ ( k2_tmap_1 @ X13 @ X15 @ X14 @ X17 ) @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_pre_topc @ X17 @ X13 )
      | ( v2_struct_0 @ X17 )
      | ~ ( l1_pre_topc @ X15 )
      | ~ ( v2_pre_topc @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t61_tmap_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ~ ( l1_pre_topc @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X1 )
        = ( k7_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ X1 ) )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( l1_pre_topc @ B ) ) ) )).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_pre_topc @ X2 @ X3 )
      | ( l1_pre_topc @ X2 )
      | ~ ( l1_pre_topc @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_pre_topc])).

thf('12',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( l1_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_pre_topc @ B @ A )
         => ( v2_pre_topc @ B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_pre_topc @ X0 @ X1 )
      | ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_pre_topc])).

thf('17',plain,
    ( ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ( v2_pre_topc @ sk_D ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_D ) ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X1 )
        = ( k7_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ X1 ) )
      | ~ ( r1_tarski @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['5','6','7','8','9','14','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ~ ( r1_tarski @ sk_F @ ( u1_struct_0 @ X0 ) )
      | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F )
        = ( k7_relset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 ) @ sk_F ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','21'])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F )
      = ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','22'])).

thf('24',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( ( k7_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F )
      = ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ( k7_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E ) @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_pre_topc @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_pre_topc @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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

thf('30',plain,(
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

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( m1_pre_topc @ sk_D @ X0 )
      | ( ( k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_pre_topc @ X1 @ sk_D )
      | ~ ( m1_pre_topc @ X1 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ sk_A )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','36'])).

thf('38',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_pre_topc @ X0 @ sk_A )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ~ ( m1_pre_topc @ sk_C @ sk_D )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','40'])).

thf('42',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ) ) ),
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
      ( ( v2_struct_0 @ sk_D )
      | ~ ( v2_pre_topc @ sk_D )
      | ~ ( l1_pre_topc @ sk_D )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ~ ( l1_pre_topc @ sk_B )
      | ~ ( v2_pre_topc @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v2_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('47',plain,(
    l1_pre_topc @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('48',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_pre_topc @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_D )
      | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0 )
        = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( m1_pre_topc @ X0 @ sk_D )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49','50','51'])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['42','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
      = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C )
    = ( k2_partfun1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( u1_struct_0 @ sk_C ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    m1_pre_topc @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['41','57','58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
      = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E )
    = ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ( k7_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F )
 != ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) @ ( k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C ) @ sk_F ) ),
    inference(demod,[status(thm)],['26','63'])).

thf('65',plain,
    ( ( ( k7_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F )
     != ( k7_relset_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F ) )
    | ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_C )
    | ( v2_struct_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( v2_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v2_struct_0 @ sk_C ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['0','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ocoWDQJPz6
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 37 iterations in 0.024s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(k2_tmap_1_type, type, k2_tmap_1: $i > $i > $i > $i > $i).
% 0.20/0.45  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.45  thf(m1_pre_topc_type, type, m1_pre_topc: $i > $i > $o).
% 0.20/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.45  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.45  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.45  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.20/0.45  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.20/0.45  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(k3_tmap_1_type, type, k3_tmap_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.45  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.45  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.20/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.45  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.45  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.45  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.45  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.45  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.45  thf(t75_tmap_1, conjecture,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.45       ( ![B:$i]:
% 0.20/0.45         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.45             ( l1_pre_topc @ B ) ) =>
% 0.20/0.45           ( ![C:$i]:
% 0.20/0.45             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.45               ( ![D:$i]:
% 0.20/0.45                 ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.45                   ( ![E:$i]:
% 0.20/0.45                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.45                         ( v1_funct_2 @
% 0.20/0.45                           E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.45                         ( m1_subset_1 @
% 0.20/0.45                           E @ 
% 0.20/0.45                           ( k1_zfmisc_1 @
% 0.20/0.45                             ( k2_zfmisc_1 @
% 0.20/0.45                               ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.45                       ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.45                         ( ![F:$i]:
% 0.20/0.45                           ( ( m1_subset_1 @
% 0.20/0.45                               F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.20/0.45                             ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.45                               ( ( k7_relset_1 @
% 0.20/0.45                                   ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.45                                   E @ F ) =
% 0.20/0.45                                 ( k7_relset_1 @
% 0.20/0.45                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.45                                   ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i]:
% 0.20/0.45        ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & 
% 0.20/0.45            ( l1_pre_topc @ A ) ) =>
% 0.20/0.45          ( ![B:$i]:
% 0.20/0.45            ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.45                ( l1_pre_topc @ B ) ) =>
% 0.20/0.45              ( ![C:$i]:
% 0.20/0.45                ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ A ) ) =>
% 0.20/0.45                  ( ![D:$i]:
% 0.20/0.45                    ( ( ( ~( v2_struct_0 @ D ) ) & ( m1_pre_topc @ D @ A ) ) =>
% 0.20/0.45                      ( ![E:$i]:
% 0.20/0.45                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.45                            ( v1_funct_2 @
% 0.20/0.45                              E @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.45                            ( m1_subset_1 @
% 0.20/0.45                              E @ 
% 0.20/0.45                              ( k1_zfmisc_1 @
% 0.20/0.45                                ( k2_zfmisc_1 @
% 0.20/0.45                                  ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.45                          ( ( m1_pre_topc @ C @ D ) =>
% 0.20/0.45                            ( ![F:$i]:
% 0.20/0.45                              ( ( m1_subset_1 @
% 0.20/0.45                                  F @ ( k1_zfmisc_1 @ ( u1_struct_0 @ D ) ) ) =>
% 0.20/0.45                                ( ( r1_tarski @ F @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.45                                  ( ( k7_relset_1 @
% 0.20/0.45                                      ( u1_struct_0 @ D ) @ 
% 0.20/0.45                                      ( u1_struct_0 @ B ) @ E @ F ) =
% 0.20/0.45                                    ( k7_relset_1 @
% 0.20/0.45                                      ( u1_struct_0 @ C ) @ 
% 0.20/0.45                                      ( u1_struct_0 @ B ) @ 
% 0.20/0.45                                      ( k3_tmap_1 @ A @ B @ D @ C @ E ) @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t75_tmap_1])).
% 0.20/0.45  thf('0', plain, (~ (v2_struct_0 @ sk_C)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('1', plain, ((r1_tarski @ sk_F @ (u1_struct_0 @ sk_C))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      ((m1_subset_1 @ sk_E @ 
% 0.20/0.45        (k1_zfmisc_1 @ 
% 0.20/0.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t61_tmap_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.45       ( ![B:$i]:
% 0.20/0.45         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.45             ( l1_pre_topc @ B ) ) =>
% 0.20/0.45           ( ![C:$i]:
% 0.20/0.45             ( ( ( ~( v2_struct_0 @ C ) ) & ( m1_pre_topc @ C @ B ) ) =>
% 0.20/0.45               ( ![D:$i]:
% 0.20/0.45                 ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.45                     ( v1_funct_2 @
% 0.20/0.45                       D @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) & 
% 0.20/0.45                     ( m1_subset_1 @
% 0.20/0.45                       D @ 
% 0.20/0.45                       ( k1_zfmisc_1 @
% 0.20/0.45                         ( k2_zfmisc_1 @
% 0.20/0.45                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) =>
% 0.20/0.45                   ( ![E:$i]:
% 0.20/0.45                     ( ( m1_subset_1 @
% 0.20/0.45                         E @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.45                       ( ( r1_tarski @ E @ ( u1_struct_0 @ C ) ) =>
% 0.20/0.45                         ( ( k7_relset_1 @
% 0.20/0.45                             ( u1_struct_0 @ B ) @ ( u1_struct_0 @ A ) @ D @ E ) =
% 0.20/0.45                           ( k7_relset_1 @
% 0.20/0.45                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ A ) @ 
% 0.20/0.45                             ( k2_tmap_1 @ B @ A @ D @ C ) @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.45  thf('4', plain,
% 0.20/0.45      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.45         ((v2_struct_0 @ X13)
% 0.20/0.45          | ~ (v2_pre_topc @ X13)
% 0.20/0.45          | ~ (l1_pre_topc @ X13)
% 0.20/0.45          | ~ (v1_funct_1 @ X14)
% 0.20/0.45          | ~ (v1_funct_2 @ X14 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X15))
% 0.20/0.45          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.45               (k1_zfmisc_1 @ 
% 0.20/0.45                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X15))))
% 0.20/0.45          | ~ (r1_tarski @ X16 @ (u1_struct_0 @ X17))
% 0.20/0.45          | ((k7_relset_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X15) @ X14 @ 
% 0.20/0.45              X16)
% 0.20/0.45              = (k7_relset_1 @ (u1_struct_0 @ X17) @ (u1_struct_0 @ X15) @ 
% 0.20/0.45                 (k2_tmap_1 @ X13 @ X15 @ X14 @ X17) @ X16))
% 0.20/0.45          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.20/0.45          | ~ (m1_pre_topc @ X17 @ X13)
% 0.20/0.45          | (v2_struct_0 @ X17)
% 0.20/0.45          | ~ (l1_pre_topc @ X15)
% 0.20/0.45          | ~ (v2_pre_topc @ X15)
% 0.20/0.45          | (v2_struct_0 @ X15))),
% 0.20/0.45      inference('cnf', [status(esa)], [t61_tmap_1])).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((v2_struct_0 @ sk_B)
% 0.20/0.45          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.45          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.45          | (v2_struct_0 @ X0)
% 0.20/0.45          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.45          | ((k7_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45              sk_E @ X1)
% 0.20/0.45              = (k7_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45                 (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ X1))
% 0.20/0.45          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.45          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.45          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.45          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.45          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.45          | (v2_struct_0 @ sk_D))),
% 0.20/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.45  thf('6', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('7', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('9', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('10', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(dt_m1_pre_topc, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( l1_pre_topc @ A ) =>
% 0.20/0.45       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( l1_pre_topc @ B ) ) ) ))).
% 0.20/0.45  thf('11', plain,
% 0.20/0.45      (![X2 : $i, X3 : $i]:
% 0.20/0.45         (~ (m1_pre_topc @ X2 @ X3) | (l1_pre_topc @ X2) | ~ (l1_pre_topc @ X3))),
% 0.20/0.45      inference('cnf', [status(esa)], [dt_m1_pre_topc])).
% 0.20/0.45  thf('12', plain, ((~ (l1_pre_topc @ sk_A) | (l1_pre_topc @ sk_D))),
% 0.20/0.45      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.45  thf('13', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('14', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.45      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.45  thf('15', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(cc1_pre_topc, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.45       ( ![B:$i]: ( ( m1_pre_topc @ B @ A ) => ( v2_pre_topc @ B ) ) ) ))).
% 0.20/0.45  thf('16', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (~ (m1_pre_topc @ X0 @ X1)
% 0.20/0.45          | (v2_pre_topc @ X0)
% 0.20/0.45          | ~ (l1_pre_topc @ X1)
% 0.20/0.45          | ~ (v2_pre_topc @ X1))),
% 0.20/0.45      inference('cnf', [status(esa)], [cc1_pre_topc])).
% 0.20/0.45  thf('17', plain,
% 0.20/0.45      ((~ (v2_pre_topc @ sk_A) | ~ (l1_pre_topc @ sk_A) | (v2_pre_topc @ sk_D))),
% 0.20/0.45      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.45  thf('18', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('19', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('20', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.45      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.45  thf('21', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((v2_struct_0 @ sk_B)
% 0.20/0.45          | (v2_struct_0 @ X0)
% 0.20/0.45          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.45          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_D)))
% 0.20/0.45          | ((k7_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45              sk_E @ X1)
% 0.20/0.45              = (k7_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45                 (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ X1))
% 0.20/0.45          | ~ (r1_tarski @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.45          | (v2_struct_0 @ sk_D))),
% 0.20/0.45      inference('demod', [status(thm)], ['5', '6', '7', '8', '9', '14', '20'])).
% 0.20/0.45  thf('22', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((v2_struct_0 @ sk_D)
% 0.20/0.45          | ~ (r1_tarski @ sk_F @ (u1_struct_0 @ X0))
% 0.20/0.45          | ((k7_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45              sk_E @ sk_F)
% 0.20/0.45              = (k7_relset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45                 (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0) @ sk_F))
% 0.20/0.45          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.45          | (v2_struct_0 @ X0)
% 0.20/0.45          | (v2_struct_0 @ sk_B))),
% 0.20/0.45      inference('sup-', [status(thm)], ['2', '21'])).
% 0.20/0.45  thf('23', plain,
% 0.20/0.45      (((v2_struct_0 @ sk_B)
% 0.20/0.45        | (v2_struct_0 @ sk_C)
% 0.20/0.45        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.45        | ((k7_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.45            sk_F)
% 0.20/0.45            = (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.20/0.45        | (v2_struct_0 @ sk_D))),
% 0.20/0.45      inference('sup-', [status(thm)], ['1', '22'])).
% 0.20/0.45  thf('24', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('25', plain,
% 0.20/0.45      (((v2_struct_0 @ sk_B)
% 0.20/0.45        | (v2_struct_0 @ sk_C)
% 0.20/0.45        | ((k7_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.45            sk_F)
% 0.20/0.45            = (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45               (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))
% 0.20/0.45        | (v2_struct_0 @ sk_D))),
% 0.20/0.45      inference('demod', [status(thm)], ['23', '24'])).
% 0.20/0.45  thf('26', plain,
% 0.20/0.45      (((k7_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.45         sk_F)
% 0.20/0.45         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45             (k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E) @ sk_F))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('27', plain, ((m1_pre_topc @ sk_C @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('28', plain, ((m1_pre_topc @ sk_D @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('29', plain,
% 0.20/0.45      ((m1_subset_1 @ sk_E @ 
% 0.20/0.45        (k1_zfmisc_1 @ 
% 0.20/0.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(d5_tmap_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.45       ( ![B:$i]:
% 0.20/0.45         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.45             ( l1_pre_topc @ B ) ) =>
% 0.20/0.45           ( ![C:$i]:
% 0.20/0.45             ( ( m1_pre_topc @ C @ A ) =>
% 0.20/0.45               ( ![D:$i]:
% 0.20/0.45                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.45                   ( ![E:$i]:
% 0.20/0.45                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.45                         ( v1_funct_2 @
% 0.20/0.45                           E @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.45                         ( m1_subset_1 @
% 0.20/0.45                           E @ 
% 0.20/0.45                           ( k1_zfmisc_1 @
% 0.20/0.45                             ( k2_zfmisc_1 @
% 0.20/0.45                               ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.45                       ( ( m1_pre_topc @ D @ C ) =>
% 0.20/0.45                         ( ( k3_tmap_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.45                           ( k2_partfun1 @
% 0.20/0.45                             ( u1_struct_0 @ C ) @ ( u1_struct_0 @ B ) @ E @ 
% 0.20/0.45                             ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.45  thf('30', plain,
% 0.20/0.45      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.45         ((v2_struct_0 @ X8)
% 0.20/0.45          | ~ (v2_pre_topc @ X8)
% 0.20/0.45          | ~ (l1_pre_topc @ X8)
% 0.20/0.45          | ~ (m1_pre_topc @ X9 @ X10)
% 0.20/0.45          | ~ (m1_pre_topc @ X9 @ X11)
% 0.20/0.45          | ((k3_tmap_1 @ X10 @ X8 @ X11 @ X9 @ X12)
% 0.20/0.45              = (k2_partfun1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8) @ 
% 0.20/0.45                 X12 @ (u1_struct_0 @ X9)))
% 0.20/0.45          | ~ (m1_subset_1 @ X12 @ 
% 0.20/0.45               (k1_zfmisc_1 @ 
% 0.20/0.45                (k2_zfmisc_1 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))))
% 0.20/0.45          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X11) @ (u1_struct_0 @ X8))
% 0.20/0.45          | ~ (v1_funct_1 @ X12)
% 0.20/0.45          | ~ (m1_pre_topc @ X11 @ X10)
% 0.20/0.45          | ~ (l1_pre_topc @ X10)
% 0.20/0.45          | ~ (v2_pre_topc @ X10)
% 0.20/0.45          | (v2_struct_0 @ X10))),
% 0.20/0.45      inference('cnf', [status(esa)], [d5_tmap_1])).
% 0.20/0.45  thf('31', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((v2_struct_0 @ X0)
% 0.20/0.45          | ~ (v2_pre_topc @ X0)
% 0.20/0.45          | ~ (l1_pre_topc @ X0)
% 0.20/0.45          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.45          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.45          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.45          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.20/0.45              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.45          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.45          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.45          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.45          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.45          | (v2_struct_0 @ sk_B))),
% 0.20/0.45      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.45  thf('32', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('33', plain,
% 0.20/0.45      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('34', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('35', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('36', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         ((v2_struct_0 @ X0)
% 0.20/0.45          | ~ (v2_pre_topc @ X0)
% 0.20/0.45          | ~ (l1_pre_topc @ X0)
% 0.20/0.45          | ~ (m1_pre_topc @ sk_D @ X0)
% 0.20/0.45          | ((k3_tmap_1 @ X0 @ sk_B @ sk_D @ X1 @ sk_E)
% 0.20/0.45              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45                 sk_E @ (u1_struct_0 @ X1)))
% 0.20/0.45          | ~ (m1_pre_topc @ X1 @ sk_D)
% 0.20/0.45          | ~ (m1_pre_topc @ X1 @ X0)
% 0.20/0.45          | (v2_struct_0 @ sk_B))),
% 0.20/0.45      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 0.20/0.45  thf('37', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((v2_struct_0 @ sk_B)
% 0.20/0.45          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.45          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.45          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.20/0.45              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.45          | ~ (l1_pre_topc @ sk_A)
% 0.20/0.45          | ~ (v2_pre_topc @ sk_A)
% 0.20/0.45          | (v2_struct_0 @ sk_A))),
% 0.20/0.45      inference('sup-', [status(thm)], ['28', '36'])).
% 0.20/0.45  thf('38', plain, ((l1_pre_topc @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('39', plain, ((v2_pre_topc @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('40', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((v2_struct_0 @ sk_B)
% 0.20/0.45          | ~ (m1_pre_topc @ X0 @ sk_A)
% 0.20/0.45          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.45          | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ X0 @ sk_E)
% 0.20/0.45              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.45          | (v2_struct_0 @ sk_A))),
% 0.20/0.45      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.20/0.45  thf('41', plain,
% 0.20/0.45      (((v2_struct_0 @ sk_A)
% 0.20/0.45        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.45            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45               sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.45        | ~ (m1_pre_topc @ sk_C @ sk_D)
% 0.20/0.45        | (v2_struct_0 @ sk_B))),
% 0.20/0.45      inference('sup-', [status(thm)], ['27', '40'])).
% 0.20/0.45  thf('42', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('43', plain,
% 0.20/0.45      ((m1_subset_1 @ sk_E @ 
% 0.20/0.45        (k1_zfmisc_1 @ 
% 0.20/0.45         (k2_zfmisc_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(d4_tmap_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( ( ~( v2_struct_0 @ A ) ) & ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.20/0.45       ( ![B:$i]:
% 0.20/0.45         ( ( ( ~( v2_struct_0 @ B ) ) & ( v2_pre_topc @ B ) & 
% 0.20/0.45             ( l1_pre_topc @ B ) ) =>
% 0.20/0.45           ( ![C:$i]:
% 0.20/0.45             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.45                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.45                 ( m1_subset_1 @
% 0.20/0.45                   C @ 
% 0.20/0.45                   ( k1_zfmisc_1 @
% 0.20/0.45                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.45               ( ![D:$i]:
% 0.20/0.45                 ( ( m1_pre_topc @ D @ A ) =>
% 0.20/0.45                   ( ( k2_tmap_1 @ A @ B @ C @ D ) =
% 0.20/0.45                     ( k2_partfun1 @
% 0.20/0.45                       ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ 
% 0.20/0.45                       ( u1_struct_0 @ D ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.45  thf('44', plain,
% 0.20/0.45      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.45         ((v2_struct_0 @ X4)
% 0.20/0.45          | ~ (v2_pre_topc @ X4)
% 0.20/0.45          | ~ (l1_pre_topc @ X4)
% 0.20/0.45          | ~ (m1_pre_topc @ X5 @ X6)
% 0.20/0.45          | ((k2_tmap_1 @ X6 @ X4 @ X7 @ X5)
% 0.20/0.45              = (k2_partfun1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4) @ X7 @ 
% 0.20/0.45                 (u1_struct_0 @ X5)))
% 0.20/0.45          | ~ (m1_subset_1 @ X7 @ 
% 0.20/0.45               (k1_zfmisc_1 @ 
% 0.20/0.45                (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))))
% 0.20/0.45          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X4))
% 0.20/0.45          | ~ (v1_funct_1 @ X7)
% 0.20/0.45          | ~ (l1_pre_topc @ X6)
% 0.20/0.45          | ~ (v2_pre_topc @ X6)
% 0.20/0.45          | (v2_struct_0 @ X6))),
% 0.20/0.45      inference('cnf', [status(esa)], [d4_tmap_1])).
% 0.20/0.45  thf('45', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((v2_struct_0 @ sk_D)
% 0.20/0.45          | ~ (v2_pre_topc @ sk_D)
% 0.20/0.45          | ~ (l1_pre_topc @ sk_D)
% 0.20/0.45          | ~ (v1_funct_1 @ sk_E)
% 0.20/0.45          | ~ (v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))
% 0.20/0.45          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.20/0.45              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.45          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.45          | ~ (l1_pre_topc @ sk_B)
% 0.20/0.45          | ~ (v2_pre_topc @ sk_B)
% 0.20/0.45          | (v2_struct_0 @ sk_B))),
% 0.20/0.45      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.45  thf('46', plain, ((v2_pre_topc @ sk_D)),
% 0.20/0.45      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.20/0.45  thf('47', plain, ((l1_pre_topc @ sk_D)),
% 0.20/0.45      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.45  thf('48', plain, ((v1_funct_1 @ sk_E)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('49', plain,
% 0.20/0.45      ((v1_funct_2 @ sk_E @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('50', plain, ((l1_pre_topc @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('51', plain, ((v2_pre_topc @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('52', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         ((v2_struct_0 @ sk_D)
% 0.20/0.45          | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ X0)
% 0.20/0.45              = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45                 sk_E @ (u1_struct_0 @ X0)))
% 0.20/0.45          | ~ (m1_pre_topc @ X0 @ sk_D)
% 0.20/0.45          | (v2_struct_0 @ sk_B))),
% 0.20/0.45      inference('demod', [status(thm)],
% 0.20/0.45                ['45', '46', '47', '48', '49', '50', '51'])).
% 0.20/0.45  thf('53', plain,
% 0.20/0.45      (((v2_struct_0 @ sk_B)
% 0.20/0.45        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.20/0.45            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45               sk_E @ (u1_struct_0 @ sk_C)))
% 0.20/0.45        | (v2_struct_0 @ sk_D))),
% 0.20/0.45      inference('sup-', [status(thm)], ['42', '52'])).
% 0.20/0.45  thf('54', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('55', plain,
% 0.20/0.45      (((v2_struct_0 @ sk_D)
% 0.20/0.45        | ((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.20/0.45            = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45               sk_E @ (u1_struct_0 @ sk_C))))),
% 0.20/0.45      inference('clc', [status(thm)], ['53', '54'])).
% 0.20/0.45  thf('56', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('57', plain,
% 0.20/0.45      (((k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)
% 0.20/0.45         = (k2_partfun1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.45            (u1_struct_0 @ sk_C)))),
% 0.20/0.45      inference('clc', [status(thm)], ['55', '56'])).
% 0.20/0.45  thf('58', plain, ((m1_pre_topc @ sk_C @ sk_D)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('59', plain,
% 0.20/0.45      (((v2_struct_0 @ sk_A)
% 0.20/0.45        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.45            = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))
% 0.20/0.45        | (v2_struct_0 @ sk_B))),
% 0.20/0.45      inference('demod', [status(thm)], ['41', '57', '58'])).
% 0.20/0.45  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('61', plain,
% 0.20/0.45      (((v2_struct_0 @ sk_B)
% 0.20/0.45        | ((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.45            = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C)))),
% 0.20/0.45      inference('clc', [status(thm)], ['59', '60'])).
% 0.20/0.45  thf('62', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('63', plain,
% 0.20/0.45      (((k3_tmap_1 @ sk_A @ sk_B @ sk_D @ sk_C @ sk_E)
% 0.20/0.45         = (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C))),
% 0.20/0.45      inference('clc', [status(thm)], ['61', '62'])).
% 0.20/0.45  thf('64', plain,
% 0.20/0.45      (((k7_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.45         sk_F)
% 0.20/0.45         != (k7_relset_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45             (k2_tmap_1 @ sk_D @ sk_B @ sk_E @ sk_C) @ sk_F))),
% 0.20/0.45      inference('demod', [status(thm)], ['26', '63'])).
% 0.20/0.45  thf('65', plain,
% 0.20/0.45      ((((k7_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ sk_E @ 
% 0.20/0.45          sk_F)
% 0.20/0.45          != (k7_relset_1 @ (u1_struct_0 @ sk_D) @ (u1_struct_0 @ sk_B) @ 
% 0.20/0.45              sk_E @ sk_F))
% 0.20/0.45        | (v2_struct_0 @ sk_D)
% 0.20/0.45        | (v2_struct_0 @ sk_C)
% 0.20/0.45        | (v2_struct_0 @ sk_B))),
% 0.20/0.45      inference('sup-', [status(thm)], ['25', '64'])).
% 0.20/0.45  thf('66', plain,
% 0.20/0.45      (((v2_struct_0 @ sk_B) | (v2_struct_0 @ sk_C) | (v2_struct_0 @ sk_D))),
% 0.20/0.45      inference('simplify', [status(thm)], ['65'])).
% 0.20/0.45  thf('67', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('68', plain, (((v2_struct_0 @ sk_D) | (v2_struct_0 @ sk_C))),
% 0.20/0.45      inference('clc', [status(thm)], ['66', '67'])).
% 0.20/0.45  thf('69', plain, (~ (v2_struct_0 @ sk_D)),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf('70', plain, ((v2_struct_0 @ sk_C)),
% 0.20/0.45      inference('clc', [status(thm)], ['68', '69'])).
% 0.20/0.45  thf('71', plain, ($false), inference('demod', [status(thm)], ['0', '70'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
