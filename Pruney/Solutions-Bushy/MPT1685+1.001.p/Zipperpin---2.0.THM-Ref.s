%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1685+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xHSCATivj7

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:04 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  439 (22084 expanded)
%              Number of leaves         :   46 (5972 expanded)
%              Depth                    :   46
%              Number of atoms          : 5292 (948771 expanded)
%              Number of equality atoms :  218 (35614 expanded)
%              Maximal formula depth    :   27 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_H_type,type,(
    sk_H: $i )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_yellow_0_type,type,(
    k2_yellow_0: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_funct_2_type,type,(
    r1_funct_2: $i > $i > $i > $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r2_yellow_0_type,type,(
    r2_yellow_0: $i > $i > $o )).

thf(r4_waybel_0_type,type,(
    r4_waybel_0: $i > $i > $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r3_waybel_0_type,type,(
    r3_waybel_0: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(t65_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_orders_2 @ B ) )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( l1_orders_2 @ C ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( l1_orders_2 @ D ) )
                 => ( ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
                        = ( g1_orders_2 @ ( u1_struct_0 @ C ) @ ( u1_orders_2 @ C ) ) )
                      & ( ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) )
                        = ( g1_orders_2 @ ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) ) ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) )
                           => ( ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) @ E @ F )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                                 => ! [H: $i] :
                                      ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                                     => ( ( G = H )
                                       => ( ( ( r4_waybel_0 @ A @ B @ E @ G )
                                           => ( r4_waybel_0 @ C @ D @ F @ H ) )
                                          & ( ( r3_waybel_0 @ A @ B @ E @ G )
                                           => ( r3_waybel_0 @ C @ D @ F @ H ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_orders_2 @ B ) )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( l1_orders_2 @ C ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( l1_orders_2 @ D ) )
                   => ( ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
                          = ( g1_orders_2 @ ( u1_struct_0 @ C ) @ ( u1_orders_2 @ C ) ) )
                        & ( ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) )
                          = ( g1_orders_2 @ ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) ) ) )
                     => ! [E: $i] :
                          ( ( ( v1_funct_1 @ E )
                            & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                         => ! [F: $i] :
                              ( ( ( v1_funct_1 @ F )
                                & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) )
                                & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) )
                             => ( ( r1_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) @ E @ F )
                               => ! [G: $i] :
                                    ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                                   => ! [H: $i] :
                                        ( ( m1_subset_1 @ H @ ( k1_zfmisc_1 @ ( u1_struct_0 @ C ) ) )
                                       => ( ( G = H )
                                         => ( ( ( r4_waybel_0 @ A @ B @ E @ G )
                                             => ( r4_waybel_0 @ C @ D @ F @ H ) )
                                            & ( ( r3_waybel_0 @ A @ B @ E @ G )
                                             => ( r3_waybel_0 @ C @ D @ F @ H ) ) ) ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t65_waybel_0])).

thf('0',plain,
    ( ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G )
    | ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G )
    | ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_orders_2 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( ( g1_orders_2 @ X17 @ X18 )
       != ( g1_orders_2 @ X15 @ X16 ) )
      | ( X18 = X16 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_D )
        = X0 )
      | ~ ( l1_orders_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    l1_orders_2 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_D )
        = X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( u1_orders_2 @ sk_D )
    = ( u1_orders_2 @ sk_B ) ),
    inference(eq_res,[status(thm)],['10'])).

thf('12',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('13',plain,
    ( ( m1_subset_1 @ ( u1_orders_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_D ) ) ) )
    | ~ ( l1_orders_2 @ sk_D ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    l1_orders_2 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ ( u1_orders_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_D ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( ( g1_orders_2 @ X17 @ X18 )
       != ( g1_orders_2 @ X15 @ X16 ) )
      | ( X17 = X15 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_D )
        = X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_orders_2 @ sk_B ) )
       != ( g1_orders_2 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_orders_2 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( u1_orders_2 @ sk_D )
    = ( u1_orders_2 @ sk_B ) ),
    inference(eq_res,[status(thm)],['10'])).

thf('20',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_D ) @ ( u1_orders_2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_D )
        = X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
       != ( g1_orders_2 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['21'])).

thf('23',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_C )
        = X0 )
      | ~ ( l1_orders_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_C )
        = X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( u1_orders_2 @ sk_C )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('29',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X13 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X13 ) ) ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('30',plain,
    ( ( m1_subset_1 @ ( u1_orders_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ) )
    | ~ ( l1_orders_2 @ sk_C ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ ( u1_orders_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( ( g1_orders_2 @ X17 @ X18 )
       != ( g1_orders_2 @ X15 @ X16 ) )
      | ( X17 = X15 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_C )
        = X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( u1_orders_2 @ sk_C )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('37',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_C )
        = X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['38'])).

thf(d31_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_orders_2 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( r4_waybel_0 @ A @ B @ C @ D )
                  <=> ( ( r1_yellow_0 @ A @ D )
                     => ( ( r1_yellow_0 @ B @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) )
                        & ( ( k1_yellow_0 @ B @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) )
                          = ( k3_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k1_yellow_0 @ A @ D ) ) ) ) ) ) ) ) ) ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( r1_yellow_0 @ X6 @ X5 )
      | ( r4_waybel_0 @ X6 @ X4 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d31_waybel_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_orders_2 @ sk_C )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_waybel_0 @ sk_C @ X0 @ X1 @ X2 )
      | ( r1_yellow_0 @ sk_C @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('44',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ( r4_waybel_0 @ sk_C @ X0 @ X1 @ X2 )
      | ( r1_yellow_0 @ sk_C @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['41','42','43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_orders_2 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_C @ X1 )
      | ( r4_waybel_0 @ sk_C @ sk_D @ X0 @ X1 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','45'])).

thf('47',plain,(
    l1_orders_2 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['21'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_C @ X1 )
      | ( r4_waybel_0 @ sk_C @ sk_D @ X0 @ X1 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ( r4_waybel_0 @ sk_C @ sk_D @ sk_E @ X0 )
      | ( r1_yellow_0 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( r4_waybel_0 @ sk_C @ sk_D @ sk_E @ X0 )
      | ( r1_yellow_0 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( r1_yellow_0 @ sk_C @ sk_G )
    | ( r4_waybel_0 @ sk_C @ sk_D @ sk_E @ sk_G )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','53'])).

thf('55',plain,
    ( ~ ( r4_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
    | ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ~ ( r4_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
   <= ~ ( r4_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H ) ),
    inference(split,[status(esa)],['55'])).

thf('57',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ~ ( r4_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_G )
   <= ~ ( r4_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) @ sk_E @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('61',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D ) @ sk_E @ sk_F ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['21'])).

thf('63',plain,(
    r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_F ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ D )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ A @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ C @ D )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( r1_funct_2 @ A @ B @ C @ D @ E @ F )
      <=> ( E = F ) ) ) )).

thf('65',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X29 )
      | ~ ( v1_funct_1 @ X27 )
      | ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X29 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X30 ) ) )
      | ( X27 = X31 )
      | ~ ( r1_funct_2 @ X28 @ X29 @ X32 @ X30 @ X27 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_funct_2])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X2 @ X1 @ sk_E @ X0 )
      | ( sk_E = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( sk_E = sk_F ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('74',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['21'])).

thf('76',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('79',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['21'])).

thf('81',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( sk_E = sk_F ) ),
    inference(demod,[status(thm)],['70','71','76','81'])).

thf('83',plain,
    ( ( sk_E = sk_F )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['21'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('85',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('86',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_D )
    | ~ ( l1_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_orders_2 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('88',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('89',plain,(
    l1_struct_0 @ sk_D ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_D ) ),
    inference(demod,[status(thm)],['86','89'])).

thf('91',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['90','91'])).

thf('93',plain,(
    sk_E = sk_F ),
    inference(clc,[status(thm)],['83','92'])).

thf('94',plain,
    ( ~ ( r4_waybel_0 @ sk_C @ sk_D @ sk_E @ sk_G )
   <= ~ ( r4_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H ) ),
    inference(demod,[status(thm)],['58','93'])).

thf('95',plain,
    ( ~ ( r4_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
    | ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H ) ),
    inference(split,[status(esa)],['55'])).

thf('96',plain,
    ( ~ ( r4_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
    | ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G )
    | ~ ( r4_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H ) ),
    inference(split,[status(esa)],['96'])).

thf('98',plain,(
    m1_subset_1 @ sk_H @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d30_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_orders_2 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ( ( r3_waybel_0 @ A @ B @ C @ D )
                  <=> ( ( r2_yellow_0 @ A @ D )
                     => ( ( r2_yellow_0 @ B @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) )
                        & ( ( k2_yellow_0 @ B @ ( k7_relset_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ D ) )
                          = ( k3_funct_2 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) @ C @ ( k2_yellow_0 @ A @ D ) ) ) ) ) ) ) ) ) ) )).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( r2_yellow_0 @ X2 @ X1 )
      | ( r3_waybel_0 @ X2 @ X0 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( l1_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d30_waybel_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ~ ( l1_orders_2 @ sk_C )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
      | ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ X0 )
      | ( r2_yellow_0 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( l1_orders_2 @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    l1_orders_2 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_C )
      | ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ X0 )
      | ( r2_yellow_0 @ sk_C @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( r2_yellow_0 @ sk_C @ sk_G )
    | ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_G )
    | ( v2_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['100','108'])).

thf('110',plain,
    ( ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
   <= ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H ) ),
    inference(split,[status(esa)],['55'])).

thf('111',plain,(
    sk_G = sk_H ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,
    ( ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_G )
   <= ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r2_yellow_0 @ sk_C @ sk_G )
      | ( v2_struct_0 @ sk_D ) )
   <= ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H ) ),
    inference('sup-',[status(thm)],['109','112'])).

thf('114',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( r2_yellow_0 @ sk_C @ sk_G ) )
   <= ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H ) ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( r2_yellow_0 @ sk_C @ sk_G )
   <= ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['38'])).

thf(t14_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
              = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
           => ! [C: $i] :
                ( ( ( r2_yellow_0 @ A @ C )
                 => ( r2_yellow_0 @ B @ C ) )
                & ( ( r1_yellow_0 @ A @ C )
                 => ( r1_yellow_0 @ B @ C ) ) ) ) ) ) )).

thf('119',plain,(
    ! [X33: $i,X34: $i,X36: $i] :
      ( ~ ( l1_orders_2 @ X33 )
      | ~ ( r2_yellow_0 @ X34 @ X36 )
      | ( r2_yellow_0 @ X33 @ X36 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X34 ) @ ( u1_orders_2 @ X34 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X33 ) @ ( u1_orders_2 @ X33 ) ) )
      | ~ ( l1_orders_2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_0])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_C ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ sk_C )
      | ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( r2_yellow_0 @ sk_C @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( u1_orders_2 @ sk_C )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('122',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( r2_yellow_0 @ sk_C @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r2_yellow_0 @ sk_C @ X0 )
      | ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference(eq_res,[status(thm)],['123'])).

thf('125',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( r2_yellow_0 @ sk_C @ X0 )
      | ( r2_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_G )
   <= ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H ) ),
    inference('sup-',[status(thm)],['117','126'])).

thf('128',plain,
    ( ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G )
   <= ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['96'])).

thf('129',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( r3_waybel_0 @ X2 @ X0 @ X3 @ X1 )
      | ( r2_yellow_0 @ X0 @ ( k7_relset_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X3 @ X1 ) )
      | ~ ( r2_yellow_0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( l1_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d30_waybel_0])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_yellow_0 @ sk_A @ X0 )
      | ( r2_yellow_0 @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 ) )
      | ~ ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_yellow_0 @ sk_A @ X0 )
      | ( r2_yellow_0 @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 ) )
      | ~ ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['131','132','133','134','135'])).

thf('137',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('138',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k7_relset_1 @ X24 @ X25 @ X23 @ X26 )
        = ( k9_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_yellow_0 @ sk_A @ X0 )
      | ( r2_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ X0 ) )
      | ~ ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['136','139'])).

thf('141',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r2_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
      | ~ ( r2_yellow_0 @ sk_A @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['128','140'])).

thf('142',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r2_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
      | ~ ( r2_yellow_0 @ sk_A @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
      & ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ) ),
    inference('sup-',[status(thm)],['127','143'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r2_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) ) )
   <= ( ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
      & ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ) ),
    inference(clc,[status(thm)],['144','145'])).

thf('147',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( r2_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
   <= ( ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
      & ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['21'])).

thf('150',plain,(
    ! [X33: $i,X34: $i,X36: $i] :
      ( ~ ( l1_orders_2 @ X33 )
      | ~ ( r2_yellow_0 @ X34 @ X36 )
      | ( r2_yellow_0 @ X33 @ X36 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X34 ) @ ( u1_orders_2 @ X34 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X33 ) @ ( u1_orders_2 @ X33 ) ) )
      | ~ ( l1_orders_2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_0])).

thf('151',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_D ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_yellow_0 @ sk_D @ X1 )
      | ~ ( r2_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( u1_orders_2 @ sk_D )
    = ( u1_orders_2 @ sk_B ) ),
    inference(eq_res,[status(thm)],['10'])).

thf('153',plain,(
    l1_orders_2 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_yellow_0 @ sk_D @ X1 )
      | ~ ( r2_yellow_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['151','152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ~ ( r2_yellow_0 @ sk_B @ X0 )
      | ( r2_yellow_0 @ sk_D @ X0 )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference(eq_res,[status(thm)],['154'])).

thf('156',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( r2_yellow_0 @ sk_B @ X0 )
      | ( r2_yellow_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['155','156'])).

thf('158',plain,
    ( ( r2_yellow_0 @ sk_D @ ( k9_relat_1 @ sk_E @ sk_G ) )
   <= ( ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
      & ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ) ),
    inference('sup-',[status(thm)],['148','157'])).

thf('159',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k7_relset_1 @ X24 @ X25 @ X23 @ X26 )
        = ( k9_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) @ sk_F @ X0 )
      = ( k9_relat_1 @ sk_F @ X0 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ( ( k2_yellow_0 @ X0 @ ( k7_relset_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X3 @ X1 ) )
       != ( k3_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X3 @ ( k2_yellow_0 @ X2 @ X1 ) ) )
      | ~ ( r2_yellow_0 @ X0 @ ( k7_relset_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X3 @ X1 ) )
      | ( r3_waybel_0 @ X2 @ X0 @ X3 @ X1 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( l1_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d30_waybel_0])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( ( k2_yellow_0 @ sk_D @ ( k9_relat_1 @ sk_F @ X0 ) )
       != ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) @ sk_F @ ( k2_yellow_0 @ sk_C @ X0 ) ) )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_orders_2 @ sk_C )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) )
      | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ) )
      | ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ X0 )
      | ~ ( r2_yellow_0 @ sk_D @ ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) @ sk_F @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( l1_orders_2 @ sk_D )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_2 @ sk_F @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) @ sk_F @ X0 )
      = ( k9_relat_1 @ sk_F @ X0 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('169',plain,(
    l1_orders_2 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( ( k2_yellow_0 @ sk_D @ ( k9_relat_1 @ sk_F @ X0 ) )
       != ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D ) @ sk_F @ ( k2_yellow_0 @ sk_C @ X0 ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ X0 )
      | ~ ( r2_yellow_0 @ sk_D @ ( k9_relat_1 @ sk_F @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['163','164','165','166','167','168','169'])).

thf('171',plain,(
    sk_E = sk_F ),
    inference(clc,[status(thm)],['83','92'])).

thf('172',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('173',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['21'])).

thf('174',plain,(
    sk_E = sk_F ),
    inference(clc,[status(thm)],['83','92'])).

thf('175',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['38'])).

thf(dt_k2_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k2_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('176',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_yellow_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['175','176'])).

thf('178',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_yellow_0 @ sk_C @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('181',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ X20 )
      | ( ( k3_funct_2 @ X20 @ X21 @ X19 @ X22 )
        = ( k1_funct_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('187',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('188',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( l1_struct_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('191',plain,(
    l1_struct_0 @ sk_C ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,
    ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_C ) ),
    inference(demod,[status(thm)],['188','191'])).

thf('193',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    ~ ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) ) ) ),
    inference(clc,[status(thm)],['185','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_yellow_0 @ sk_C @ X0 ) )
      = ( k1_funct_1 @ sk_E @ ( k2_yellow_0 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['179','195'])).

thf('197',plain,(
    sk_E = sk_F ),
    inference(clc,[status(thm)],['83','92'])).

thf('198',plain,(
    sk_E = sk_F ),
    inference(clc,[status(thm)],['83','92'])).

thf('199',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('200',plain,(
    ! [X0: $i] :
      ( ( ( k2_yellow_0 @ sk_D @ ( k9_relat_1 @ sk_E @ X0 ) )
       != ( k1_funct_1 @ sk_E @ ( k2_yellow_0 @ sk_C @ X0 ) ) )
      | ( v2_struct_0 @ sk_C )
      | ( r3_waybel_0 @ sk_C @ sk_D @ sk_E @ X0 )
      | ~ ( r2_yellow_0 @ sk_D @ ( k9_relat_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['170','171','172','173','174','196','197','198','199'])).

thf('201',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r3_waybel_0 @ sk_C @ sk_D @ sk_E @ sk_G )
      | ( v2_struct_0 @ sk_C )
      | ( ( k2_yellow_0 @ sk_D @ ( k9_relat_1 @ sk_E @ sk_G ) )
       != ( k1_funct_1 @ sk_E @ ( k2_yellow_0 @ sk_C @ sk_G ) ) ) )
   <= ( ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
      & ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ) ),
    inference('sup-',[status(thm)],['158','200'])).

thf('202',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( r3_waybel_0 @ sk_C @ sk_D @ sk_E @ sk_G )
      | ( v2_struct_0 @ sk_C )
      | ( ( k2_yellow_0 @ sk_D @ ( k9_relat_1 @ sk_E @ sk_G ) )
       != ( k1_funct_1 @ sk_E @ ( k2_yellow_0 @ sk_C @ sk_G ) ) ) )
   <= ( ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
      & ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ) ),
    inference(demod,[status(thm)],['201','202'])).

thf('204',plain,
    ( ( r2_yellow_0 @ sk_D @ ( k9_relat_1 @ sk_E @ sk_G ) )
   <= ( ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
      & ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ) ),
    inference('sup-',[status(thm)],['148','157'])).

thf('205',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['21'])).

thf(t27_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
              = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
           => ! [C: $i] :
                ( ( r2_yellow_0 @ A @ C )
               => ( ( k2_yellow_0 @ A @ C )
                  = ( k2_yellow_0 @ B @ C ) ) ) ) ) ) )).

thf('206',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( l1_orders_2 @ X40 )
      | ( ( k2_yellow_0 @ X42 @ X41 )
        = ( k2_yellow_0 @ X40 @ X41 ) )
      | ~ ( r2_yellow_0 @ X42 @ X41 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X42 ) @ ( u1_orders_2 @ X42 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X40 ) @ ( u1_orders_2 @ X40 ) ) )
      | ~ ( l1_orders_2 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow_0])).

thf('207',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_D ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ sk_D )
      | ~ ( r2_yellow_0 @ sk_D @ X1 )
      | ( ( k2_yellow_0 @ sk_D @ X1 )
        = ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['205','206'])).

thf('208',plain,
    ( ( u1_orders_2 @ sk_D )
    = ( u1_orders_2 @ sk_B ) ),
    inference(eq_res,[status(thm)],['10'])).

thf('209',plain,(
    l1_orders_2 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( r2_yellow_0 @ sk_D @ X1 )
      | ( ( k2_yellow_0 @ sk_D @ X1 )
        = ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['207','208','209'])).

thf('211',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_B )
      | ( ( k2_yellow_0 @ sk_D @ X0 )
        = ( k2_yellow_0 @ sk_B @ X0 ) )
      | ~ ( r2_yellow_0 @ sk_D @ X0 ) ) ),
    inference(eq_res,[status(thm)],['210'])).

thf('212',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    ! [X0: $i] :
      ( ( ( k2_yellow_0 @ sk_D @ X0 )
        = ( k2_yellow_0 @ sk_B @ X0 ) )
      | ~ ( r2_yellow_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['211','212'])).

thf('214',plain,
    ( ( ( k2_yellow_0 @ sk_D @ ( k9_relat_1 @ sk_E @ sk_G ) )
      = ( k2_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) ) )
   <= ( ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
      & ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ) ),
    inference('sup-',[status(thm)],['204','213'])).

thf('215',plain,
    ( ( r2_yellow_0 @ sk_C @ sk_G )
   <= ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('216',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('217',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( l1_orders_2 @ X40 )
      | ( ( k2_yellow_0 @ X42 @ X41 )
        = ( k2_yellow_0 @ X40 @ X41 ) )
      | ~ ( r2_yellow_0 @ X42 @ X41 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X42 ) @ ( u1_orders_2 @ X42 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X40 ) @ ( u1_orders_2 @ X40 ) ) )
      | ~ ( l1_orders_2 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t27_yellow_0])).

thf('218',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_C ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ sk_C )
      | ~ ( r2_yellow_0 @ sk_C @ X1 )
      | ( ( k2_yellow_0 @ sk_C @ X1 )
        = ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['216','217'])).

thf('219',plain,
    ( ( u1_orders_2 @ sk_C )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('220',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( r2_yellow_0 @ sk_C @ X1 )
      | ( ( k2_yellow_0 @ sk_C @ X1 )
        = ( k2_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['218','219','220'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( ( k2_yellow_0 @ sk_C @ X0 )
        = ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r2_yellow_0 @ sk_C @ X0 ) ) ),
    inference(eq_res,[status(thm)],['221'])).

thf('223',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( ( k2_yellow_0 @ sk_C @ X0 )
        = ( k2_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r2_yellow_0 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['222','223'])).

thf('225',plain,
    ( ( ( k2_yellow_0 @ sk_C @ sk_G )
      = ( k2_yellow_0 @ sk_A @ sk_G ) )
   <= ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H ) ),
    inference('sup-',[status(thm)],['215','224'])).

thf('226',plain,
    ( ( r2_yellow_0 @ sk_A @ sk_G )
   <= ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H ) ),
    inference('sup-',[status(thm)],['117','126'])).

thf('227',plain,
    ( ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G )
   <= ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['96'])).

thf('228',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X2 ) ) )
      | ~ ( r3_waybel_0 @ X2 @ X0 @ X3 @ X1 )
      | ( ( k2_yellow_0 @ X0 @ ( k7_relset_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X3 @ X1 ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) @ X3 @ ( k2_yellow_0 @ X2 @ X1 ) ) )
      | ~ ( r2_yellow_0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ X3 @ ( u1_struct_0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( l1_orders_2 @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d30_waybel_0])).

thf('230',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r2_yellow_0 @ sk_A @ X0 )
      | ( ( k2_yellow_0 @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_yellow_0 @ sk_A @ X0 ) ) )
      | ~ ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('233',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('234',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('235',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_yellow_0 @ sk_A @ X0 )
      | ( ( k2_yellow_0 @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_yellow_0 @ sk_A @ X0 ) ) )
      | ~ ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['230','231','232','233','234'])).

thf('236',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('237',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ( m1_subset_1 @ ( k2_yellow_0 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_0])).

thf('238',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) ) ) ),
    inference(clc,[status(thm)],['185','194'])).

thf('239',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_yellow_0 @ sk_A @ X0 ) )
        = ( k1_funct_1 @ sk_E @ ( k2_yellow_0 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['237','238'])).

thf('240',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('241',plain,(
    ! [X0: $i] :
      ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k2_yellow_0 @ sk_A @ X0 ) )
      = ( k1_funct_1 @ sk_E @ ( k2_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['239','240'])).

thf('242',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_yellow_0 @ sk_A @ X0 )
      | ( ( k2_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ X0 ) )
        = ( k1_funct_1 @ sk_E @ ( k2_yellow_0 @ sk_A @ X0 ) ) )
      | ~ ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['235','236','241'])).

thf('243',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k2_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
        = ( k1_funct_1 @ sk_E @ ( k2_yellow_0 @ sk_A @ sk_G ) ) )
      | ~ ( r2_yellow_0 @ sk_A @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['227','242'])).

thf('244',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( ( k2_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
        = ( k1_funct_1 @ sk_E @ ( k2_yellow_0 @ sk_A @ sk_G ) ) )
      | ~ ( r2_yellow_0 @ sk_A @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['243','244'])).

thf('246',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k2_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
        = ( k1_funct_1 @ sk_E @ ( k2_yellow_0 @ sk_A @ sk_G ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
      & ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ) ),
    inference('sup-',[status(thm)],['226','245'])).

thf('247',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('248',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( ( k2_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
        = ( k1_funct_1 @ sk_E @ ( k2_yellow_0 @ sk_A @ sk_G ) ) ) )
   <= ( ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
      & ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ) ),
    inference(clc,[status(thm)],['246','247'])).

thf('249',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('250',plain,
    ( ( ( k2_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
      = ( k1_funct_1 @ sk_E @ ( k2_yellow_0 @ sk_A @ sk_G ) ) )
   <= ( ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
      & ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ) ),
    inference(clc,[status(thm)],['248','249'])).

thf('251',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( r3_waybel_0 @ sk_C @ sk_D @ sk_E @ sk_G )
      | ( v2_struct_0 @ sk_C )
      | ( ( k2_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
       != ( k2_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) ) ) )
   <= ( ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
      & ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ) ),
    inference(demod,[status(thm)],['203','214','225','250'])).

thf('252',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r3_waybel_0 @ sk_C @ sk_D @ sk_E @ sk_G )
      | ( v2_struct_0 @ sk_D ) )
   <= ( ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
      & ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ) ),
    inference(simplify,[status(thm)],['251'])).

thf('253',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('254',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( r3_waybel_0 @ sk_C @ sk_D @ sk_E @ sk_G ) )
   <= ( ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
      & ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ) ),
    inference(clc,[status(thm)],['252','253'])).

thf('255',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('256',plain,
    ( ( r3_waybel_0 @ sk_C @ sk_D @ sk_E @ sk_G )
   <= ( ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
      & ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ) ),
    inference(clc,[status(thm)],['254','255'])).

thf('257',plain,(
    sk_E = sk_F ),
    inference(clc,[status(thm)],['83','92'])).

thf('258',plain,
    ( ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_G )
   <= ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('259',plain,
    ( ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_E @ sk_G )
   <= ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H ) ),
    inference('sup-',[status(thm)],['257','258'])).

thf('260',plain,
    ( ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
    | ~ ( r3_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['256','259'])).

thf('261',plain,(
    ~ ( r4_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H ) ),
    inference('sat_resolution*',[status(thm)],['95','97','260'])).

thf('262',plain,(
    ~ ( r4_waybel_0 @ sk_C @ sk_D @ sk_E @ sk_G ) ),
    inference(simpl_trail,[status(thm)],['94','261'])).

thf('263',plain,
    ( ( v2_struct_0 @ sk_C )
    | ( r1_yellow_0 @ sk_C @ sk_G )
    | ( v2_struct_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['54','262'])).

thf('264',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,
    ( ( v2_struct_0 @ sk_D )
    | ( r1_yellow_0 @ sk_C @ sk_G ) ),
    inference(clc,[status(thm)],['263','264'])).

thf('266',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('267',plain,(
    r1_yellow_0 @ sk_C @ sk_G ),
    inference(clc,[status(thm)],['265','266'])).

thf('268',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('269',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( l1_orders_2 @ X33 )
      | ~ ( r1_yellow_0 @ X34 @ X35 )
      | ( r1_yellow_0 @ X33 @ X35 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X34 ) @ ( u1_orders_2 @ X34 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X33 ) @ ( u1_orders_2 @ X33 ) ) )
      | ~ ( l1_orders_2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_0])).

thf('270',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_C ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ sk_C )
      | ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r1_yellow_0 @ sk_C @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['268','269'])).

thf('271',plain,
    ( ( u1_orders_2 @ sk_C )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('272',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('273',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( r1_yellow_0 @ sk_C @ X1 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['270','271','272'])).

thf('274',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_C @ X0 )
      | ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(eq_res,[status(thm)],['273'])).

thf('275',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('276',plain,(
    ! [X0: $i] :
      ( ~ ( r1_yellow_0 @ sk_C @ X0 )
      | ( r1_yellow_0 @ sk_A @ X0 ) ) ),
    inference(demod,[status(thm)],['274','275'])).

thf('277',plain,(
    r1_yellow_0 @ sk_A @ sk_G ),
    inference('sup-',[status(thm)],['267','276'])).

thf('278',plain,
    ( ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G )
    | ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('279',plain,
    ( ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G )
   <= ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['278'])).

thf('280',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('281',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r4_waybel_0 @ X6 @ X4 @ X7 @ X5 )
      | ( r1_yellow_0 @ X4 @ ( k7_relset_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) @ X7 @ X5 ) )
      | ~ ( r1_yellow_0 @ X6 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d31_waybel_0])).

thf('282',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ( r1_yellow_0 @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 ) )
      | ~ ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['280','281'])).

thf('283',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('284',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('285',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('286',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('287',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('288',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ( r1_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ X0 ) )
      | ~ ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['282','283','284','285','286','287'])).

thf('289',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
      | ~ ( r1_yellow_0 @ sk_A @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['279','288'])).

thf('290',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('291',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
      | ~ ( r1_yellow_0 @ sk_A @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['289','290'])).

thf('292',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r1_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['277','291'])).

thf('293',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('294',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( r1_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) ) )
   <= ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(clc,[status(thm)],['292','293'])).

thf('295',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('296',plain,
    ( ( r1_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
   <= ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(clc,[status(thm)],['294','295'])).

thf('297',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['21'])).

thf('298',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( l1_orders_2 @ X33 )
      | ~ ( r1_yellow_0 @ X34 @ X35 )
      | ( r1_yellow_0 @ X33 @ X35 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X34 ) @ ( u1_orders_2 @ X34 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X33 ) @ ( u1_orders_2 @ X33 ) ) )
      | ~ ( l1_orders_2 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t14_yellow_0])).

thf('299',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_D ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_yellow_0 @ sk_D @ X1 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['297','298'])).

thf('300',plain,
    ( ( u1_orders_2 @ sk_D )
    = ( u1_orders_2 @ sk_B ) ),
    inference(eq_res,[status(thm)],['10'])).

thf('301',plain,(
    l1_orders_2 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('302',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_yellow_0 @ sk_D @ X1 )
      | ~ ( r1_yellow_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['299','300','301'])).

thf('303',plain,(
    ! [X0: $i] :
      ( ~ ( r1_yellow_0 @ sk_B @ X0 )
      | ( r1_yellow_0 @ sk_D @ X0 )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference(eq_res,[status(thm)],['302'])).

thf('304',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('305',plain,(
    ! [X0: $i] :
      ( ~ ( r1_yellow_0 @ sk_B @ X0 )
      | ( r1_yellow_0 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['303','304'])).

thf('306',plain,
    ( ( r1_yellow_0 @ sk_D @ ( k9_relat_1 @ sk_E @ sk_G ) )
   <= ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['296','305'])).

thf('307',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('308',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['21'])).

thf('309',plain,(
    r1_yellow_0 @ sk_C @ sk_G ),
    inference(clc,[status(thm)],['265','266'])).

thf('310',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['38'])).

thf(t26_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
              = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
           => ! [C: $i] :
                ( ( r1_yellow_0 @ A @ C )
               => ( ( k1_yellow_0 @ A @ C )
                  = ( k1_yellow_0 @ B @ C ) ) ) ) ) ) )).

thf('311',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( l1_orders_2 @ X37 )
      | ( ( k1_yellow_0 @ X39 @ X38 )
        = ( k1_yellow_0 @ X37 @ X38 ) )
      | ~ ( r1_yellow_0 @ X39 @ X38 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X39 ) @ ( u1_orders_2 @ X39 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X37 ) @ ( u1_orders_2 @ X37 ) ) )
      | ~ ( l1_orders_2 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_0])).

thf('312',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_C ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ sk_C )
      | ~ ( r1_yellow_0 @ sk_C @ X1 )
      | ( ( k1_yellow_0 @ sk_C @ X1 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['310','311'])).

thf('313',plain,
    ( ( u1_orders_2 @ sk_C )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('314',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('315',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( r1_yellow_0 @ sk_C @ X1 )
      | ( ( k1_yellow_0 @ sk_C @ X1 )
        = ( k1_yellow_0 @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['312','313','314'])).

thf('316',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( ( k1_yellow_0 @ sk_C @ X0 )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_C @ X0 ) ) ),
    inference(eq_res,[status(thm)],['315'])).

thf('317',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('318',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_C @ X0 )
        = ( k1_yellow_0 @ sk_A @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['316','317'])).

thf('319',plain,
    ( ( k1_yellow_0 @ sk_C @ sk_G )
    = ( k1_yellow_0 @ sk_A @ sk_G ) ),
    inference('sup-',[status(thm)],['309','318'])).

thf('320',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ( ( k1_yellow_0 @ X4 @ ( k7_relset_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) @ X7 @ X5 ) )
       != ( k3_funct_2 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) @ X7 @ ( k1_yellow_0 @ X6 @ X5 ) ) )
      | ~ ( r1_yellow_0 @ X4 @ ( k7_relset_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) @ X7 @ X5 ) )
      | ( r4_waybel_0 @ X6 @ X4 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d31_waybel_0])).

thf('321',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_yellow_0 @ X1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X1 ) @ X0 @ sk_G ) )
       != ( k3_funct_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X1 ) @ X0 @ ( k1_yellow_0 @ sk_A @ sk_G ) ) )
      | ( v2_struct_0 @ sk_C )
      | ~ ( l1_orders_2 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ( r4_waybel_0 @ sk_C @ X1 @ X0 @ sk_G )
      | ~ ( r1_yellow_0 @ X1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X1 ) @ X0 @ sk_G ) )
      | ~ ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_C ) ) )
      | ~ ( l1_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['319','320'])).

thf('322',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('323',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('324',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('325',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('326',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('327',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('328',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['38'])).

thf('329',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('330',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_yellow_0 @ X1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X1 ) @ X0 @ sk_G ) )
       != ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X1 ) @ X0 @ ( k1_yellow_0 @ sk_A @ sk_G ) ) )
      | ( v2_struct_0 @ sk_C )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X1 ) ) ) )
      | ( r4_waybel_0 @ sk_C @ X1 @ X0 @ sk_G )
      | ~ ( r1_yellow_0 @ X1 @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X1 ) @ X0 @ sk_G ) )
      | ~ ( l1_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['321','322','323','324','325','326','327','328','329'])).

thf('331',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_D @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 @ sk_G ) )
       != ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D ) @ X0 @ ( k1_yellow_0 @ sk_A @ sk_G ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( l1_orders_2 @ sk_D )
      | ~ ( r1_yellow_0 @ sk_D @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D ) @ X0 @ sk_G ) )
      | ( r4_waybel_0 @ sk_C @ sk_D @ X0 @ sk_G )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_D ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['308','330'])).

thf('332',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['21'])).

thf('333',plain,(
    l1_orders_2 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('334',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['21'])).

thf('335',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['21'])).

thf('336',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['21'])).

thf('337',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_D @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 @ sk_G ) )
       != ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 @ ( k1_yellow_0 @ sk_A @ sk_G ) ) )
      | ( v2_struct_0 @ sk_D )
      | ~ ( r1_yellow_0 @ sk_D @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ X0 @ sk_G ) )
      | ( r4_waybel_0 @ sk_C @ sk_D @ X0 @ sk_G )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( v2_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['331','332','333','334','335','336'])).

thf('338',plain,
    ( ~ ( r1_yellow_0 @ sk_D @ ( k9_relat_1 @ sk_E @ sk_G ) )
    | ( v2_struct_0 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ( r4_waybel_0 @ sk_C @ sk_D @ sk_E @ sk_G )
    | ( v2_struct_0 @ sk_D )
    | ( ( k1_yellow_0 @ sk_D @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ sk_G ) )
     != ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k1_yellow_0 @ sk_A @ sk_G ) ) ) ),
    inference('sup-',[status(thm)],['307','337'])).

thf('339',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('340',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('341',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('342',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf(dt_k1_yellow_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k1_yellow_0 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('343',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( k1_yellow_0 @ X8 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_yellow_0])).

thf('344',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) ) ) ),
    inference(clc,[status(thm)],['185','194'])).

thf('345',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k1_yellow_0 @ sk_A @ X0 ) )
        = ( k1_funct_1 @ sk_E @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['343','344'])).

thf('346',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('347',plain,(
    ! [X0: $i] :
      ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k1_yellow_0 @ sk_A @ X0 ) )
      = ( k1_funct_1 @ sk_E @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['345','346'])).

thf('348',plain,
    ( ~ ( r1_yellow_0 @ sk_D @ ( k9_relat_1 @ sk_E @ sk_G ) )
    | ( v2_struct_0 @ sk_C )
    | ( r4_waybel_0 @ sk_C @ sk_D @ sk_E @ sk_G )
    | ( v2_struct_0 @ sk_D )
    | ( ( k1_yellow_0 @ sk_D @ ( k9_relat_1 @ sk_E @ sk_G ) )
     != ( k1_funct_1 @ sk_E @ ( k1_yellow_0 @ sk_A @ sk_G ) ) ) ),
    inference(demod,[status(thm)],['338','339','340','341','342','347'])).

thf('349',plain,
    ( ( ( ( k1_yellow_0 @ sk_D @ ( k9_relat_1 @ sk_E @ sk_G ) )
       != ( k1_funct_1 @ sk_E @ ( k1_yellow_0 @ sk_A @ sk_G ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( r4_waybel_0 @ sk_C @ sk_D @ sk_E @ sk_G )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['306','348'])).

thf('350',plain,
    ( ( r1_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
   <= ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(clc,[status(thm)],['294','295'])).

thf('351',plain,
    ( ( u1_struct_0 @ sk_D )
    = ( u1_struct_0 @ sk_B ) ),
    inference(eq_res,[status(thm)],['21'])).

thf('352',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( l1_orders_2 @ X37 )
      | ( ( k1_yellow_0 @ X39 @ X38 )
        = ( k1_yellow_0 @ X37 @ X38 ) )
      | ~ ( r1_yellow_0 @ X39 @ X38 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X39 ) @ ( u1_orders_2 @ X39 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X37 ) @ ( u1_orders_2 @ X37 ) ) )
      | ~ ( l1_orders_2 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t26_yellow_0])).

thf('353',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_D ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ( ( k1_yellow_0 @ X0 @ X1 )
        = ( k1_yellow_0 @ sk_D @ X1 ) )
      | ~ ( l1_orders_2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['351','352'])).

thf('354',plain,
    ( ( u1_orders_2 @ sk_D )
    = ( u1_orders_2 @ sk_B ) ),
    inference(eq_res,[status(thm)],['10'])).

thf('355',plain,(
    l1_orders_2 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('356',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_yellow_0 @ X0 @ X1 )
      | ( ( k1_yellow_0 @ X0 @ X1 )
        = ( k1_yellow_0 @ sk_D @ X1 ) ) ) ),
    inference(demod,[status(thm)],['353','354','355'])).

thf('357',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_B @ X0 )
        = ( k1_yellow_0 @ sk_D @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_B @ X0 )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference(eq_res,[status(thm)],['356'])).

thf('358',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('359',plain,(
    ! [X0: $i] :
      ( ( ( k1_yellow_0 @ sk_B @ X0 )
        = ( k1_yellow_0 @ sk_D @ X0 ) )
      | ~ ( r1_yellow_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['357','358'])).

thf('360',plain,
    ( ( ( k1_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
      = ( k1_yellow_0 @ sk_D @ ( k9_relat_1 @ sk_E @ sk_G ) ) )
   <= ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['350','359'])).

thf('361',plain,(
    r1_yellow_0 @ sk_A @ sk_G ),
    inference('sup-',[status(thm)],['267','276'])).

thf('362',plain,
    ( ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G )
   <= ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['278'])).

thf('363',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('364',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( r4_waybel_0 @ X6 @ X4 @ X7 @ X5 )
      | ( ( k1_yellow_0 @ X4 @ ( k7_relset_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) @ X7 @ X5 ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) @ X7 @ ( k1_yellow_0 @ X6 @ X5 ) ) )
      | ~ ( r1_yellow_0 @ X6 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d31_waybel_0])).

thf('365',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ( ( k1_yellow_0 @ sk_B @ ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k1_yellow_0 @ sk_A @ X0 ) ) )
      | ~ ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['363','364'])).

thf('366',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('367',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('368',plain,(
    v1_funct_2 @ sk_E @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('369',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['137','138'])).

thf('370',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('371',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ( ( k1_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ X0 ) )
        = ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k1_yellow_0 @ sk_A @ X0 ) ) )
      | ~ ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['365','366','367','368','369','370'])).

thf('372',plain,(
    ! [X0: $i] :
      ( ( k3_funct_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) @ sk_E @ ( k1_yellow_0 @ sk_A @ X0 ) )
      = ( k1_funct_1 @ sk_E @ ( k1_yellow_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['345','346'])).

thf('373',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r1_yellow_0 @ sk_A @ X0 )
      | ( ( k1_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ X0 ) )
        = ( k1_funct_1 @ sk_E @ ( k1_yellow_0 @ sk_A @ X0 ) ) )
      | ~ ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['371','372'])).

thf('374',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k1_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
        = ( k1_funct_1 @ sk_E @ ( k1_yellow_0 @ sk_A @ sk_G ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['362','373'])).

thf('375',plain,(
    m1_subset_1 @ sk_G @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('376',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( ( k1_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
        = ( k1_funct_1 @ sk_E @ ( k1_yellow_0 @ sk_A @ sk_G ) ) )
      | ~ ( r1_yellow_0 @ sk_A @ sk_G )
      | ( v2_struct_0 @ sk_A ) )
   <= ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['374','375'])).

thf('377',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( k1_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
        = ( k1_funct_1 @ sk_E @ ( k1_yellow_0 @ sk_A @ sk_G ) ) )
      | ( v2_struct_0 @ sk_B ) )
   <= ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['361','376'])).

thf('378',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('379',plain,
    ( ( ( v2_struct_0 @ sk_B )
      | ( ( k1_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
        = ( k1_funct_1 @ sk_E @ ( k1_yellow_0 @ sk_A @ sk_G ) ) ) )
   <= ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(clc,[status(thm)],['377','378'])).

thf('380',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('381',plain,
    ( ( ( k1_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
      = ( k1_funct_1 @ sk_E @ ( k1_yellow_0 @ sk_A @ sk_G ) ) )
   <= ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(clc,[status(thm)],['379','380'])).

thf('382',plain,
    ( ( ( ( k1_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) )
       != ( k1_yellow_0 @ sk_B @ ( k9_relat_1 @ sk_E @ sk_G ) ) )
      | ( v2_struct_0 @ sk_D )
      | ( r4_waybel_0 @ sk_C @ sk_D @ sk_E @ sk_G )
      | ( v2_struct_0 @ sk_C ) )
   <= ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(demod,[status(thm)],['349','360','381'])).

thf('383',plain,
    ( ( ( v2_struct_0 @ sk_C )
      | ( r4_waybel_0 @ sk_C @ sk_D @ sk_E @ sk_G )
      | ( v2_struct_0 @ sk_D ) )
   <= ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(simplify,[status(thm)],['382'])).

thf('384',plain,(
    ~ ( v2_struct_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('385',plain,
    ( ( ( v2_struct_0 @ sk_D )
      | ( r4_waybel_0 @ sk_C @ sk_D @ sk_E @ sk_G ) )
   <= ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(clc,[status(thm)],['383','384'])).

thf('386',plain,(
    ~ ( v2_struct_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('387',plain,
    ( ( r4_waybel_0 @ sk_C @ sk_D @ sk_E @ sk_G )
   <= ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(clc,[status(thm)],['385','386'])).

thf('388',plain,(
    ~ ( r4_waybel_0 @ sk_C @ sk_D @ sk_E @ sk_G ) ),
    inference(simpl_trail,[status(thm)],['94','261'])).

thf('389',plain,(
    ~ ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference('sup-',[status(thm)],['387','388'])).

thf('390',plain,
    ( ~ ( r3_waybel_0 @ sk_C @ sk_D @ sk_F @ sk_H )
    | ( r4_waybel_0 @ sk_A @ sk_B @ sk_E @ sk_G ) ),
    inference(split,[status(esa)],['278'])).

thf('391',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','389','390','260'])).


%------------------------------------------------------------------------------
