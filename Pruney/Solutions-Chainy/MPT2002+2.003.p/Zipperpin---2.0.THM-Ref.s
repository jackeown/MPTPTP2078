%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pM78prztGu

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:19 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  213 (1027 expanded)
%              Number of leaves         :   29 ( 300 expanded)
%              Depth                    :   23
%              Number of atoms          : 2694 (38224 expanded)
%              Number of equality atoms :   92 (1690 expanded)
%              Maximal formula depth    :   25 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_orders_3_type,type,(
    v5_orders_3: $i > $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(t1_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ! [C: $i] :
              ( ( ~ ( v2_struct_0 @ C )
                & ( l1_orders_2 @ C ) )
             => ! [D: $i] :
                  ( ( ~ ( v2_struct_0 @ D )
                    & ( l1_orders_2 @ D ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                     => ! [F: $i] :
                          ( ( ( v1_funct_1 @ F )
                            & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) )
                            & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) )
                         => ( ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
                                = ( g1_orders_2 @ ( u1_struct_0 @ C ) @ ( u1_orders_2 @ C ) ) )
                              & ( ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) )
                                = ( g1_orders_2 @ ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) ) )
                              & ( E = F )
                              & ( v5_orders_3 @ E @ A @ B ) )
                           => ( v5_orders_3 @ F @ C @ D ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( l1_orders_2 @ B )
           => ! [C: $i] :
                ( ( ~ ( v2_struct_0 @ C )
                  & ( l1_orders_2 @ C ) )
               => ! [D: $i] :
                    ( ( ~ ( v2_struct_0 @ D )
                      & ( l1_orders_2 @ D ) )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) )
                           => ( ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
                                  = ( g1_orders_2 @ ( u1_struct_0 @ C ) @ ( u1_orders_2 @ C ) ) )
                                & ( ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) )
                                  = ( g1_orders_2 @ ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) ) )
                                & ( E = F )
                                & ( v5_orders_3 @ E @ A @ B ) )
                             => ( v5_orders_3 @ F @ C @ D ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_waybel_9])).

thf('0',plain,(
    m1_subset_1 @ sk_F_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    sk_E_1 = sk_F_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(d5_orders_3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) )
             => ( ( v5_orders_3 @ C @ A @ B )
              <=> ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                       => ( ( r1_orders_2 @ A @ D @ E )
                         => ! [F: $i] :
                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                             => ! [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( u1_struct_0 @ B ) )
                                 => ( ( ( F
                                        = ( k1_funct_1 @ C @ D ) )
                                      & ( G
                                        = ( k1_funct_1 @ C @ E ) ) )
                                   => ( r1_orders_2 @ B @ F @ G ) ) ) ) ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( r1_orders_2 @ X11 @ ( sk_F @ X12 @ X11 @ X13 ) @ ( sk_G @ X12 @ X11 @ X13 ) )
      | ( v5_orders_3 @ X12 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('4',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ~ ( r1_orders_2 @ sk_D_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) )
    | ~ ( l1_orders_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_F_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_E_1 = sk_F_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ~ ( r1_orders_2 @ sk_D_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','5','6','9','10'])).

thf('12',plain,(
    ~ ( v5_orders_3 @ sk_F_1 @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_E_1 = sk_F_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ~ ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( r1_orders_2 @ sk_D_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['11','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('17',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ( r1_orders_2 @ X13 @ ( sk_D @ X12 @ X11 @ X13 ) @ ( sk_E @ X12 @ X11 @ X13 ) )
      | ( v5_orders_3 @ X12 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('18',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( r1_orders_2 @ sk_C @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) )
    | ~ ( l1_orders_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('22',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( r1_orders_2 @ sk_C @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['18','19','20','21','22'])).

thf('24',plain,(
    ~ ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('25',plain,(
    r1_orders_2 @ sk_C @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('27',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ( m1_subset_1 @ ( sk_E @ X12 @ X11 @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ( v5_orders_3 @ X12 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('28',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_orders_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('32',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,(
    ~ ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('35',plain,(
    m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('38',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( g1_orders_2 @ X3 @ X4 )
       != ( g1_orders_2 @ X1 @ X2 ) )
      | ( X4 = X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_A )
        = X0 )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','39'])).

thf('41',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_A )
        = X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( u1_orders_2 @ sk_A )
    = ( u1_orders_2 @ sk_C ) ),
    inference(eq_res,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('45',plain,
    ( ( m1_subset_1 @ ( u1_orders_2 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ ( u1_orders_2 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( g1_orders_2 @ X3 @ X4 )
       != ( g1_orders_2 @ X1 @ X2 ) )
      | ( X3 = X1 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_C ) )
       != ( g1_orders_2 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( u1_orders_2 @ sk_A )
    = ( u1_orders_2 @ sk_C ) ),
    inference(eq_res,[status(thm)],['42'])).

thf('52',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_C ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_A )
        = X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) )
       != ( g1_orders_2 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['53'])).

thf(t1_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
              = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                       => ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                           => ( ( ( C = E )
                                & ( D = F ) )
                             => ( ( ( r1_orders_2 @ A @ C @ D )
                                 => ( r1_orders_2 @ B @ E @ F ) )
                                & ( ( r2_orders_2 @ A @ C @ D )
                                 => ( r2_orders_2 @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) )).

thf('55',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X5 ) )
      | ~ ( r1_orders_2 @ X7 @ X9 @ X6 )
      | ( r1_orders_2 @ X5 @ X10 @ X8 )
      | ( X6 != X8 )
      | ( X9 != X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X7 ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X7 ) @ ( u1_orders_2 @ X7 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X5 ) @ ( u1_orders_2 @ X5 ) ) )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t1_yellow_0])).

thf('56',plain,(
    ! [X5: $i,X7: $i,X8: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X7 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X7 ) @ ( u1_orders_2 @ X7 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X5 ) @ ( u1_orders_2 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X5 ) )
      | ( r1_orders_2 @ X5 @ X10 @ X8 )
      | ~ ( r1_orders_2 @ X7 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ( r1_orders_2 @ sk_A @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,
    ( ( u1_orders_2 @ sk_A )
    = ( u1_orders_2 @ sk_C ) ),
    inference(eq_res,[status(thm)],['42'])).

thf('59',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['53'])).

thf('61',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['53'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ( r1_orders_2 @ sk_A @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_C @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(eq_res,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_orders_2 @ sk_C @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_orders_2 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_orders_2 @ sk_C @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_orders_2 @ sk_A @ X0 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) )
      | ~ ( r1_orders_2 @ sk_C @ X0 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['35','66'])).

thf('68',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('70',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ( m1_subset_1 @ ( sk_D @ X12 @ X11 @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ( v5_orders_3 @ X12 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('71',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_orders_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('75',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['71','72','73','74','75'])).

thf('77',plain,(
    ~ ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('78',plain,(
    m1_subset_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('79',plain,(
    r1_orders_2 @ sk_A @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['68','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('81',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ( ( sk_G @ X12 @ X11 @ X13 )
        = ( k1_funct_1 @ X12 @ ( sk_E @ X12 @ X11 @ X13 ) ) )
      | ( v5_orders_3 @ X12 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('82',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C )
      = ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ) )
    | ~ ( l1_orders_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('86',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C )
      = ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('88',plain,(
    ~ ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('89',plain,
    ( ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C )
    = ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('91',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('93',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( g1_orders_2 @ X3 @ X4 )
       != ( g1_orders_2 @ X1 @ X2 ) )
      | ( X3 = X1 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('94',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B )
        = X1 )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B )
        = X1 ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_D_1 ) ),
    inference(eq_res,[status(thm)],['97'])).

thf('99',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['53'])).

thf('100',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_3 @ X12 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X11 ) )
      | ( r1_orders_2 @ X11 @ X16 @ X15 )
      | ( X15
       != ( k1_funct_1 @ X12 @ X14 ) )
      | ( X16
       != ( k1_funct_1 @ X12 @ X17 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_orders_2 @ X13 @ X17 @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('101',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_orders_2 @ X13 @ X17 @ X14 )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ X12 @ X17 ) @ ( u1_struct_0 @ X11 ) )
      | ( r1_orders_2 @ X11 @ ( k1_funct_1 @ X12 @ X17 ) @ ( k1_funct_1 @ X12 @ X14 ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ X12 @ X14 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( v5_orders_3 @ X12 @ X13 @ X11 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_3 @ X1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ X1 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_funct_1 @ X1 @ X3 ) @ ( k1_funct_1 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ X1 @ X3 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['99','101'])).

thf('103',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['53'])).

thf('104',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['53'])).

thf('105',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['53'])).

thf('106',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_3 @ X1 @ sk_A @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ X1 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ( r1_orders_2 @ X0 @ ( k1_funct_1 @ X1 @ X3 ) @ ( k1_funct_1 @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ X1 @ X3 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ sk_A @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_2 @ X1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['102','103','104','105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X2 )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ X0 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_orders_2 @ sk_B @ ( k1_funct_1 @ X0 @ X1 ) @ ( k1_funct_1 @ X0 @ X2 ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ X0 @ X2 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v5_orders_3 @ X0 @ sk_A @ sk_B )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['98','107'])).

thf('109',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_D_1 ) ),
    inference(eq_res,[status(thm)],['97'])).

thf('110',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_D_1 ) ),
    inference(eq_res,[status(thm)],['97'])).

thf('111',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_D_1 ) ),
    inference(eq_res,[status(thm)],['97'])).

thf('112',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X2 )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ X0 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_orders_2 @ sk_B @ ( k1_funct_1 @ X0 @ X1 ) @ ( k1_funct_1 @ X0 @ X2 ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ X0 @ X2 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v5_orders_3 @ X0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['108','109','110','111','112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_orders_3 @ sk_E_1 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_orders_2 @ sk_B @ ( k1_funct_1 @ sk_E_1 @ X1 ) @ ( k1_funct_1 @ sk_E_1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['90','113'])).

thf('115',plain,(
    v5_orders_3 @ sk_E_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('117',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_orders_2 @ sk_B @ ( k1_funct_1 @ sk_E_1 @ X1 ) @ ( k1_funct_1 @ sk_E_1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['114','115','116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_orders_2 @ sk_B @ ( k1_funct_1 @ sk_E_1 @ X0 ) @ ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['89','118'])).

thf('120',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('121',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ( m1_subset_1 @ ( sk_G @ X12 @ X11 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ( v5_orders_3 @ X12 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('122',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( l1_orders_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('126',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,
    ( ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['122','123','124','125','126'])).

thf('128',plain,(
    ~ ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('129',plain,(
    m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C )
    = ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('131',plain,(
    m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_orders_2 @ sk_B @ ( k1_funct_1 @ sk_E_1 @ X0 ) @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['119','129','130','131'])).

thf('133',plain,
    ( ( r1_orders_2 @ sk_B @ ( k1_funct_1 @ sk_E_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) ) @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['79','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('135',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ( ( sk_F @ X12 @ X11 @ X13 )
        = ( k1_funct_1 @ X12 @ ( sk_D @ X12 @ X11 @ X13 ) ) )
      | ( v5_orders_3 @ X12 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('136',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C )
      = ( k1_funct_1 @ sk_E_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) ) )
    | ~ ( l1_orders_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('140',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,
    ( ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C )
      = ( k1_funct_1 @ sk_E_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['136','137','138','139','140'])).

thf('142',plain,(
    ~ ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('143',plain,
    ( ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C )
    = ( k1_funct_1 @ sk_E_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('144',plain,
    ( ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C )
    = ( k1_funct_1 @ sk_E_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['141','142'])).

thf('145',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('146',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ( m1_subset_1 @ ( sk_F @ X12 @ X11 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ( v5_orders_3 @ X12 @ X13 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) ) ) )
      | ~ ( v1_funct_2 @ X12 @ ( u1_struct_0 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('147',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( l1_orders_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('151',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['147','148','149','150','151'])).

thf('153',plain,(
    ~ ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('154',plain,(
    m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,(
    m1_subset_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['76','77'])).

thf('156',plain,(
    r1_orders_2 @ sk_B @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['133','143','144','154','155'])).

thf('157',plain,(
    m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('158',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_B )
        = X0 )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_B )
        = X0 ) ) ),
    inference(demod,[status(thm)],['160','161'])).

thf('163',plain,
    ( ( u1_orders_2 @ sk_B )
    = ( u1_orders_2 @ sk_D_1 ) ),
    inference(eq_res,[status(thm)],['162'])).

thf('164',plain,(
    ! [X5: $i,X7: $i,X8: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X7 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X7 ) @ ( u1_orders_2 @ X7 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X5 ) @ ( u1_orders_2 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X7 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X5 ) )
      | ( r1_orders_2 @ X5 @ X10 @ X8 )
      | ~ ( r1_orders_2 @ X7 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('165',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_D_1 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ sk_B @ X2 @ X1 )
      | ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('167',plain,
    ( ( u1_orders_2 @ sk_B )
    = ( u1_orders_2 @ sk_D_1 ) ),
    inference(eq_res,[status(thm)],['162'])).

thf('168',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_D_1 ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ sk_B @ X2 @ X1 )
      | ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['165','168','169'])).

thf('171',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_D_1 ) ),
    inference(eq_res,[status(thm)],['97'])).

thf('172',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_D_1 ) ),
    inference(eq_res,[status(thm)],['97'])).

thf('173',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r1_orders_2 @ sk_B @ X2 @ X1 )
      | ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_orders_2 @ sk_D_1 @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_B @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( l1_orders_2 @ sk_D_1 ) ) ),
    inference(eq_res,[status(thm)],['173'])).

thf('175',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_orders_2 @ sk_B @ X0 @ X1 )
      | ( r1_orders_2 @ sk_D_1 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_orders_2 @ sk_B @ X0 @ X1 )
      | ( r1_orders_2 @ sk_D_1 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_orders_2 @ sk_D_1 @ X0 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) )
      | ~ ( r1_orders_2 @ sk_B @ X0 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['157','177'])).

thf('179',plain,
    ( ( r1_orders_2 @ sk_D_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['156','178'])).

thf('180',plain,(
    m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['152','153'])).

thf('181',plain,(
    r1_orders_2 @ sk_D_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['179','180'])).

thf('182',plain,(
    $false ),
    inference(demod,[status(thm)],['15','181'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pM78prztGu
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:19:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.49/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.68  % Solved by: fo/fo7.sh
% 0.49/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.68  % done 481 iterations in 0.210s
% 0.49/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.68  % SZS output start Refutation
% 0.49/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.68  thf(v5_orders_3_type, type, v5_orders_3: $i > $i > $i > $o).
% 0.49/0.68  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.49/0.68  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.49/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.68  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.49/0.68  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.49/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.49/0.68  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.49/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.68  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.49/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.49/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.68  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.49/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.49/0.68  thf(sk_G_type, type, sk_G: $i > $i > $i > $i).
% 0.49/0.68  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.49/0.68  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.49/0.68  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.49/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.68  thf(sk_F_1_type, type, sk_F_1: $i).
% 0.49/0.68  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.49/0.68  thf(t1_waybel_9, conjecture,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( l1_orders_2 @ A ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( l1_orders_2 @ B ) =>
% 0.49/0.68           ( ![C:$i]:
% 0.49/0.68             ( ( ( ~( v2_struct_0 @ C ) ) & ( l1_orders_2 @ C ) ) =>
% 0.49/0.68               ( ![D:$i]:
% 0.49/0.68                 ( ( ( ~( v2_struct_0 @ D ) ) & ( l1_orders_2 @ D ) ) =>
% 0.49/0.68                   ( ![E:$i]:
% 0.49/0.68                     ( ( ( v1_funct_1 @ E ) & 
% 0.49/0.68                         ( v1_funct_2 @
% 0.49/0.68                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.49/0.68                         ( m1_subset_1 @
% 0.49/0.68                           E @ 
% 0.49/0.68                           ( k1_zfmisc_1 @
% 0.49/0.68                             ( k2_zfmisc_1 @
% 0.49/0.68                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.49/0.68                       ( ![F:$i]:
% 0.49/0.68                         ( ( ( v1_funct_1 @ F ) & 
% 0.49/0.68                             ( v1_funct_2 @
% 0.49/0.68                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) & 
% 0.49/0.68                             ( m1_subset_1 @
% 0.49/0.68                               F @ 
% 0.49/0.68                               ( k1_zfmisc_1 @
% 0.49/0.68                                 ( k2_zfmisc_1 @
% 0.49/0.68                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) ) =>
% 0.49/0.68                           ( ( ( ( g1_orders_2 @
% 0.49/0.68                                   ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) =
% 0.49/0.68                                 ( g1_orders_2 @
% 0.49/0.68                                   ( u1_struct_0 @ C ) @ ( u1_orders_2 @ C ) ) ) & 
% 0.49/0.68                               ( ( g1_orders_2 @
% 0.49/0.68                                   ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) =
% 0.49/0.68                                 ( g1_orders_2 @
% 0.49/0.68                                   ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) ) ) & 
% 0.49/0.68                               ( ( E ) = ( F ) ) & ( v5_orders_3 @ E @ A @ B ) ) =>
% 0.49/0.68                             ( v5_orders_3 @ F @ C @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.49/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.68    (~( ![A:$i]:
% 0.49/0.68        ( ( l1_orders_2 @ A ) =>
% 0.49/0.68          ( ![B:$i]:
% 0.49/0.68            ( ( l1_orders_2 @ B ) =>
% 0.49/0.68              ( ![C:$i]:
% 0.49/0.68                ( ( ( ~( v2_struct_0 @ C ) ) & ( l1_orders_2 @ C ) ) =>
% 0.49/0.68                  ( ![D:$i]:
% 0.49/0.68                    ( ( ( ~( v2_struct_0 @ D ) ) & ( l1_orders_2 @ D ) ) =>
% 0.49/0.68                      ( ![E:$i]:
% 0.49/0.68                        ( ( ( v1_funct_1 @ E ) & 
% 0.49/0.68                            ( v1_funct_2 @
% 0.49/0.68                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.49/0.68                            ( m1_subset_1 @
% 0.49/0.68                              E @ 
% 0.49/0.68                              ( k1_zfmisc_1 @
% 0.49/0.68                                ( k2_zfmisc_1 @
% 0.49/0.68                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.49/0.68                          ( ![F:$i]:
% 0.49/0.68                            ( ( ( v1_funct_1 @ F ) & 
% 0.49/0.68                                ( v1_funct_2 @
% 0.49/0.68                                  F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) & 
% 0.49/0.68                                ( m1_subset_1 @
% 0.49/0.68                                  F @ 
% 0.49/0.68                                  ( k1_zfmisc_1 @
% 0.49/0.68                                    ( k2_zfmisc_1 @
% 0.49/0.68                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) ) =>
% 0.49/0.68                              ( ( ( ( g1_orders_2 @
% 0.49/0.68                                      ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) =
% 0.49/0.68                                    ( g1_orders_2 @
% 0.49/0.68                                      ( u1_struct_0 @ C ) @ ( u1_orders_2 @ C ) ) ) & 
% 0.49/0.68                                  ( ( g1_orders_2 @
% 0.49/0.68                                      ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) =
% 0.49/0.68                                    ( g1_orders_2 @
% 0.49/0.68                                      ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) ) ) & 
% 0.49/0.68                                  ( ( E ) = ( F ) ) & 
% 0.49/0.68                                  ( v5_orders_3 @ E @ A @ B ) ) =>
% 0.49/0.68                                ( v5_orders_3 @ F @ C @ D ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.49/0.68    inference('cnf.neg', [status(esa)], [t1_waybel_9])).
% 0.49/0.68  thf('0', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_F_1 @ 
% 0.49/0.68        (k1_zfmisc_1 @ 
% 0.49/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('1', plain, (((sk_E_1) = (sk_F_1))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('2', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_E_1 @ 
% 0.49/0.68        (k1_zfmisc_1 @ 
% 0.49/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.49/0.68      inference('demod', [status(thm)], ['0', '1'])).
% 0.49/0.68  thf(d5_orders_3, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( l1_orders_2 @ A ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( l1_orders_2 @ B ) =>
% 0.49/0.68           ( ![C:$i]:
% 0.49/0.68             ( ( ( v1_funct_1 @ C ) & 
% 0.49/0.68                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.49/0.68                 ( m1_subset_1 @
% 0.49/0.68                   C @ 
% 0.49/0.68                   ( k1_zfmisc_1 @
% 0.49/0.68                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.49/0.68               ( ( v5_orders_3 @ C @ A @ B ) <=>
% 0.49/0.68                 ( ![D:$i]:
% 0.49/0.68                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.68                     ( ![E:$i]:
% 0.49/0.68                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.68                         ( ( r1_orders_2 @ A @ D @ E ) =>
% 0.49/0.68                           ( ![F:$i]:
% 0.49/0.68                             ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.49/0.68                               ( ![G:$i]:
% 0.49/0.68                                 ( ( m1_subset_1 @ G @ ( u1_struct_0 @ B ) ) =>
% 0.49/0.68                                   ( ( ( ( F ) = ( k1_funct_1 @ C @ D ) ) & 
% 0.49/0.68                                       ( ( G ) = ( k1_funct_1 @ C @ E ) ) ) =>
% 0.49/0.68                                     ( r1_orders_2 @ B @ F @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.49/0.68  thf('3', plain,
% 0.49/0.68      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.68         (~ (l1_orders_2 @ X11)
% 0.49/0.68          | ~ (r1_orders_2 @ X11 @ (sk_F @ X12 @ X11 @ X13) @ 
% 0.49/0.68               (sk_G @ X12 @ X11 @ X13))
% 0.49/0.68          | (v5_orders_3 @ X12 @ X13 @ X11)
% 0.49/0.68          | ~ (m1_subset_1 @ X12 @ 
% 0.49/0.68               (k1_zfmisc_1 @ 
% 0.49/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.49/0.68          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.49/0.68          | ~ (v1_funct_1 @ X12)
% 0.49/0.68          | ~ (l1_orders_2 @ X13))),
% 0.49/0.68      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.49/0.68  thf('4', plain,
% 0.49/0.68      ((~ (l1_orders_2 @ sk_C)
% 0.49/0.68        | ~ (v1_funct_1 @ sk_E_1)
% 0.49/0.68        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.49/0.68             (u1_struct_0 @ sk_D_1))
% 0.49/0.68        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.49/0.68        | ~ (r1_orders_2 @ sk_D_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.68             (sk_G @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.49/0.68        | ~ (l1_orders_2 @ sk_D_1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.49/0.68  thf('5', plain, ((l1_orders_2 @ sk_C)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('6', plain, ((v1_funct_1 @ sk_E_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('7', plain,
% 0.49/0.68      ((v1_funct_2 @ sk_F_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('8', plain, (((sk_E_1) = (sk_F_1))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('9', plain,
% 0.49/0.68      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.49/0.68      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.68  thf('10', plain, ((l1_orders_2 @ sk_D_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('11', plain,
% 0.49/0.68      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.49/0.68        | ~ (r1_orders_2 @ sk_D_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.68             (sk_G @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.49/0.68      inference('demod', [status(thm)], ['4', '5', '6', '9', '10'])).
% 0.49/0.68  thf('12', plain, (~ (v5_orders_3 @ sk_F_1 @ sk_C @ sk_D_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('13', plain, (((sk_E_1) = (sk_F_1))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('14', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.49/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.49/0.68  thf('15', plain,
% 0.49/0.68      (~ (r1_orders_2 @ sk_D_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.68          (sk_G @ sk_E_1 @ sk_D_1 @ sk_C))),
% 0.49/0.68      inference('clc', [status(thm)], ['11', '14'])).
% 0.49/0.68  thf('16', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_E_1 @ 
% 0.49/0.68        (k1_zfmisc_1 @ 
% 0.49/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.49/0.68      inference('demod', [status(thm)], ['0', '1'])).
% 0.49/0.68  thf('17', plain,
% 0.49/0.68      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.68         (~ (l1_orders_2 @ X11)
% 0.49/0.68          | (r1_orders_2 @ X13 @ (sk_D @ X12 @ X11 @ X13) @ 
% 0.49/0.68             (sk_E @ X12 @ X11 @ X13))
% 0.49/0.68          | (v5_orders_3 @ X12 @ X13 @ X11)
% 0.49/0.68          | ~ (m1_subset_1 @ X12 @ 
% 0.49/0.68               (k1_zfmisc_1 @ 
% 0.49/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.49/0.68          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.49/0.68          | ~ (v1_funct_1 @ X12)
% 0.49/0.68          | ~ (l1_orders_2 @ X13))),
% 0.49/0.68      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.49/0.68  thf('18', plain,
% 0.49/0.68      ((~ (l1_orders_2 @ sk_C)
% 0.49/0.68        | ~ (v1_funct_1 @ sk_E_1)
% 0.49/0.68        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.49/0.68             (u1_struct_0 @ sk_D_1))
% 0.49/0.68        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.49/0.68        | (r1_orders_2 @ sk_C @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.68           (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.49/0.68        | ~ (l1_orders_2 @ sk_D_1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.68  thf('19', plain, ((l1_orders_2 @ sk_C)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('20', plain, ((v1_funct_1 @ sk_E_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('21', plain,
% 0.49/0.68      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.49/0.68      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.68  thf('22', plain, ((l1_orders_2 @ sk_D_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('23', plain,
% 0.49/0.68      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.49/0.68        | (r1_orders_2 @ sk_C @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.68           (sk_E @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.49/0.68      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.49/0.68  thf('24', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.49/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.49/0.68  thf('25', plain,
% 0.49/0.68      ((r1_orders_2 @ sk_C @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.68        (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))),
% 0.49/0.68      inference('clc', [status(thm)], ['23', '24'])).
% 0.49/0.68  thf('26', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_E_1 @ 
% 0.49/0.68        (k1_zfmisc_1 @ 
% 0.49/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.49/0.68      inference('demod', [status(thm)], ['0', '1'])).
% 0.49/0.68  thf('27', plain,
% 0.49/0.68      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.68         (~ (l1_orders_2 @ X11)
% 0.49/0.68          | (m1_subset_1 @ (sk_E @ X12 @ X11 @ X13) @ (u1_struct_0 @ X13))
% 0.49/0.68          | (v5_orders_3 @ X12 @ X13 @ X11)
% 0.49/0.68          | ~ (m1_subset_1 @ X12 @ 
% 0.49/0.68               (k1_zfmisc_1 @ 
% 0.49/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.49/0.68          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.49/0.68          | ~ (v1_funct_1 @ X12)
% 0.49/0.68          | ~ (l1_orders_2 @ X13))),
% 0.49/0.68      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.49/0.68  thf('28', plain,
% 0.49/0.68      ((~ (l1_orders_2 @ sk_C)
% 0.49/0.68        | ~ (v1_funct_1 @ sk_E_1)
% 0.49/0.68        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.49/0.68             (u1_struct_0 @ sk_D_1))
% 0.49/0.68        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.49/0.68        | (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.49/0.68        | ~ (l1_orders_2 @ sk_D_1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['26', '27'])).
% 0.49/0.68  thf('29', plain, ((l1_orders_2 @ sk_C)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('30', plain, ((v1_funct_1 @ sk_E_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('31', plain,
% 0.49/0.68      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.49/0.68      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.68  thf('32', plain, ((l1_orders_2 @ sk_D_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('33', plain,
% 0.49/0.68      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.49/0.68        | (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C)))),
% 0.49/0.68      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 0.49/0.68  thf('34', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.49/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.49/0.68  thf('35', plain,
% 0.49/0.68      ((m1_subset_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))),
% 0.49/0.68      inference('clc', [status(thm)], ['33', '34'])).
% 0.49/0.68  thf('36', plain,
% 0.49/0.68      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.49/0.68         = (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf(dt_u1_orders_2, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( l1_orders_2 @ A ) =>
% 0.49/0.68       ( m1_subset_1 @
% 0.49/0.68         ( u1_orders_2 @ A ) @ 
% 0.49/0.68         ( k1_zfmisc_1 @
% 0.49/0.68           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.49/0.68  thf('37', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((m1_subset_1 @ (u1_orders_2 @ X0) @ 
% 0.49/0.68           (k1_zfmisc_1 @ 
% 0.49/0.68            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))
% 0.49/0.68          | ~ (l1_orders_2 @ X0))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.49/0.68  thf(free_g1_orders_2, axiom,
% 0.49/0.68    (![A:$i,B:$i]:
% 0.49/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.49/0.68       ( ![C:$i,D:$i]:
% 0.49/0.68         ( ( ( g1_orders_2 @ A @ B ) = ( g1_orders_2 @ C @ D ) ) =>
% 0.49/0.68           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.49/0.68  thf('38', plain,
% 0.49/0.68      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.49/0.68         (((g1_orders_2 @ X3 @ X4) != (g1_orders_2 @ X1 @ X2))
% 0.49/0.68          | ((X4) = (X2))
% 0.49/0.68          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X3))))),
% 0.49/0.68      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.49/0.68  thf('39', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.68         (~ (l1_orders_2 @ X0)
% 0.49/0.68          | ((u1_orders_2 @ X0) = (X1))
% 0.49/0.68          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.49/0.68              != (g1_orders_2 @ X2 @ X1)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['37', '38'])).
% 0.49/0.68  thf('40', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (((g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C))
% 0.49/0.68            != (g1_orders_2 @ X1 @ X0))
% 0.49/0.68          | ((u1_orders_2 @ sk_A) = (X0))
% 0.49/0.68          | ~ (l1_orders_2 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['36', '39'])).
% 0.49/0.68  thf('41', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('42', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (((g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C))
% 0.49/0.68            != (g1_orders_2 @ X1 @ X0))
% 0.49/0.68          | ((u1_orders_2 @ sk_A) = (X0)))),
% 0.49/0.68      inference('demod', [status(thm)], ['40', '41'])).
% 0.49/0.68  thf('43', plain, (((u1_orders_2 @ sk_A) = (u1_orders_2 @ sk_C))),
% 0.49/0.68      inference('eq_res', [status(thm)], ['42'])).
% 0.49/0.68  thf('44', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((m1_subset_1 @ (u1_orders_2 @ X0) @ 
% 0.49/0.68           (k1_zfmisc_1 @ 
% 0.49/0.68            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))
% 0.49/0.68          | ~ (l1_orders_2 @ X0))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.49/0.68  thf('45', plain,
% 0.49/0.68      (((m1_subset_1 @ (u1_orders_2 @ sk_C) @ 
% 0.49/0.68         (k1_zfmisc_1 @ 
% 0.49/0.68          (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))
% 0.49/0.68        | ~ (l1_orders_2 @ sk_A))),
% 0.49/0.68      inference('sup+', [status(thm)], ['43', '44'])).
% 0.49/0.68  thf('46', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('47', plain,
% 0.49/0.68      ((m1_subset_1 @ (u1_orders_2 @ sk_C) @ 
% 0.49/0.68        (k1_zfmisc_1 @ 
% 0.49/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A))))),
% 0.49/0.68      inference('demod', [status(thm)], ['45', '46'])).
% 0.49/0.68  thf('48', plain,
% 0.49/0.68      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.49/0.68         (((g1_orders_2 @ X3 @ X4) != (g1_orders_2 @ X1 @ X2))
% 0.49/0.68          | ((X3) = (X1))
% 0.49/0.68          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X3))))),
% 0.49/0.68      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.49/0.68  thf('49', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (((u1_struct_0 @ sk_A) = (X0))
% 0.49/0.68          | ((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_C))
% 0.49/0.68              != (g1_orders_2 @ X0 @ X1)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['47', '48'])).
% 0.49/0.68  thf('50', plain,
% 0.49/0.68      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.49/0.68         = (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('51', plain, (((u1_orders_2 @ sk_A) = (u1_orders_2 @ sk_C))),
% 0.49/0.68      inference('eq_res', [status(thm)], ['42'])).
% 0.49/0.68  thf('52', plain,
% 0.49/0.68      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_C))
% 0.49/0.68         = (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))),
% 0.49/0.68      inference('demod', [status(thm)], ['50', '51'])).
% 0.49/0.68  thf('53', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (((u1_struct_0 @ sk_A) = (X0))
% 0.49/0.68          | ((g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C))
% 0.49/0.68              != (g1_orders_2 @ X0 @ X1)))),
% 0.49/0.68      inference('demod', [status(thm)], ['49', '52'])).
% 0.49/0.68  thf('54', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_C))),
% 0.49/0.68      inference('eq_res', [status(thm)], ['53'])).
% 0.49/0.68  thf(t1_yellow_0, axiom,
% 0.49/0.68    (![A:$i]:
% 0.49/0.68     ( ( l1_orders_2 @ A ) =>
% 0.49/0.68       ( ![B:$i]:
% 0.49/0.68         ( ( l1_orders_2 @ B ) =>
% 0.49/0.68           ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) =
% 0.49/0.68               ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) ) =>
% 0.49/0.68             ( ![C:$i]:
% 0.49/0.68               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.68                 ( ![D:$i]:
% 0.49/0.68                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.49/0.68                     ( ![E:$i]:
% 0.49/0.68                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.49/0.68                         ( ![F:$i]:
% 0.49/0.68                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.49/0.68                             ( ( ( ( C ) = ( E ) ) & ( ( D ) = ( F ) ) ) =>
% 0.49/0.68                               ( ( ( r1_orders_2 @ A @ C @ D ) =>
% 0.49/0.68                                   ( r1_orders_2 @ B @ E @ F ) ) & 
% 0.49/0.68                                 ( ( r2_orders_2 @ A @ C @ D ) =>
% 0.49/0.68                                   ( r2_orders_2 @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.49/0.68  thf('55', plain,
% 0.49/0.68      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.68         (~ (l1_orders_2 @ X5)
% 0.49/0.68          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.49/0.68          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X5))
% 0.49/0.68          | ~ (r1_orders_2 @ X7 @ X9 @ X6)
% 0.49/0.68          | (r1_orders_2 @ X5 @ X10 @ X8)
% 0.49/0.68          | ((X6) != (X8))
% 0.49/0.68          | ((X9) != (X10))
% 0.49/0.68          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X5))
% 0.49/0.68          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X7))
% 0.49/0.68          | ((g1_orders_2 @ (u1_struct_0 @ X7) @ (u1_orders_2 @ X7))
% 0.49/0.68              != (g1_orders_2 @ (u1_struct_0 @ X5) @ (u1_orders_2 @ X5)))
% 0.49/0.68          | ~ (l1_orders_2 @ X7))),
% 0.49/0.68      inference('cnf', [status(esa)], [t1_yellow_0])).
% 0.49/0.68  thf('56', plain,
% 0.49/0.68      (![X5 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.49/0.68         (~ (l1_orders_2 @ X7)
% 0.49/0.68          | ((g1_orders_2 @ (u1_struct_0 @ X7) @ (u1_orders_2 @ X7))
% 0.49/0.68              != (g1_orders_2 @ (u1_struct_0 @ X5) @ (u1_orders_2 @ X5)))
% 0.49/0.68          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X7))
% 0.49/0.68          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X5))
% 0.49/0.68          | (r1_orders_2 @ X5 @ X10 @ X8)
% 0.49/0.68          | ~ (r1_orders_2 @ X7 @ X10 @ X8)
% 0.49/0.68          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X5))
% 0.49/0.68          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.49/0.68          | ~ (l1_orders_2 @ X5))),
% 0.49/0.68      inference('simplify', [status(thm)], ['55'])).
% 0.49/0.68  thf('57', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.68         (((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.49/0.68            != (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_A)))
% 0.49/0.68          | ~ (l1_orders_2 @ sk_A)
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.49/0.68          | ~ (r1_orders_2 @ X0 @ X2 @ X1)
% 0.49/0.68          | (r1_orders_2 @ sk_A @ X2 @ X1)
% 0.49/0.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 0.49/0.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.49/0.68          | ~ (l1_orders_2 @ X0))),
% 0.49/0.68      inference('sup-', [status(thm)], ['54', '56'])).
% 0.49/0.68  thf('58', plain, (((u1_orders_2 @ sk_A) = (u1_orders_2 @ sk_C))),
% 0.49/0.68      inference('eq_res', [status(thm)], ['42'])).
% 0.49/0.68  thf('59', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('60', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_C))),
% 0.49/0.68      inference('eq_res', [status(thm)], ['53'])).
% 0.49/0.68  thf('61', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_C))),
% 0.49/0.68      inference('eq_res', [status(thm)], ['53'])).
% 0.49/0.68  thf('62', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.68         (((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.49/0.68            != (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C))
% 0.49/0.68          | ~ (r1_orders_2 @ X0 @ X2 @ X1)
% 0.49/0.68          | (r1_orders_2 @ sk_A @ X2 @ X1)
% 0.49/0.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C))
% 0.49/0.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.49/0.68          | ~ (l1_orders_2 @ X0))),
% 0.49/0.68      inference('demod', [status(thm)], ['57', '58', '59', '60', '61'])).
% 0.49/0.68  thf('63', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (l1_orders_2 @ sk_C)
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.49/0.68          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.49/0.68          | ~ (r1_orders_2 @ sk_C @ X0 @ X1)
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C))
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C)))),
% 0.49/0.68      inference('eq_res', [status(thm)], ['62'])).
% 0.49/0.68  thf('64', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C))
% 0.49/0.68          | ~ (r1_orders_2 @ sk_C @ X0 @ X1)
% 0.49/0.68          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.49/0.68          | ~ (l1_orders_2 @ sk_C))),
% 0.49/0.68      inference('simplify', [status(thm)], ['63'])).
% 0.49/0.68  thf('65', plain, ((l1_orders_2 @ sk_C)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('66', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C))
% 0.49/0.68          | ~ (r1_orders_2 @ sk_C @ X0 @ X1)
% 0.49/0.68          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.49/0.68      inference('demod', [status(thm)], ['64', '65'])).
% 0.49/0.68  thf('67', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.49/0.68          | (r1_orders_2 @ sk_A @ X0 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.49/0.68          | ~ (r1_orders_2 @ sk_C @ X0 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['35', '66'])).
% 0.49/0.68  thf('68', plain,
% 0.49/0.68      (((r1_orders_2 @ sk_A @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.68         (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.49/0.68        | ~ (m1_subset_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.68             (u1_struct_0 @ sk_C)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['25', '67'])).
% 0.49/0.68  thf('69', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_E_1 @ 
% 0.49/0.68        (k1_zfmisc_1 @ 
% 0.49/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.49/0.68      inference('demod', [status(thm)], ['0', '1'])).
% 0.49/0.68  thf('70', plain,
% 0.49/0.68      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.68         (~ (l1_orders_2 @ X11)
% 0.49/0.68          | (m1_subset_1 @ (sk_D @ X12 @ X11 @ X13) @ (u1_struct_0 @ X13))
% 0.49/0.68          | (v5_orders_3 @ X12 @ X13 @ X11)
% 0.49/0.68          | ~ (m1_subset_1 @ X12 @ 
% 0.49/0.68               (k1_zfmisc_1 @ 
% 0.49/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.49/0.68          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.49/0.68          | ~ (v1_funct_1 @ X12)
% 0.49/0.68          | ~ (l1_orders_2 @ X13))),
% 0.49/0.68      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.49/0.68  thf('71', plain,
% 0.49/0.68      ((~ (l1_orders_2 @ sk_C)
% 0.49/0.68        | ~ (v1_funct_1 @ sk_E_1)
% 0.49/0.68        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.49/0.68             (u1_struct_0 @ sk_D_1))
% 0.49/0.68        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.49/0.68        | (m1_subset_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.49/0.68        | ~ (l1_orders_2 @ sk_D_1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['69', '70'])).
% 0.49/0.68  thf('72', plain, ((l1_orders_2 @ sk_C)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('73', plain, ((v1_funct_1 @ sk_E_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('74', plain,
% 0.49/0.68      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.49/0.68      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.68  thf('75', plain, ((l1_orders_2 @ sk_D_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('76', plain,
% 0.49/0.68      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.49/0.68        | (m1_subset_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C)))),
% 0.49/0.68      inference('demod', [status(thm)], ['71', '72', '73', '74', '75'])).
% 0.49/0.68  thf('77', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.49/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.49/0.68  thf('78', plain,
% 0.49/0.68      ((m1_subset_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))),
% 0.49/0.68      inference('clc', [status(thm)], ['76', '77'])).
% 0.49/0.68  thf('79', plain,
% 0.49/0.68      ((r1_orders_2 @ sk_A @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.68        (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))),
% 0.49/0.68      inference('demod', [status(thm)], ['68', '78'])).
% 0.49/0.68  thf('80', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_E_1 @ 
% 0.49/0.68        (k1_zfmisc_1 @ 
% 0.49/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.49/0.68      inference('demod', [status(thm)], ['0', '1'])).
% 0.49/0.68  thf('81', plain,
% 0.49/0.68      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.68         (~ (l1_orders_2 @ X11)
% 0.49/0.68          | ((sk_G @ X12 @ X11 @ X13)
% 0.49/0.68              = (k1_funct_1 @ X12 @ (sk_E @ X12 @ X11 @ X13)))
% 0.49/0.68          | (v5_orders_3 @ X12 @ X13 @ X11)
% 0.49/0.68          | ~ (m1_subset_1 @ X12 @ 
% 0.49/0.68               (k1_zfmisc_1 @ 
% 0.49/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.49/0.68          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.49/0.68          | ~ (v1_funct_1 @ X12)
% 0.49/0.68          | ~ (l1_orders_2 @ X13))),
% 0.49/0.68      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.49/0.68  thf('82', plain,
% 0.49/0.68      ((~ (l1_orders_2 @ sk_C)
% 0.49/0.68        | ~ (v1_funct_1 @ sk_E_1)
% 0.49/0.68        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.49/0.68             (u1_struct_0 @ sk_D_1))
% 0.49/0.68        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.49/0.68        | ((sk_G @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.49/0.68            = (k1_funct_1 @ sk_E_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C)))
% 0.49/0.68        | ~ (l1_orders_2 @ sk_D_1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['80', '81'])).
% 0.49/0.68  thf('83', plain, ((l1_orders_2 @ sk_C)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('84', plain, ((v1_funct_1 @ sk_E_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('85', plain,
% 0.49/0.68      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.49/0.68      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.68  thf('86', plain, ((l1_orders_2 @ sk_D_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('87', plain,
% 0.49/0.68      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.49/0.68        | ((sk_G @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.49/0.68            = (k1_funct_1 @ sk_E_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))))),
% 0.49/0.68      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 0.49/0.68  thf('88', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.49/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.49/0.68  thf('89', plain,
% 0.49/0.68      (((sk_G @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.49/0.68         = (k1_funct_1 @ sk_E_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.49/0.68      inference('clc', [status(thm)], ['87', '88'])).
% 0.49/0.68  thf('90', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_E_1 @ 
% 0.49/0.68        (k1_zfmisc_1 @ 
% 0.49/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.49/0.68      inference('demod', [status(thm)], ['0', '1'])).
% 0.49/0.68  thf('91', plain,
% 0.49/0.68      (((g1_orders_2 @ (u1_struct_0 @ sk_B) @ (u1_orders_2 @ sk_B))
% 0.49/0.68         = (g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('92', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         ((m1_subset_1 @ (u1_orders_2 @ X0) @ 
% 0.49/0.68           (k1_zfmisc_1 @ 
% 0.49/0.68            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))
% 0.49/0.68          | ~ (l1_orders_2 @ X0))),
% 0.49/0.68      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.49/0.68  thf('93', plain,
% 0.49/0.68      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.49/0.68         (((g1_orders_2 @ X3 @ X4) != (g1_orders_2 @ X1 @ X2))
% 0.49/0.68          | ((X3) = (X1))
% 0.49/0.68          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X3))))),
% 0.49/0.68      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.49/0.68  thf('94', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.68         (~ (l1_orders_2 @ X0)
% 0.49/0.68          | ((u1_struct_0 @ X0) = (X1))
% 0.49/0.68          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.49/0.68              != (g1_orders_2 @ X1 @ X2)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['92', '93'])).
% 0.49/0.68  thf('95', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (((g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1))
% 0.49/0.68            != (g1_orders_2 @ X1 @ X0))
% 0.49/0.68          | ((u1_struct_0 @ sk_B) = (X1))
% 0.49/0.68          | ~ (l1_orders_2 @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['91', '94'])).
% 0.49/0.68  thf('96', plain, ((l1_orders_2 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('97', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (((g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1))
% 0.49/0.68            != (g1_orders_2 @ X1 @ X0))
% 0.49/0.68          | ((u1_struct_0 @ sk_B) = (X1)))),
% 0.49/0.68      inference('demod', [status(thm)], ['95', '96'])).
% 0.49/0.68  thf('98', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_D_1))),
% 0.49/0.68      inference('eq_res', [status(thm)], ['97'])).
% 0.49/0.68  thf('99', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_C))),
% 0.49/0.68      inference('eq_res', [status(thm)], ['53'])).
% 0.49/0.68  thf('100', plain,
% 0.49/0.68      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.49/0.68         (~ (l1_orders_2 @ X11)
% 0.49/0.68          | ~ (v5_orders_3 @ X12 @ X13 @ X11)
% 0.49/0.68          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.49/0.68          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X11))
% 0.49/0.68          | (r1_orders_2 @ X11 @ X16 @ X15)
% 0.49/0.68          | ((X15) != (k1_funct_1 @ X12 @ X14))
% 0.49/0.68          | ((X16) != (k1_funct_1 @ X12 @ X17))
% 0.49/0.68          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X11))
% 0.49/0.68          | ~ (r1_orders_2 @ X13 @ X17 @ X14)
% 0.49/0.68          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X13))
% 0.49/0.68          | ~ (m1_subset_1 @ X12 @ 
% 0.49/0.68               (k1_zfmisc_1 @ 
% 0.49/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.49/0.68          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.49/0.68          | ~ (v1_funct_1 @ X12)
% 0.49/0.68          | ~ (l1_orders_2 @ X13))),
% 0.49/0.68      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.49/0.68  thf('101', plain,
% 0.49/0.68      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X17 : $i]:
% 0.49/0.68         (~ (l1_orders_2 @ X13)
% 0.49/0.68          | ~ (v1_funct_1 @ X12)
% 0.49/0.68          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.49/0.68          | ~ (m1_subset_1 @ X12 @ 
% 0.49/0.68               (k1_zfmisc_1 @ 
% 0.49/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.49/0.68          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X13))
% 0.49/0.68          | ~ (r1_orders_2 @ X13 @ X17 @ X14)
% 0.49/0.68          | ~ (m1_subset_1 @ (k1_funct_1 @ X12 @ X17) @ (u1_struct_0 @ X11))
% 0.49/0.68          | (r1_orders_2 @ X11 @ (k1_funct_1 @ X12 @ X17) @ 
% 0.49/0.68             (k1_funct_1 @ X12 @ X14))
% 0.49/0.68          | ~ (m1_subset_1 @ (k1_funct_1 @ X12 @ X14) @ (u1_struct_0 @ X11))
% 0.49/0.68          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.49/0.68          | ~ (v5_orders_3 @ X12 @ X13 @ X11)
% 0.49/0.68          | ~ (l1_orders_2 @ X11))),
% 0.49/0.68      inference('simplify', [status(thm)], ['100'])).
% 0.49/0.68  thf('102', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X1 @ 
% 0.49/0.68             (k1_zfmisc_1 @ 
% 0.49/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.49/0.68          | ~ (l1_orders_2 @ X0)
% 0.49/0.68          | ~ (v5_orders_3 @ X1 @ sk_A @ X0)
% 0.49/0.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 0.49/0.68          | ~ (m1_subset_1 @ (k1_funct_1 @ X1 @ X2) @ (u1_struct_0 @ X0))
% 0.49/0.68          | (r1_orders_2 @ X0 @ (k1_funct_1 @ X1 @ X3) @ (k1_funct_1 @ X1 @ X2))
% 0.49/0.68          | ~ (m1_subset_1 @ (k1_funct_1 @ X1 @ X3) @ (u1_struct_0 @ X0))
% 0.49/0.68          | ~ (r1_orders_2 @ sk_A @ X3 @ X2)
% 0.49/0.68          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_A))
% 0.49/0.68          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ X0))
% 0.49/0.68          | ~ (v1_funct_1 @ X1)
% 0.49/0.68          | ~ (l1_orders_2 @ sk_A))),
% 0.49/0.68      inference('sup-', [status(thm)], ['99', '101'])).
% 0.49/0.68  thf('103', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_C))),
% 0.49/0.68      inference('eq_res', [status(thm)], ['53'])).
% 0.49/0.68  thf('104', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_C))),
% 0.49/0.68      inference('eq_res', [status(thm)], ['53'])).
% 0.49/0.68  thf('105', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_C))),
% 0.49/0.68      inference('eq_res', [status(thm)], ['53'])).
% 0.49/0.68  thf('106', plain, ((l1_orders_2 @ sk_A)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('107', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X1 @ 
% 0.49/0.68             (k1_zfmisc_1 @ 
% 0.49/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))))
% 0.49/0.68          | ~ (l1_orders_2 @ X0)
% 0.49/0.68          | ~ (v5_orders_3 @ X1 @ sk_A @ X0)
% 0.49/0.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C))
% 0.49/0.68          | ~ (m1_subset_1 @ (k1_funct_1 @ X1 @ X2) @ (u1_struct_0 @ X0))
% 0.49/0.68          | (r1_orders_2 @ X0 @ (k1_funct_1 @ X1 @ X3) @ (k1_funct_1 @ X1 @ X2))
% 0.49/0.68          | ~ (m1_subset_1 @ (k1_funct_1 @ X1 @ X3) @ (u1_struct_0 @ X0))
% 0.49/0.68          | ~ (r1_orders_2 @ sk_A @ X3 @ X2)
% 0.49/0.68          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ sk_C))
% 0.49/0.68          | ~ (v1_funct_2 @ X1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ X0))
% 0.49/0.68          | ~ (v1_funct_1 @ X1))),
% 0.49/0.68      inference('demod', [status(thm)], ['102', '103', '104', '105', '106'])).
% 0.49/0.68  thf('108', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X0 @ 
% 0.49/0.68             (k1_zfmisc_1 @ 
% 0.49/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))
% 0.49/0.68          | ~ (v1_funct_1 @ X0)
% 0.49/0.68          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_B))
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C))
% 0.49/0.68          | ~ (r1_orders_2 @ sk_A @ X1 @ X2)
% 0.49/0.68          | ~ (m1_subset_1 @ (k1_funct_1 @ X0 @ X1) @ (u1_struct_0 @ sk_B))
% 0.49/0.68          | (r1_orders_2 @ sk_B @ (k1_funct_1 @ X0 @ X1) @ 
% 0.49/0.68             (k1_funct_1 @ X0 @ X2))
% 0.49/0.68          | ~ (m1_subset_1 @ (k1_funct_1 @ X0 @ X2) @ (u1_struct_0 @ sk_B))
% 0.49/0.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C))
% 0.49/0.68          | ~ (v5_orders_3 @ X0 @ sk_A @ sk_B)
% 0.49/0.68          | ~ (l1_orders_2 @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['98', '107'])).
% 0.49/0.68  thf('109', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_D_1))),
% 0.49/0.68      inference('eq_res', [status(thm)], ['97'])).
% 0.49/0.68  thf('110', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_D_1))),
% 0.49/0.68      inference('eq_res', [status(thm)], ['97'])).
% 0.49/0.68  thf('111', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_D_1))),
% 0.49/0.68      inference('eq_res', [status(thm)], ['97'])).
% 0.49/0.68  thf('112', plain, ((l1_orders_2 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('113', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X0 @ 
% 0.49/0.68             (k1_zfmisc_1 @ 
% 0.49/0.68              (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))
% 0.49/0.68          | ~ (v1_funct_1 @ X0)
% 0.49/0.68          | ~ (v1_funct_2 @ X0 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C))
% 0.49/0.68          | ~ (r1_orders_2 @ sk_A @ X1 @ X2)
% 0.49/0.68          | ~ (m1_subset_1 @ (k1_funct_1 @ X0 @ X1) @ (u1_struct_0 @ sk_D_1))
% 0.49/0.68          | (r1_orders_2 @ sk_B @ (k1_funct_1 @ X0 @ X1) @ 
% 0.49/0.68             (k1_funct_1 @ X0 @ X2))
% 0.49/0.68          | ~ (m1_subset_1 @ (k1_funct_1 @ X0 @ X2) @ (u1_struct_0 @ sk_D_1))
% 0.49/0.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C))
% 0.49/0.68          | ~ (v5_orders_3 @ X0 @ sk_A @ sk_B))),
% 0.49/0.68      inference('demod', [status(thm)], ['108', '109', '110', '111', '112'])).
% 0.49/0.68  thf('114', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (v5_orders_3 @ sk_E_1 @ sk_A @ sk_B)
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.49/0.68          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X0) @ 
% 0.49/0.68               (u1_struct_0 @ sk_D_1))
% 0.49/0.68          | (r1_orders_2 @ sk_B @ (k1_funct_1 @ sk_E_1 @ X1) @ 
% 0.49/0.68             (k1_funct_1 @ sk_E_1 @ X0))
% 0.49/0.68          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X1) @ 
% 0.49/0.68               (u1_struct_0 @ sk_D_1))
% 0.49/0.68          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C))
% 0.49/0.68          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.49/0.68               (u1_struct_0 @ sk_D_1))
% 0.49/0.68          | ~ (v1_funct_1 @ sk_E_1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['90', '113'])).
% 0.49/0.68  thf('115', plain, ((v5_orders_3 @ sk_E_1 @ sk_A @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('116', plain,
% 0.49/0.68      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.49/0.68      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.68  thf('117', plain, ((v1_funct_1 @ sk_E_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('118', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.49/0.68          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X0) @ 
% 0.49/0.68               (u1_struct_0 @ sk_D_1))
% 0.49/0.68          | (r1_orders_2 @ sk_B @ (k1_funct_1 @ sk_E_1 @ X1) @ 
% 0.49/0.68             (k1_funct_1 @ sk_E_1 @ X0))
% 0.49/0.68          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X1) @ 
% 0.49/0.68               (u1_struct_0 @ sk_D_1))
% 0.49/0.68          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C)))),
% 0.49/0.68      inference('demod', [status(thm)], ['114', '115', '116', '117'])).
% 0.49/0.68  thf('119', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.68             (u1_struct_0 @ sk_D_1))
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.49/0.68          | ~ (r1_orders_2 @ sk_A @ X0 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.49/0.68          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X0) @ 
% 0.49/0.68               (u1_struct_0 @ sk_D_1))
% 0.49/0.68          | (r1_orders_2 @ sk_B @ (k1_funct_1 @ sk_E_1 @ X0) @ 
% 0.49/0.68             (k1_funct_1 @ sk_E_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C)))
% 0.49/0.68          | ~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.68               (u1_struct_0 @ sk_C)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['89', '118'])).
% 0.49/0.68  thf('120', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_E_1 @ 
% 0.49/0.68        (k1_zfmisc_1 @ 
% 0.49/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.49/0.68      inference('demod', [status(thm)], ['0', '1'])).
% 0.49/0.68  thf('121', plain,
% 0.49/0.68      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.68         (~ (l1_orders_2 @ X11)
% 0.49/0.68          | (m1_subset_1 @ (sk_G @ X12 @ X11 @ X13) @ (u1_struct_0 @ X11))
% 0.49/0.68          | (v5_orders_3 @ X12 @ X13 @ X11)
% 0.49/0.68          | ~ (m1_subset_1 @ X12 @ 
% 0.49/0.68               (k1_zfmisc_1 @ 
% 0.49/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.49/0.68          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.49/0.68          | ~ (v1_funct_1 @ X12)
% 0.49/0.68          | ~ (l1_orders_2 @ X13))),
% 0.49/0.68      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.49/0.68  thf('122', plain,
% 0.49/0.68      ((~ (l1_orders_2 @ sk_C)
% 0.49/0.68        | ~ (v1_funct_1 @ sk_E_1)
% 0.49/0.68        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.49/0.68             (u1_struct_0 @ sk_D_1))
% 0.49/0.68        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.49/0.68        | (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.68           (u1_struct_0 @ sk_D_1))
% 0.49/0.68        | ~ (l1_orders_2 @ sk_D_1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['120', '121'])).
% 0.49/0.68  thf('123', plain, ((l1_orders_2 @ sk_C)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('124', plain, ((v1_funct_1 @ sk_E_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('125', plain,
% 0.49/0.68      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.49/0.68      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.68  thf('126', plain, ((l1_orders_2 @ sk_D_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('127', plain,
% 0.49/0.68      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.49/0.68        | (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.68           (u1_struct_0 @ sk_D_1)))),
% 0.49/0.68      inference('demod', [status(thm)], ['122', '123', '124', '125', '126'])).
% 0.49/0.68  thf('128', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.49/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.49/0.68  thf('129', plain,
% 0.49/0.68      ((m1_subset_1 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.49/0.68      inference('clc', [status(thm)], ['127', '128'])).
% 0.49/0.68  thf('130', plain,
% 0.49/0.68      (((sk_G @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.49/0.68         = (k1_funct_1 @ sk_E_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.49/0.68      inference('clc', [status(thm)], ['87', '88'])).
% 0.49/0.68  thf('131', plain,
% 0.49/0.68      ((m1_subset_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))),
% 0.49/0.68      inference('clc', [status(thm)], ['33', '34'])).
% 0.49/0.68  thf('132', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.49/0.68          | ~ (r1_orders_2 @ sk_A @ X0 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.49/0.68          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X0) @ 
% 0.49/0.68               (u1_struct_0 @ sk_D_1))
% 0.49/0.68          | (r1_orders_2 @ sk_B @ (k1_funct_1 @ sk_E_1 @ X0) @ 
% 0.49/0.68             (sk_G @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.49/0.68      inference('demod', [status(thm)], ['119', '129', '130', '131'])).
% 0.49/0.68  thf('133', plain,
% 0.49/0.68      (((r1_orders_2 @ sk_B @ 
% 0.49/0.68         (k1_funct_1 @ sk_E_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C)) @ 
% 0.49/0.68         (sk_G @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.49/0.68        | ~ (m1_subset_1 @ 
% 0.49/0.68             (k1_funct_1 @ sk_E_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C)) @ 
% 0.49/0.68             (u1_struct_0 @ sk_D_1))
% 0.49/0.68        | ~ (m1_subset_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.68             (u1_struct_0 @ sk_C)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['79', '132'])).
% 0.49/0.68  thf('134', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_E_1 @ 
% 0.49/0.68        (k1_zfmisc_1 @ 
% 0.49/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.49/0.68      inference('demod', [status(thm)], ['0', '1'])).
% 0.49/0.68  thf('135', plain,
% 0.49/0.68      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.68         (~ (l1_orders_2 @ X11)
% 0.49/0.68          | ((sk_F @ X12 @ X11 @ X13)
% 0.49/0.68              = (k1_funct_1 @ X12 @ (sk_D @ X12 @ X11 @ X13)))
% 0.49/0.68          | (v5_orders_3 @ X12 @ X13 @ X11)
% 0.49/0.68          | ~ (m1_subset_1 @ X12 @ 
% 0.49/0.68               (k1_zfmisc_1 @ 
% 0.49/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.49/0.68          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.49/0.68          | ~ (v1_funct_1 @ X12)
% 0.49/0.68          | ~ (l1_orders_2 @ X13))),
% 0.49/0.68      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.49/0.68  thf('136', plain,
% 0.49/0.68      ((~ (l1_orders_2 @ sk_C)
% 0.49/0.68        | ~ (v1_funct_1 @ sk_E_1)
% 0.49/0.68        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.49/0.68             (u1_struct_0 @ sk_D_1))
% 0.49/0.68        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.49/0.68        | ((sk_F @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.49/0.68            = (k1_funct_1 @ sk_E_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C)))
% 0.49/0.68        | ~ (l1_orders_2 @ sk_D_1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['134', '135'])).
% 0.49/0.68  thf('137', plain, ((l1_orders_2 @ sk_C)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('138', plain, ((v1_funct_1 @ sk_E_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('139', plain,
% 0.49/0.68      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.49/0.68      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.68  thf('140', plain, ((l1_orders_2 @ sk_D_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('141', plain,
% 0.49/0.68      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.49/0.68        | ((sk_F @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.49/0.68            = (k1_funct_1 @ sk_E_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C))))),
% 0.49/0.68      inference('demod', [status(thm)], ['136', '137', '138', '139', '140'])).
% 0.49/0.68  thf('142', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.49/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.49/0.68  thf('143', plain,
% 0.49/0.68      (((sk_F @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.49/0.68         = (k1_funct_1 @ sk_E_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.49/0.68      inference('clc', [status(thm)], ['141', '142'])).
% 0.49/0.68  thf('144', plain,
% 0.49/0.68      (((sk_F @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.49/0.68         = (k1_funct_1 @ sk_E_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.49/0.68      inference('clc', [status(thm)], ['141', '142'])).
% 0.49/0.68  thf('145', plain,
% 0.49/0.68      ((m1_subset_1 @ sk_E_1 @ 
% 0.49/0.68        (k1_zfmisc_1 @ 
% 0.49/0.68         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.49/0.68      inference('demod', [status(thm)], ['0', '1'])).
% 0.49/0.68  thf('146', plain,
% 0.49/0.68      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.49/0.68         (~ (l1_orders_2 @ X11)
% 0.49/0.68          | (m1_subset_1 @ (sk_F @ X12 @ X11 @ X13) @ (u1_struct_0 @ X11))
% 0.49/0.68          | (v5_orders_3 @ X12 @ X13 @ X11)
% 0.49/0.68          | ~ (m1_subset_1 @ X12 @ 
% 0.49/0.68               (k1_zfmisc_1 @ 
% 0.49/0.68                (k2_zfmisc_1 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))))
% 0.49/0.68          | ~ (v1_funct_2 @ X12 @ (u1_struct_0 @ X13) @ (u1_struct_0 @ X11))
% 0.49/0.68          | ~ (v1_funct_1 @ X12)
% 0.49/0.68          | ~ (l1_orders_2 @ X13))),
% 0.49/0.68      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.49/0.68  thf('147', plain,
% 0.49/0.68      ((~ (l1_orders_2 @ sk_C)
% 0.49/0.68        | ~ (v1_funct_1 @ sk_E_1)
% 0.49/0.68        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.49/0.68             (u1_struct_0 @ sk_D_1))
% 0.49/0.68        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.49/0.68        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.68           (u1_struct_0 @ sk_D_1))
% 0.49/0.68        | ~ (l1_orders_2 @ sk_D_1))),
% 0.49/0.68      inference('sup-', [status(thm)], ['145', '146'])).
% 0.49/0.68  thf('148', plain, ((l1_orders_2 @ sk_C)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('149', plain, ((v1_funct_1 @ sk_E_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('150', plain,
% 0.49/0.68      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.49/0.68      inference('demod', [status(thm)], ['7', '8'])).
% 0.49/0.68  thf('151', plain, ((l1_orders_2 @ sk_D_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('152', plain,
% 0.49/0.68      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.49/0.68        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.68           (u1_struct_0 @ sk_D_1)))),
% 0.49/0.68      inference('demod', [status(thm)], ['147', '148', '149', '150', '151'])).
% 0.49/0.68  thf('153', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.49/0.68      inference('demod', [status(thm)], ['12', '13'])).
% 0.49/0.68  thf('154', plain,
% 0.49/0.68      ((m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.49/0.68      inference('clc', [status(thm)], ['152', '153'])).
% 0.49/0.68  thf('155', plain,
% 0.49/0.68      ((m1_subset_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))),
% 0.49/0.68      inference('clc', [status(thm)], ['76', '77'])).
% 0.49/0.68  thf('156', plain,
% 0.49/0.68      ((r1_orders_2 @ sk_B @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.68        (sk_G @ sk_E_1 @ sk_D_1 @ sk_C))),
% 0.49/0.68      inference('demod', [status(thm)], ['133', '143', '144', '154', '155'])).
% 0.49/0.68  thf('157', plain,
% 0.49/0.68      ((m1_subset_1 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.49/0.68      inference('clc', [status(thm)], ['127', '128'])).
% 0.49/0.68  thf('158', plain,
% 0.49/0.68      (((g1_orders_2 @ (u1_struct_0 @ sk_B) @ (u1_orders_2 @ sk_B))
% 0.49/0.68         = (g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('159', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.68         (~ (l1_orders_2 @ X0)
% 0.49/0.68          | ((u1_orders_2 @ X0) = (X1))
% 0.49/0.68          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.49/0.68              != (g1_orders_2 @ X2 @ X1)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['37', '38'])).
% 0.49/0.68  thf('160', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (((g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1))
% 0.49/0.68            != (g1_orders_2 @ X1 @ X0))
% 0.49/0.68          | ((u1_orders_2 @ sk_B) = (X0))
% 0.49/0.68          | ~ (l1_orders_2 @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['158', '159'])).
% 0.49/0.68  thf('161', plain, ((l1_orders_2 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('162', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (((g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1))
% 0.49/0.68            != (g1_orders_2 @ X1 @ X0))
% 0.49/0.68          | ((u1_orders_2 @ sk_B) = (X0)))),
% 0.49/0.68      inference('demod', [status(thm)], ['160', '161'])).
% 0.49/0.68  thf('163', plain, (((u1_orders_2 @ sk_B) = (u1_orders_2 @ sk_D_1))),
% 0.49/0.68      inference('eq_res', [status(thm)], ['162'])).
% 0.49/0.68  thf('164', plain,
% 0.49/0.68      (![X5 : $i, X7 : $i, X8 : $i, X10 : $i]:
% 0.49/0.68         (~ (l1_orders_2 @ X7)
% 0.49/0.68          | ((g1_orders_2 @ (u1_struct_0 @ X7) @ (u1_orders_2 @ X7))
% 0.49/0.68              != (g1_orders_2 @ (u1_struct_0 @ X5) @ (u1_orders_2 @ X5)))
% 0.49/0.68          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X7))
% 0.49/0.68          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X5))
% 0.49/0.68          | (r1_orders_2 @ X5 @ X10 @ X8)
% 0.49/0.68          | ~ (r1_orders_2 @ X7 @ X10 @ X8)
% 0.49/0.68          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X5))
% 0.49/0.68          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.49/0.68          | ~ (l1_orders_2 @ X5))),
% 0.49/0.68      inference('simplify', [status(thm)], ['55'])).
% 0.49/0.68  thf('165', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.68         (((g1_orders_2 @ (u1_struct_0 @ sk_B) @ (u1_orders_2 @ sk_D_1))
% 0.49/0.68            != (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 0.49/0.68          | ~ (l1_orders_2 @ X0)
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.49/0.68          | ~ (r1_orders_2 @ sk_B @ X2 @ X1)
% 0.49/0.68          | (r1_orders_2 @ X0 @ X2 @ X1)
% 0.49/0.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.49/0.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_B))
% 0.49/0.68          | ~ (l1_orders_2 @ sk_B))),
% 0.49/0.68      inference('sup-', [status(thm)], ['163', '164'])).
% 0.49/0.68  thf('166', plain,
% 0.49/0.68      (((g1_orders_2 @ (u1_struct_0 @ sk_B) @ (u1_orders_2 @ sk_B))
% 0.49/0.68         = (g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1)))),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('167', plain, (((u1_orders_2 @ sk_B) = (u1_orders_2 @ sk_D_1))),
% 0.49/0.68      inference('eq_res', [status(thm)], ['162'])).
% 0.49/0.68  thf('168', plain,
% 0.49/0.68      (((g1_orders_2 @ (u1_struct_0 @ sk_B) @ (u1_orders_2 @ sk_D_1))
% 0.49/0.68         = (g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1)))),
% 0.49/0.68      inference('demod', [status(thm)], ['166', '167'])).
% 0.49/0.68  thf('169', plain, ((l1_orders_2 @ sk_B)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('170', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.68         (((g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1))
% 0.49/0.68            != (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 0.49/0.68          | ~ (l1_orders_2 @ X0)
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.49/0.68          | ~ (r1_orders_2 @ sk_B @ X2 @ X1)
% 0.49/0.68          | (r1_orders_2 @ X0 @ X2 @ X1)
% 0.49/0.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.49/0.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_B)))),
% 0.49/0.68      inference('demod', [status(thm)], ['165', '168', '169'])).
% 0.49/0.68  thf('171', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_D_1))),
% 0.49/0.68      inference('eq_res', [status(thm)], ['97'])).
% 0.49/0.68  thf('172', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_D_1))),
% 0.49/0.68      inference('eq_res', [status(thm)], ['97'])).
% 0.49/0.68  thf('173', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.68         (((g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1))
% 0.49/0.68            != (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 0.49/0.68          | ~ (l1_orders_2 @ X0)
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.49/0.68          | ~ (r1_orders_2 @ sk_B @ X2 @ X1)
% 0.49/0.68          | (r1_orders_2 @ X0 @ X2 @ X1)
% 0.49/0.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.49/0.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1)))),
% 0.49/0.68      inference('demod', [status(thm)], ['170', '171', '172'])).
% 0.49/0.68  thf('174', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.49/0.68          | (r1_orders_2 @ sk_D_1 @ X0 @ X1)
% 0.49/0.68          | ~ (r1_orders_2 @ sk_B @ X0 @ X1)
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.49/0.68          | ~ (l1_orders_2 @ sk_D_1))),
% 0.49/0.68      inference('eq_res', [status(thm)], ['173'])).
% 0.49/0.68  thf('175', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (l1_orders_2 @ sk_D_1)
% 0.49/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.49/0.68          | ~ (r1_orders_2 @ sk_B @ X0 @ X1)
% 0.49/0.68          | (r1_orders_2 @ sk_D_1 @ X0 @ X1)
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.49/0.68      inference('simplify', [status(thm)], ['174'])).
% 0.49/0.68  thf('176', plain, ((l1_orders_2 @ sk_D_1)),
% 0.49/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.68  thf('177', plain,
% 0.49/0.68      (![X0 : $i, X1 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.49/0.68          | ~ (r1_orders_2 @ sk_B @ X0 @ X1)
% 0.49/0.68          | (r1_orders_2 @ sk_D_1 @ X0 @ X1)
% 0.49/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.49/0.68      inference('demod', [status(thm)], ['175', '176'])).
% 0.49/0.68  thf('178', plain,
% 0.49/0.68      (![X0 : $i]:
% 0.49/0.68         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.49/0.68          | (r1_orders_2 @ sk_D_1 @ X0 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.49/0.68          | ~ (r1_orders_2 @ sk_B @ X0 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['157', '177'])).
% 0.49/0.68  thf('179', plain,
% 0.49/0.68      (((r1_orders_2 @ sk_D_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.68         (sk_G @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.49/0.68        | ~ (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.68             (u1_struct_0 @ sk_D_1)))),
% 0.49/0.68      inference('sup-', [status(thm)], ['156', '178'])).
% 0.49/0.68  thf('180', plain,
% 0.49/0.68      ((m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.49/0.68      inference('clc', [status(thm)], ['152', '153'])).
% 0.49/0.68  thf('181', plain,
% 0.49/0.68      ((r1_orders_2 @ sk_D_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.68        (sk_G @ sk_E_1 @ sk_D_1 @ sk_C))),
% 0.49/0.68      inference('demod', [status(thm)], ['179', '180'])).
% 0.49/0.68  thf('182', plain, ($false), inference('demod', [status(thm)], ['15', '181'])).
% 0.49/0.68  
% 0.49/0.68  % SZS output end Refutation
% 0.49/0.68  
% 0.49/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
