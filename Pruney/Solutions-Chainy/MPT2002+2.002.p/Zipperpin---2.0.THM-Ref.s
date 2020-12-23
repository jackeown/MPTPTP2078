%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1V5xCczjcM

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:19 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :  233 (1743 expanded)
%              Number of leaves         :   30 ( 500 expanded)
%              Depth                    :   27
%              Number of atoms          : 2732 (61786 expanded)
%              Number of equality atoms :  117 (2826 expanded)
%              Maximal formula depth    :   25 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_orders_3_type,type,(
    v5_orders_3: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k7_lattice3_type,type,(
    k7_lattice3: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_F_1_type,type,(
    sk_F_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_orders_2 @ X6 )
      | ~ ( r1_orders_2 @ X6 @ ( sk_F @ X7 @ X6 @ X8 ) @ ( sk_G @ X7 @ X6 @ X8 ) )
      | ( v5_orders_3 @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_orders_2 @ X6 )
      | ( r1_orders_2 @ X8 @ ( sk_D @ X7 @ X6 @ X8 ) @ ( sk_E @ X7 @ X6 @ X8 ) )
      | ( v5_orders_3 @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_orders_2 @ X6 )
      | ( m1_subset_1 @ ( sk_E @ X7 @ X6 @ X8 ) @ ( u1_struct_0 @ X8 ) )
      | ( v5_orders_3 @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
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

thf('37',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( k7_lattice3 @ ( k7_lattice3 @ A ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) )).

thf('38',plain,(
    ! [X5: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X5 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X5 ) @ ( u1_orders_2 @ X5 ) ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_lattice3])).

thf('39',plain,
    ( ( ( k7_lattice3 @ ( k7_lattice3 @ sk_A ) )
      = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k7_lattice3 @ ( k7_lattice3 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( k7_lattice3 @ ( k7_lattice3 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','41'])).

thf('43',plain,(
    ! [X5: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X5 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X5 ) @ ( u1_orders_2 @ X5 ) ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_lattice3])).

thf('44',plain,
    ( ( k7_lattice3 @ ( k7_lattice3 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('45',plain,
    ( ( ( k7_lattice3 @ ( k7_lattice3 @ sk_A ) )
      = ( k7_lattice3 @ ( k7_lattice3 @ sk_C ) ) )
    | ~ ( l1_orders_2 @ sk_C ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( k7_lattice3 @ ( k7_lattice3 @ sk_A ) )
    = ( k7_lattice3 @ ( k7_lattice3 @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( k7_lattice3 @ ( k7_lattice3 @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('49',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( k7_lattice3 @ ( k7_lattice3 @ sk_C ) ) ),
    inference(demod,[status(thm)],['42','47'])).

thf('50',plain,
    ( ( k7_lattice3 @ ( k7_lattice3 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('51',plain,
    ( ( k7_lattice3 @ ( k7_lattice3 @ sk_A ) )
    = ( k7_lattice3 @ ( k7_lattice3 @ sk_C ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('52',plain,
    ( ( k7_lattice3 @ ( k7_lattice3 @ sk_C ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('53',plain,(
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

thf('54',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( g1_orders_2 @ X3 @ X4 )
       != ( g1_orders_2 @ X1 @ X2 ) )
      | ( X4 = X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ sk_C ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_C )
        = X0 )
      | ~ ( l1_orders_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ sk_C ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_C )
        = X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k7_lattice3 @ ( k7_lattice3 @ sk_C ) )
     != ( k7_lattice3 @ ( k7_lattice3 @ sk_C ) ) )
    | ( ( u1_orders_2 @ sk_C )
      = ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','58'])).

thf('60',plain,
    ( ( u1_orders_2 @ sk_C )
    = ( u1_orders_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_C ) )
    = ( k7_lattice3 @ ( k7_lattice3 @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','60'])).

thf('62',plain,
    ( ( k7_lattice3 @ ( k7_lattice3 @ sk_C ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('64',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( g1_orders_2 @ X3 @ X4 )
       != ( g1_orders_2 @ X1 @ X2 ) )
      | ( X3 = X1 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ sk_C ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_C )
        = X1 )
      | ~ ( l1_orders_2 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ sk_C ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_C )
        = X1 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( ( k7_lattice3 @ ( k7_lattice3 @ sk_C ) )
     != ( k7_lattice3 @ ( k7_lattice3 @ sk_C ) ) )
    | ( ( u1_struct_0 @ sk_C )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','68'])).

thf('70',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X5: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X5 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X5 ) @ ( u1_orders_2 @ X5 ) ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_lattice3])).

thf(l20_yellow_6,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ! [F: $i] :
                          ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) )
                         => ( ( ( C = E )
                              & ( D = F )
                              & ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
                                = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
                              & ( r1_orders_2 @ A @ C @ D ) )
                           => ( r1_orders_2 @ B @ E @ F ) ) ) ) ) ) ) ) )).

thf('72',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ( r1_orders_2 @ X13 @ X17 @ X16 )
      | ( X14 != X16 )
      | ~ ( r1_orders_2 @ X15 @ X18 @ X14 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X15 ) @ ( u1_orders_2 @ X15 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X13 ) @ ( u1_orders_2 @ X13 ) ) )
      | ( X18 != X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l20_yellow_6])).

thf('73',plain,(
    ! [X13: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X13 ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X15 ) @ ( u1_orders_2 @ X15 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X13 ) @ ( u1_orders_2 @ X13 ) ) )
      | ~ ( r1_orders_2 @ X15 @ X17 @ X16 )
      | ( r1_orders_2 @ X13 @ X17 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X1 ) @ ( u1_orders_2 @ X1 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_orders_2 @ X1 @ X3 @ X2 )
      | ~ ( r1_orders_2 @ X0 @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X0 @ X3 @ X2 )
      | ( r1_orders_2 @ X1 @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X1 ) @ ( u1_orders_2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X2 @ X1 )
      | ~ ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','75'])).

thf('77',plain,
    ( ( u1_orders_2 @ sk_C )
    = ( u1_orders_2 @ sk_A ) ),
    inference(simplify,[status(thm)],['59'])).

thf('78',plain,
    ( ( k7_lattice3 @ ( k7_lattice3 @ sk_C ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('79',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['69'])).

thf('81',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['69'])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
       != ( k7_lattice3 @ ( k7_lattice3 @ sk_C ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_orders_2 @ sk_A @ X2 @ X1 )
      | ~ ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_orders_2 @ sk_C @ X0 @ X1 )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( l1_orders_2 @ sk_C ) ) ),
    inference(eq_res,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_C )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_C @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_C @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_orders_2 @ sk_C @ X0 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) )
      | ( r1_orders_2 @ sk_A @ X0 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['35','86'])).

thf('88',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('90',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_orders_2 @ X6 )
      | ( m1_subset_1 @ ( sk_D @ X7 @ X6 @ X8 ) @ ( u1_struct_0 @ X8 ) )
      | ( v5_orders_3 @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('91',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_orders_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('95',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,
    ( ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['91','92','93','94','95'])).

thf('97',plain,(
    ~ ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('98',plain,(
    m1_subset_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    r1_orders_2 @ sk_A @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['88','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('101',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_orders_2 @ X6 )
      | ( ( sk_G @ X7 @ X6 @ X8 )
        = ( k1_funct_1 @ X7 @ ( sk_E @ X7 @ X6 @ X8 ) ) )
      | ( v5_orders_3 @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('102',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C )
      = ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ) )
    | ~ ( l1_orders_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('106',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C )
      = ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['102','103','104','105','106'])).

thf('108',plain,(
    ~ ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('109',plain,
    ( ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C )
    = ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( l1_orders_2 @ X6 )
      | ~ ( v5_orders_3 @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X6 ) )
      | ( r1_orders_2 @ X6 @ X11 @ X10 )
      | ( X10
       != ( k1_funct_1 @ X7 @ X9 ) )
      | ( X11
       != ( k1_funct_1 @ X7 @ X12 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X6 ) )
      | ~ ( r1_orders_2 @ X8 @ X12 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('112',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X12: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_orders_2 @ X8 @ X12 @ X9 )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ X7 @ X12 ) @ ( u1_struct_0 @ X6 ) )
      | ( r1_orders_2 @ X6 @ ( k1_funct_1 @ X7 @ X12 ) @ ( k1_funct_1 @ X7 @ X9 ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ X7 @ X9 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( v5_orders_3 @ X7 @ X8 @ X6 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_B )
      | ~ ( v5_orders_3 @ sk_E_1 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_orders_2 @ sk_B @ ( k1_funct_1 @ sk_E_1 @ X1 ) @ ( k1_funct_1 @ sk_E_1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','112'])).

thf('114',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v5_orders_3 @ sk_E_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_orders_2 @ sk_B @ ( k1_funct_1 @ sk_E_1 @ X1 ) @ ( k1_funct_1 @ sk_E_1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['113','114','115','116','117','118'])).

thf('120',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['69'])).

thf('121',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X5: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X5 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X5 ) @ ( u1_orders_2 @ X5 ) ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_lattice3])).

thf('123',plain,
    ( ( ( k7_lattice3 @ ( k7_lattice3 @ sk_B ) )
      = ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) ) )
    | ~ ( l1_orders_2 @ sk_B ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,
    ( ( k7_lattice3 @ ( k7_lattice3 @ sk_B ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X5: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X5 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X5 ) @ ( u1_orders_2 @ X5 ) ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_lattice3])).

thf('127',plain,
    ( ( k7_lattice3 @ ( k7_lattice3 @ sk_B ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('128',plain,
    ( ( ( k7_lattice3 @ ( k7_lattice3 @ sk_B ) )
      = ( k7_lattice3 @ ( k7_lattice3 @ sk_D_1 ) ) )
    | ~ ( l1_orders_2 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['126','127'])).

thf('129',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( k7_lattice3 @ ( k7_lattice3 @ sk_B ) )
    = ( k7_lattice3 @ ( k7_lattice3 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('131',plain,
    ( ( k7_lattice3 @ ( k7_lattice3 @ sk_D_1 ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['125','130'])).

thf('132',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ( k7_lattice3 @ ( k7_lattice3 @ sk_B ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('134',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
    = ( k7_lattice3 @ ( k7_lattice3 @ sk_B ) ) ),
    inference(demod,[status(thm)],['132','133'])).

thf('135',plain,
    ( ( k7_lattice3 @ ( k7_lattice3 @ sk_B ) )
    = ( k7_lattice3 @ ( k7_lattice3 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('136',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
    = ( k7_lattice3 @ ( k7_lattice3 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('138',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ sk_D_1 ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B )
        = X1 )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ sk_D_1 ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B )
        = X1 ) ) ),
    inference(demod,[status(thm)],['138','139'])).

thf('141',plain,
    ( ( ( k7_lattice3 @ ( k7_lattice3 @ sk_D_1 ) )
     != ( k7_lattice3 @ ( k7_lattice3 @ sk_D_1 ) ) )
    | ( ( u1_struct_0 @ sk_B )
      = ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['131','140'])).

thf('142',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['141'])).

thf('144',plain,
    ( ( u1_struct_0 @ sk_C )
    = ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['69'])).

thf('145',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_orders_2 @ sk_B @ ( k1_funct_1 @ sk_E_1 @ X1 ) @ ( k1_funct_1 @ sk_E_1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['119','120','142','143','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_orders_2 @ sk_B @ ( k1_funct_1 @ sk_E_1 @ X0 ) @ ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['109','145'])).

thf('147',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('148',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_orders_2 @ X6 )
      | ( m1_subset_1 @ ( sk_G @ X7 @ X6 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ( v5_orders_3 @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('149',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( l1_orders_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('153',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['149','150','151','152','153'])).

thf('155',plain,(
    ~ ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('156',plain,(
    m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,
    ( ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C )
    = ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('158',plain,(
    m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_orders_2 @ sk_B @ ( k1_funct_1 @ sk_E_1 @ X0 ) @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['146','156','157','158'])).

thf('160',plain,
    ( ( r1_orders_2 @ sk_B @ ( k1_funct_1 @ sk_E_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) ) @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['99','159'])).

thf('161',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('162',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_orders_2 @ X6 )
      | ( ( sk_F @ X7 @ X6 @ X8 )
        = ( k1_funct_1 @ X7 @ ( sk_D @ X7 @ X6 @ X8 ) ) )
      | ( v5_orders_3 @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('163',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C )
      = ( k1_funct_1 @ sk_E_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) ) )
    | ~ ( l1_orders_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('167',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C )
      = ( k1_funct_1 @ sk_E_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['163','164','165','166','167'])).

thf('169',plain,(
    ~ ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('170',plain,
    ( ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C )
    = ( k1_funct_1 @ sk_E_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,
    ( ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C )
    = ( k1_funct_1 @ sk_E_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('172',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('173',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_orders_2 @ X6 )
      | ( m1_subset_1 @ ( sk_F @ X7 @ X6 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ( v5_orders_3 @ X7 @ X8 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ X7 @ ( u1_struct_0 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('174',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( l1_orders_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('178',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['174','175','176','177','178'])).

thf('180',plain,(
    ~ ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('181',plain,(
    m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('182',plain,(
    m1_subset_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('183',plain,(
    r1_orders_2 @ sk_B @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['160','170','171','181','182'])).

thf('184',plain,(
    m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('185',plain,
    ( ( k7_lattice3 @ ( k7_lattice3 @ sk_B ) )
    = ( k7_lattice3 @ ( k7_lattice3 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['128','129'])).

thf('186',plain,
    ( ( k7_lattice3 @ ( k7_lattice3 @ sk_D_1 ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['125','130'])).

thf('187',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X0 @ X3 @ X2 )
      | ( r1_orders_2 @ X1 @ X3 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X1 ) @ ( u1_orders_2 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('188',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
       != ( k7_lattice3 @ ( k7_lattice3 @ sk_D_1 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ sk_D_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_orders_2 @ sk_D_1 @ X2 @ X1 )
      | ~ ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('190',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ X0 ) )
       != ( k7_lattice3 @ ( k7_lattice3 @ sk_D_1 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_orders_2 @ sk_D_1 @ X2 @ X1 )
      | ~ ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ sk_D_1 ) )
       != ( k7_lattice3 @ ( k7_lattice3 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_orders_2 @ sk_B @ X0 @ X1 )
      | ( r1_orders_2 @ sk_D_1 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['185','190'])).

thf('192',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['141'])).

thf('193',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_D_1 ) ),
    inference(simplify,[status(thm)],['141'])).

thf('194',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_lattice3 @ ( k7_lattice3 @ sk_D_1 ) )
       != ( k7_lattice3 @ ( k7_lattice3 @ sk_D_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_orders_2 @ sk_B @ X0 @ X1 )
      | ( r1_orders_2 @ sk_D_1 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('196',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_orders_2 @ sk_D_1 @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_B @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_orders_2 @ sk_B @ X0 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) )
      | ( r1_orders_2 @ sk_D_1 @ X0 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['184','196'])).

thf('198',plain,
    ( ( r1_orders_2 @ sk_D_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['183','197'])).

thf('199',plain,(
    m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('200',plain,(
    r1_orders_2 @ sk_D_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['198','199'])).

thf('201',plain,(
    $false ),
    inference(demod,[status(thm)],['15','200'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1V5xCczjcM
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:58:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.67  % Solved by: fo/fo7.sh
% 0.44/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.67  % done 440 iterations in 0.211s
% 0.44/0.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.67  % SZS output start Refutation
% 0.44/0.67  thf(v5_orders_3_type, type, v5_orders_3: $i > $i > $i > $o).
% 0.44/0.67  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.44/0.67  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.44/0.67  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.44/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.44/0.67  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.44/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.67  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.44/0.67  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.44/0.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.44/0.67  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.44/0.67  thf(k7_lattice3_type, type, k7_lattice3: $i > $i).
% 0.44/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.67  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.44/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.67  thf(sk_F_1_type, type, sk_F_1: $i).
% 0.44/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.67  thf(sk_G_type, type, sk_G: $i > $i > $i > $i).
% 0.44/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.67  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.44/0.67  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.44/0.67  thf(t1_waybel_9, conjecture,
% 0.44/0.67    (![A:$i]:
% 0.44/0.67     ( ( l1_orders_2 @ A ) =>
% 0.44/0.67       ( ![B:$i]:
% 0.44/0.67         ( ( l1_orders_2 @ B ) =>
% 0.44/0.67           ( ![C:$i]:
% 0.44/0.67             ( ( ( ~( v2_struct_0 @ C ) ) & ( l1_orders_2 @ C ) ) =>
% 0.44/0.67               ( ![D:$i]:
% 0.44/0.67                 ( ( ( ~( v2_struct_0 @ D ) ) & ( l1_orders_2 @ D ) ) =>
% 0.44/0.67                   ( ![E:$i]:
% 0.44/0.67                     ( ( ( v1_funct_1 @ E ) & 
% 0.44/0.67                         ( v1_funct_2 @
% 0.44/0.67                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.44/0.67                         ( m1_subset_1 @
% 0.44/0.67                           E @ 
% 0.44/0.67                           ( k1_zfmisc_1 @
% 0.44/0.67                             ( k2_zfmisc_1 @
% 0.44/0.67                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.44/0.67                       ( ![F:$i]:
% 0.44/0.67                         ( ( ( v1_funct_1 @ F ) & 
% 0.44/0.67                             ( v1_funct_2 @
% 0.44/0.67                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) & 
% 0.44/0.67                             ( m1_subset_1 @
% 0.44/0.67                               F @ 
% 0.44/0.67                               ( k1_zfmisc_1 @
% 0.44/0.67                                 ( k2_zfmisc_1 @
% 0.44/0.67                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) ) =>
% 0.44/0.67                           ( ( ( ( g1_orders_2 @
% 0.44/0.67                                   ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) =
% 0.44/0.67                                 ( g1_orders_2 @
% 0.44/0.67                                   ( u1_struct_0 @ C ) @ ( u1_orders_2 @ C ) ) ) & 
% 0.44/0.67                               ( ( g1_orders_2 @
% 0.44/0.67                                   ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) =
% 0.44/0.67                                 ( g1_orders_2 @
% 0.44/0.67                                   ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) ) ) & 
% 0.44/0.67                               ( ( E ) = ( F ) ) & ( v5_orders_3 @ E @ A @ B ) ) =>
% 0.44/0.67                             ( v5_orders_3 @ F @ C @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.67    (~( ![A:$i]:
% 0.44/0.67        ( ( l1_orders_2 @ A ) =>
% 0.44/0.67          ( ![B:$i]:
% 0.44/0.67            ( ( l1_orders_2 @ B ) =>
% 0.44/0.67              ( ![C:$i]:
% 0.44/0.67                ( ( ( ~( v2_struct_0 @ C ) ) & ( l1_orders_2 @ C ) ) =>
% 0.44/0.67                  ( ![D:$i]:
% 0.44/0.67                    ( ( ( ~( v2_struct_0 @ D ) ) & ( l1_orders_2 @ D ) ) =>
% 0.44/0.67                      ( ![E:$i]:
% 0.44/0.67                        ( ( ( v1_funct_1 @ E ) & 
% 0.44/0.67                            ( v1_funct_2 @
% 0.44/0.67                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.44/0.67                            ( m1_subset_1 @
% 0.44/0.67                              E @ 
% 0.44/0.67                              ( k1_zfmisc_1 @
% 0.44/0.67                                ( k2_zfmisc_1 @
% 0.44/0.67                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.44/0.67                          ( ![F:$i]:
% 0.44/0.67                            ( ( ( v1_funct_1 @ F ) & 
% 0.44/0.67                                ( v1_funct_2 @
% 0.44/0.67                                  F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) & 
% 0.44/0.67                                ( m1_subset_1 @
% 0.44/0.67                                  F @ 
% 0.44/0.67                                  ( k1_zfmisc_1 @
% 0.44/0.67                                    ( k2_zfmisc_1 @
% 0.44/0.67                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) ) =>
% 0.44/0.67                              ( ( ( ( g1_orders_2 @
% 0.44/0.67                                      ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) =
% 0.44/0.67                                    ( g1_orders_2 @
% 0.44/0.67                                      ( u1_struct_0 @ C ) @ ( u1_orders_2 @ C ) ) ) & 
% 0.44/0.67                                  ( ( g1_orders_2 @
% 0.44/0.67                                      ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) =
% 0.44/0.67                                    ( g1_orders_2 @
% 0.44/0.67                                      ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) ) ) & 
% 0.44/0.67                                  ( ( E ) = ( F ) ) & 
% 0.44/0.67                                  ( v5_orders_3 @ E @ A @ B ) ) =>
% 0.44/0.67                                ( v5_orders_3 @ F @ C @ D ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.44/0.67    inference('cnf.neg', [status(esa)], [t1_waybel_9])).
% 0.44/0.67  thf('0', plain,
% 0.44/0.67      ((m1_subset_1 @ sk_F_1 @ 
% 0.44/0.67        (k1_zfmisc_1 @ 
% 0.44/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('1', plain, (((sk_E_1) = (sk_F_1))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('2', plain,
% 0.44/0.67      ((m1_subset_1 @ sk_E_1 @ 
% 0.44/0.67        (k1_zfmisc_1 @ 
% 0.44/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.44/0.67      inference('demod', [status(thm)], ['0', '1'])).
% 0.44/0.67  thf(d5_orders_3, axiom,
% 0.44/0.67    (![A:$i]:
% 0.44/0.67     ( ( l1_orders_2 @ A ) =>
% 0.44/0.67       ( ![B:$i]:
% 0.44/0.67         ( ( l1_orders_2 @ B ) =>
% 0.44/0.67           ( ![C:$i]:
% 0.44/0.67             ( ( ( v1_funct_1 @ C ) & 
% 0.44/0.67                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.44/0.67                 ( m1_subset_1 @
% 0.44/0.67                   C @ 
% 0.44/0.67                   ( k1_zfmisc_1 @
% 0.44/0.67                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.44/0.67               ( ( v5_orders_3 @ C @ A @ B ) <=>
% 0.44/0.67                 ( ![D:$i]:
% 0.44/0.67                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.67                     ( ![E:$i]:
% 0.44/0.67                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.67                         ( ( r1_orders_2 @ A @ D @ E ) =>
% 0.44/0.67                           ( ![F:$i]:
% 0.44/0.67                             ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.44/0.67                               ( ![G:$i]:
% 0.44/0.67                                 ( ( m1_subset_1 @ G @ ( u1_struct_0 @ B ) ) =>
% 0.44/0.67                                   ( ( ( ( F ) = ( k1_funct_1 @ C @ D ) ) & 
% 0.44/0.67                                       ( ( G ) = ( k1_funct_1 @ C @ E ) ) ) =>
% 0.44/0.67                                     ( r1_orders_2 @ B @ F @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.67  thf('3', plain,
% 0.44/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.67         (~ (l1_orders_2 @ X6)
% 0.44/0.67          | ~ (r1_orders_2 @ X6 @ (sk_F @ X7 @ X6 @ X8) @ (sk_G @ X7 @ X6 @ X8))
% 0.44/0.67          | (v5_orders_3 @ X7 @ X8 @ X6)
% 0.44/0.67          | ~ (m1_subset_1 @ X7 @ 
% 0.44/0.67               (k1_zfmisc_1 @ 
% 0.44/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.44/0.67          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.44/0.67          | ~ (v1_funct_1 @ X7)
% 0.44/0.67          | ~ (l1_orders_2 @ X8))),
% 0.44/0.67      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.44/0.67  thf('4', plain,
% 0.44/0.67      ((~ (l1_orders_2 @ sk_C)
% 0.44/0.67        | ~ (v1_funct_1 @ sk_E_1)
% 0.44/0.67        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.44/0.67             (u1_struct_0 @ sk_D_1))
% 0.44/0.67        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.44/0.67        | ~ (r1_orders_2 @ sk_D_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.67             (sk_G @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.44/0.67        | ~ (l1_orders_2 @ sk_D_1))),
% 0.44/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.44/0.67  thf('5', plain, ((l1_orders_2 @ sk_C)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('6', plain, ((v1_funct_1 @ sk_E_1)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('7', plain,
% 0.44/0.67      ((v1_funct_2 @ sk_F_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('8', plain, (((sk_E_1) = (sk_F_1))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('9', plain,
% 0.44/0.67      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.44/0.67      inference('demod', [status(thm)], ['7', '8'])).
% 0.44/0.67  thf('10', plain, ((l1_orders_2 @ sk_D_1)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('11', plain,
% 0.44/0.67      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.44/0.67        | ~ (r1_orders_2 @ sk_D_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.67             (sk_G @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.44/0.67      inference('demod', [status(thm)], ['4', '5', '6', '9', '10'])).
% 0.44/0.67  thf('12', plain, (~ (v5_orders_3 @ sk_F_1 @ sk_C @ sk_D_1)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('13', plain, (((sk_E_1) = (sk_F_1))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('14', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.44/0.67      inference('demod', [status(thm)], ['12', '13'])).
% 0.44/0.67  thf('15', plain,
% 0.44/0.67      (~ (r1_orders_2 @ sk_D_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.67          (sk_G @ sk_E_1 @ sk_D_1 @ sk_C))),
% 0.44/0.67      inference('clc', [status(thm)], ['11', '14'])).
% 0.44/0.67  thf('16', plain,
% 0.44/0.67      ((m1_subset_1 @ sk_E_1 @ 
% 0.44/0.67        (k1_zfmisc_1 @ 
% 0.44/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.44/0.67      inference('demod', [status(thm)], ['0', '1'])).
% 0.44/0.67  thf('17', plain,
% 0.44/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.67         (~ (l1_orders_2 @ X6)
% 0.44/0.67          | (r1_orders_2 @ X8 @ (sk_D @ X7 @ X6 @ X8) @ (sk_E @ X7 @ X6 @ X8))
% 0.44/0.67          | (v5_orders_3 @ X7 @ X8 @ X6)
% 0.44/0.67          | ~ (m1_subset_1 @ X7 @ 
% 0.44/0.67               (k1_zfmisc_1 @ 
% 0.44/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.44/0.67          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.44/0.67          | ~ (v1_funct_1 @ X7)
% 0.44/0.67          | ~ (l1_orders_2 @ X8))),
% 0.44/0.67      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.44/0.67  thf('18', plain,
% 0.44/0.67      ((~ (l1_orders_2 @ sk_C)
% 0.44/0.67        | ~ (v1_funct_1 @ sk_E_1)
% 0.44/0.67        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.44/0.67             (u1_struct_0 @ sk_D_1))
% 0.44/0.67        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.44/0.67        | (r1_orders_2 @ sk_C @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.67           (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.44/0.67        | ~ (l1_orders_2 @ sk_D_1))),
% 0.44/0.67      inference('sup-', [status(thm)], ['16', '17'])).
% 0.44/0.67  thf('19', plain, ((l1_orders_2 @ sk_C)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('20', plain, ((v1_funct_1 @ sk_E_1)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('21', plain,
% 0.44/0.67      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.44/0.67      inference('demod', [status(thm)], ['7', '8'])).
% 0.44/0.67  thf('22', plain, ((l1_orders_2 @ sk_D_1)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('23', plain,
% 0.44/0.67      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.44/0.67        | (r1_orders_2 @ sk_C @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.67           (sk_E @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.44/0.67      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.44/0.67  thf('24', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.44/0.67      inference('demod', [status(thm)], ['12', '13'])).
% 0.44/0.67  thf('25', plain,
% 0.44/0.67      ((r1_orders_2 @ sk_C @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.67        (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))),
% 0.44/0.67      inference('clc', [status(thm)], ['23', '24'])).
% 0.44/0.67  thf('26', plain,
% 0.44/0.67      ((m1_subset_1 @ sk_E_1 @ 
% 0.44/0.67        (k1_zfmisc_1 @ 
% 0.44/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.44/0.67      inference('demod', [status(thm)], ['0', '1'])).
% 0.44/0.67  thf('27', plain,
% 0.44/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.67         (~ (l1_orders_2 @ X6)
% 0.44/0.67          | (m1_subset_1 @ (sk_E @ X7 @ X6 @ X8) @ (u1_struct_0 @ X8))
% 0.44/0.67          | (v5_orders_3 @ X7 @ X8 @ X6)
% 0.44/0.67          | ~ (m1_subset_1 @ X7 @ 
% 0.44/0.67               (k1_zfmisc_1 @ 
% 0.44/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.44/0.67          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.44/0.67          | ~ (v1_funct_1 @ X7)
% 0.44/0.67          | ~ (l1_orders_2 @ X8))),
% 0.44/0.67      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.44/0.67  thf('28', plain,
% 0.44/0.67      ((~ (l1_orders_2 @ sk_C)
% 0.44/0.67        | ~ (v1_funct_1 @ sk_E_1)
% 0.44/0.67        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.44/0.67             (u1_struct_0 @ sk_D_1))
% 0.44/0.67        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.44/0.67        | (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.44/0.67        | ~ (l1_orders_2 @ sk_D_1))),
% 0.44/0.67      inference('sup-', [status(thm)], ['26', '27'])).
% 0.44/0.67  thf('29', plain, ((l1_orders_2 @ sk_C)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('30', plain, ((v1_funct_1 @ sk_E_1)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('31', plain,
% 0.44/0.67      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.44/0.67      inference('demod', [status(thm)], ['7', '8'])).
% 0.44/0.67  thf('32', plain, ((l1_orders_2 @ sk_D_1)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('33', plain,
% 0.44/0.67      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.44/0.67        | (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C)))),
% 0.44/0.67      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 0.44/0.67  thf('34', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.44/0.67      inference('demod', [status(thm)], ['12', '13'])).
% 0.44/0.67  thf('35', plain,
% 0.44/0.67      ((m1_subset_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))),
% 0.44/0.67      inference('clc', [status(thm)], ['33', '34'])).
% 0.44/0.67  thf('36', plain,
% 0.44/0.67      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.44/0.67         = (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('37', plain,
% 0.44/0.67      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.44/0.67         = (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf(t8_lattice3, axiom,
% 0.44/0.67    (![A:$i]:
% 0.44/0.67     ( ( l1_orders_2 @ A ) =>
% 0.44/0.67       ( ( k7_lattice3 @ ( k7_lattice3 @ A ) ) =
% 0.44/0.67         ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ))).
% 0.44/0.67  thf('38', plain,
% 0.44/0.67      (![X5 : $i]:
% 0.44/0.67         (((k7_lattice3 @ (k7_lattice3 @ X5))
% 0.44/0.67            = (g1_orders_2 @ (u1_struct_0 @ X5) @ (u1_orders_2 @ X5)))
% 0.44/0.67          | ~ (l1_orders_2 @ X5))),
% 0.44/0.67      inference('cnf', [status(esa)], [t8_lattice3])).
% 0.44/0.67  thf('39', plain,
% 0.44/0.67      ((((k7_lattice3 @ (k7_lattice3 @ sk_A))
% 0.44/0.67          = (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))
% 0.44/0.67        | ~ (l1_orders_2 @ sk_A))),
% 0.44/0.67      inference('sup+', [status(thm)], ['37', '38'])).
% 0.44/0.67  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('41', plain,
% 0.44/0.67      (((k7_lattice3 @ (k7_lattice3 @ sk_A))
% 0.44/0.67         = (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))),
% 0.44/0.67      inference('demod', [status(thm)], ['39', '40'])).
% 0.44/0.67  thf('42', plain,
% 0.44/0.67      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.44/0.67         = (k7_lattice3 @ (k7_lattice3 @ sk_A)))),
% 0.44/0.67      inference('demod', [status(thm)], ['36', '41'])).
% 0.44/0.67  thf('43', plain,
% 0.44/0.67      (![X5 : $i]:
% 0.44/0.67         (((k7_lattice3 @ (k7_lattice3 @ X5))
% 0.44/0.67            = (g1_orders_2 @ (u1_struct_0 @ X5) @ (u1_orders_2 @ X5)))
% 0.44/0.67          | ~ (l1_orders_2 @ X5))),
% 0.44/0.67      inference('cnf', [status(esa)], [t8_lattice3])).
% 0.44/0.67  thf('44', plain,
% 0.44/0.67      (((k7_lattice3 @ (k7_lattice3 @ sk_A))
% 0.44/0.67         = (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))),
% 0.44/0.67      inference('demod', [status(thm)], ['39', '40'])).
% 0.44/0.67  thf('45', plain,
% 0.44/0.67      ((((k7_lattice3 @ (k7_lattice3 @ sk_A))
% 0.44/0.67          = (k7_lattice3 @ (k7_lattice3 @ sk_C)))
% 0.44/0.67        | ~ (l1_orders_2 @ sk_C))),
% 0.44/0.67      inference('sup+', [status(thm)], ['43', '44'])).
% 0.44/0.67  thf('46', plain, ((l1_orders_2 @ sk_C)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('47', plain,
% 0.44/0.67      (((k7_lattice3 @ (k7_lattice3 @ sk_A))
% 0.44/0.67         = (k7_lattice3 @ (k7_lattice3 @ sk_C)))),
% 0.44/0.67      inference('demod', [status(thm)], ['45', '46'])).
% 0.44/0.67  thf('48', plain,
% 0.44/0.67      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.44/0.67         = (k7_lattice3 @ (k7_lattice3 @ sk_C)))),
% 0.44/0.67      inference('demod', [status(thm)], ['42', '47'])).
% 0.44/0.67  thf('49', plain,
% 0.44/0.67      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.44/0.67         = (k7_lattice3 @ (k7_lattice3 @ sk_C)))),
% 0.44/0.67      inference('demod', [status(thm)], ['42', '47'])).
% 0.44/0.67  thf('50', plain,
% 0.44/0.67      (((k7_lattice3 @ (k7_lattice3 @ sk_A))
% 0.44/0.67         = (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))),
% 0.44/0.67      inference('demod', [status(thm)], ['39', '40'])).
% 0.44/0.67  thf('51', plain,
% 0.44/0.67      (((k7_lattice3 @ (k7_lattice3 @ sk_A))
% 0.44/0.67         = (k7_lattice3 @ (k7_lattice3 @ sk_C)))),
% 0.44/0.67      inference('demod', [status(thm)], ['45', '46'])).
% 0.44/0.67  thf('52', plain,
% 0.44/0.67      (((k7_lattice3 @ (k7_lattice3 @ sk_C))
% 0.44/0.67         = (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))),
% 0.44/0.67      inference('demod', [status(thm)], ['50', '51'])).
% 0.44/0.67  thf(dt_u1_orders_2, axiom,
% 0.44/0.67    (![A:$i]:
% 0.44/0.67     ( ( l1_orders_2 @ A ) =>
% 0.44/0.67       ( m1_subset_1 @
% 0.44/0.67         ( u1_orders_2 @ A ) @ 
% 0.44/0.67         ( k1_zfmisc_1 @
% 0.44/0.67           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.44/0.67  thf('53', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((m1_subset_1 @ (u1_orders_2 @ X0) @ 
% 0.44/0.67           (k1_zfmisc_1 @ 
% 0.44/0.67            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))
% 0.44/0.67          | ~ (l1_orders_2 @ X0))),
% 0.44/0.67      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.44/0.67  thf(free_g1_orders_2, axiom,
% 0.44/0.67    (![A:$i,B:$i]:
% 0.44/0.67     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.44/0.67       ( ![C:$i,D:$i]:
% 0.44/0.67         ( ( ( g1_orders_2 @ A @ B ) = ( g1_orders_2 @ C @ D ) ) =>
% 0.44/0.67           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.44/0.67  thf('54', plain,
% 0.44/0.67      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.67         (((g1_orders_2 @ X3 @ X4) != (g1_orders_2 @ X1 @ X2))
% 0.44/0.67          | ((X4) = (X2))
% 0.44/0.67          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X3))))),
% 0.44/0.67      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.44/0.67  thf('55', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.67         (~ (l1_orders_2 @ X0)
% 0.44/0.67          | ((u1_orders_2 @ X0) = (X1))
% 0.44/0.67          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.44/0.67              != (g1_orders_2 @ X2 @ X1)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['53', '54'])).
% 0.44/0.67  thf('56', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (((k7_lattice3 @ (k7_lattice3 @ sk_C)) != (g1_orders_2 @ X1 @ X0))
% 0.44/0.67          | ((u1_orders_2 @ sk_C) = (X0))
% 0.44/0.67          | ~ (l1_orders_2 @ sk_C))),
% 0.44/0.67      inference('sup-', [status(thm)], ['52', '55'])).
% 0.44/0.67  thf('57', plain, ((l1_orders_2 @ sk_C)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('58', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (((k7_lattice3 @ (k7_lattice3 @ sk_C)) != (g1_orders_2 @ X1 @ X0))
% 0.44/0.67          | ((u1_orders_2 @ sk_C) = (X0)))),
% 0.44/0.67      inference('demod', [status(thm)], ['56', '57'])).
% 0.44/0.67  thf('59', plain,
% 0.44/0.67      ((((k7_lattice3 @ (k7_lattice3 @ sk_C))
% 0.44/0.67          != (k7_lattice3 @ (k7_lattice3 @ sk_C)))
% 0.44/0.67        | ((u1_orders_2 @ sk_C) = (u1_orders_2 @ sk_A)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['49', '58'])).
% 0.44/0.67  thf('60', plain, (((u1_orders_2 @ sk_C) = (u1_orders_2 @ sk_A))),
% 0.44/0.67      inference('simplify', [status(thm)], ['59'])).
% 0.44/0.67  thf('61', plain,
% 0.44/0.67      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_C))
% 0.44/0.67         = (k7_lattice3 @ (k7_lattice3 @ sk_C)))),
% 0.44/0.67      inference('demod', [status(thm)], ['48', '60'])).
% 0.44/0.67  thf('62', plain,
% 0.44/0.67      (((k7_lattice3 @ (k7_lattice3 @ sk_C))
% 0.44/0.67         = (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))),
% 0.44/0.67      inference('demod', [status(thm)], ['50', '51'])).
% 0.44/0.67  thf('63', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         ((m1_subset_1 @ (u1_orders_2 @ X0) @ 
% 0.44/0.67           (k1_zfmisc_1 @ 
% 0.44/0.67            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))
% 0.44/0.67          | ~ (l1_orders_2 @ X0))),
% 0.44/0.67      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.44/0.67  thf('64', plain,
% 0.44/0.67      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.67         (((g1_orders_2 @ X3 @ X4) != (g1_orders_2 @ X1 @ X2))
% 0.44/0.67          | ((X3) = (X1))
% 0.44/0.67          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X3))))),
% 0.44/0.67      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.44/0.67  thf('65', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.67         (~ (l1_orders_2 @ X0)
% 0.44/0.67          | ((u1_struct_0 @ X0) = (X1))
% 0.44/0.67          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.44/0.67              != (g1_orders_2 @ X1 @ X2)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['63', '64'])).
% 0.44/0.67  thf('66', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (((k7_lattice3 @ (k7_lattice3 @ sk_C)) != (g1_orders_2 @ X1 @ X0))
% 0.44/0.67          | ((u1_struct_0 @ sk_C) = (X1))
% 0.44/0.67          | ~ (l1_orders_2 @ sk_C))),
% 0.44/0.67      inference('sup-', [status(thm)], ['62', '65'])).
% 0.44/0.67  thf('67', plain, ((l1_orders_2 @ sk_C)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('68', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (((k7_lattice3 @ (k7_lattice3 @ sk_C)) != (g1_orders_2 @ X1 @ X0))
% 0.44/0.67          | ((u1_struct_0 @ sk_C) = (X1)))),
% 0.44/0.67      inference('demod', [status(thm)], ['66', '67'])).
% 0.44/0.67  thf('69', plain,
% 0.44/0.67      ((((k7_lattice3 @ (k7_lattice3 @ sk_C))
% 0.44/0.67          != (k7_lattice3 @ (k7_lattice3 @ sk_C)))
% 0.44/0.67        | ((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['61', '68'])).
% 0.44/0.67  thf('70', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.44/0.67      inference('simplify', [status(thm)], ['69'])).
% 0.44/0.67  thf('71', plain,
% 0.44/0.67      (![X5 : $i]:
% 0.44/0.67         (((k7_lattice3 @ (k7_lattice3 @ X5))
% 0.44/0.67            = (g1_orders_2 @ (u1_struct_0 @ X5) @ (u1_orders_2 @ X5)))
% 0.44/0.67          | ~ (l1_orders_2 @ X5))),
% 0.44/0.67      inference('cnf', [status(esa)], [t8_lattice3])).
% 0.44/0.67  thf(l20_yellow_6, axiom,
% 0.44/0.67    (![A:$i]:
% 0.44/0.67     ( ( l1_orders_2 @ A ) =>
% 0.44/0.67       ( ![B:$i]:
% 0.44/0.67         ( ( l1_orders_2 @ B ) =>
% 0.44/0.67           ( ![C:$i]:
% 0.44/0.67             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.67               ( ![D:$i]:
% 0.44/0.67                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.44/0.67                   ( ![E:$i]:
% 0.44/0.67                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.44/0.67                       ( ![F:$i]:
% 0.44/0.67                         ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.44/0.67                           ( ( ( ( C ) = ( E ) ) & ( ( D ) = ( F ) ) & 
% 0.44/0.67                               ( ( g1_orders_2 @
% 0.44/0.67                                   ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) =
% 0.44/0.67                                 ( g1_orders_2 @
% 0.44/0.67                                   ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) ) & 
% 0.44/0.67                               ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.44/0.67                             ( r1_orders_2 @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.44/0.67  thf('72', plain,
% 0.44/0.67      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.44/0.67         (~ (l1_orders_2 @ X13)
% 0.44/0.67          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 0.44/0.67          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X13))
% 0.44/0.67          | (r1_orders_2 @ X13 @ X17 @ X16)
% 0.44/0.67          | ((X14) != (X16))
% 0.44/0.67          | ~ (r1_orders_2 @ X15 @ X18 @ X14)
% 0.44/0.67          | ((g1_orders_2 @ (u1_struct_0 @ X15) @ (u1_orders_2 @ X15))
% 0.44/0.67              != (g1_orders_2 @ (u1_struct_0 @ X13) @ (u1_orders_2 @ X13)))
% 0.44/0.67          | ((X18) != (X17))
% 0.44/0.67          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X13))
% 0.44/0.67          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X15))
% 0.44/0.67          | ~ (l1_orders_2 @ X15))),
% 0.44/0.67      inference('cnf', [status(esa)], [l20_yellow_6])).
% 0.44/0.67  thf('73', plain,
% 0.44/0.67      (![X13 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.67         (~ (l1_orders_2 @ X15)
% 0.44/0.67          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.44/0.67          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X13))
% 0.44/0.67          | ((g1_orders_2 @ (u1_struct_0 @ X15) @ (u1_orders_2 @ X15))
% 0.44/0.67              != (g1_orders_2 @ (u1_struct_0 @ X13) @ (u1_orders_2 @ X13)))
% 0.44/0.67          | ~ (r1_orders_2 @ X15 @ X17 @ X16)
% 0.44/0.67          | (r1_orders_2 @ X13 @ X17 @ X16)
% 0.44/0.67          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X13))
% 0.44/0.67          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 0.44/0.67          | ~ (l1_orders_2 @ X13))),
% 0.44/0.67      inference('simplify', [status(thm)], ['72'])).
% 0.44/0.67  thf('74', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.67         (((k7_lattice3 @ (k7_lattice3 @ X0))
% 0.44/0.67            != (g1_orders_2 @ (u1_struct_0 @ X1) @ (u1_orders_2 @ X1)))
% 0.44/0.67          | ~ (l1_orders_2 @ X0)
% 0.44/0.67          | ~ (l1_orders_2 @ X1)
% 0.44/0.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.44/0.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.44/0.67          | (r1_orders_2 @ X1 @ X3 @ X2)
% 0.44/0.67          | ~ (r1_orders_2 @ X0 @ X3 @ X2)
% 0.44/0.67          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.44/0.67          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 0.44/0.67          | ~ (l1_orders_2 @ X0))),
% 0.44/0.67      inference('sup-', [status(thm)], ['71', '73'])).
% 0.44/0.67  thf('75', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.67         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 0.44/0.67          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.44/0.67          | ~ (r1_orders_2 @ X0 @ X3 @ X2)
% 0.44/0.67          | (r1_orders_2 @ X1 @ X3 @ X2)
% 0.44/0.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.44/0.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.44/0.67          | ~ (l1_orders_2 @ X1)
% 0.44/0.67          | ~ (l1_orders_2 @ X0)
% 0.44/0.67          | ((k7_lattice3 @ (k7_lattice3 @ X0))
% 0.44/0.67              != (g1_orders_2 @ (u1_struct_0 @ X1) @ (u1_orders_2 @ X1))))),
% 0.44/0.67      inference('simplify', [status(thm)], ['74'])).
% 0.44/0.67  thf('76', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.67         (((k7_lattice3 @ (k7_lattice3 @ X0))
% 0.44/0.67            != (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_A)))
% 0.44/0.67          | ~ (l1_orders_2 @ X0)
% 0.44/0.67          | ~ (l1_orders_2 @ sk_A)
% 0.44/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.44/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.44/0.67          | (r1_orders_2 @ sk_A @ X2 @ X1)
% 0.44/0.67          | ~ (r1_orders_2 @ X0 @ X2 @ X1)
% 0.44/0.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_A))
% 0.44/0.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['70', '75'])).
% 0.44/0.67  thf('77', plain, (((u1_orders_2 @ sk_C) = (u1_orders_2 @ sk_A))),
% 0.44/0.67      inference('simplify', [status(thm)], ['59'])).
% 0.44/0.67  thf('78', plain,
% 0.44/0.67      (((k7_lattice3 @ (k7_lattice3 @ sk_C))
% 0.44/0.67         = (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))),
% 0.44/0.67      inference('demod', [status(thm)], ['50', '51'])).
% 0.44/0.67  thf('79', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('80', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.44/0.67      inference('simplify', [status(thm)], ['69'])).
% 0.44/0.67  thf('81', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.44/0.67      inference('simplify', [status(thm)], ['69'])).
% 0.44/0.67  thf('82', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.67         (((k7_lattice3 @ (k7_lattice3 @ X0))
% 0.44/0.67            != (k7_lattice3 @ (k7_lattice3 @ sk_C)))
% 0.44/0.67          | ~ (l1_orders_2 @ X0)
% 0.44/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.44/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C))
% 0.44/0.67          | (r1_orders_2 @ sk_A @ X2 @ X1)
% 0.44/0.67          | ~ (r1_orders_2 @ X0 @ X2 @ X1)
% 0.44/0.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_C))
% 0.44/0.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.44/0.67      inference('demod', [status(thm)], ['76', '77', '78', '79', '80', '81'])).
% 0.44/0.67  thf('83', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.44/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.44/0.67          | ~ (r1_orders_2 @ sk_C @ X0 @ X1)
% 0.44/0.67          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.44/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C))
% 0.44/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C))
% 0.44/0.67          | ~ (l1_orders_2 @ sk_C))),
% 0.44/0.67      inference('eq_res', [status(thm)], ['82'])).
% 0.44/0.67  thf('84', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (~ (l1_orders_2 @ sk_C)
% 0.44/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C))
% 0.44/0.67          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.44/0.67          | ~ (r1_orders_2 @ sk_C @ X0 @ X1)
% 0.44/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.44/0.67      inference('simplify', [status(thm)], ['83'])).
% 0.44/0.67  thf('85', plain, ((l1_orders_2 @ sk_C)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('86', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C))
% 0.44/0.67          | (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.44/0.67          | ~ (r1_orders_2 @ sk_C @ X0 @ X1)
% 0.44/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C)))),
% 0.44/0.67      inference('demod', [status(thm)], ['84', '85'])).
% 0.44/0.67  thf('87', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.44/0.67          | ~ (r1_orders_2 @ sk_C @ X0 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.44/0.67          | (r1_orders_2 @ sk_A @ X0 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['35', '86'])).
% 0.44/0.67  thf('88', plain,
% 0.44/0.67      (((r1_orders_2 @ sk_A @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.67         (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.44/0.67        | ~ (m1_subset_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.67             (u1_struct_0 @ sk_C)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['25', '87'])).
% 0.44/0.67  thf('89', plain,
% 0.44/0.67      ((m1_subset_1 @ sk_E_1 @ 
% 0.44/0.67        (k1_zfmisc_1 @ 
% 0.44/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.44/0.67      inference('demod', [status(thm)], ['0', '1'])).
% 0.44/0.67  thf('90', plain,
% 0.44/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.67         (~ (l1_orders_2 @ X6)
% 0.44/0.67          | (m1_subset_1 @ (sk_D @ X7 @ X6 @ X8) @ (u1_struct_0 @ X8))
% 0.44/0.67          | (v5_orders_3 @ X7 @ X8 @ X6)
% 0.44/0.67          | ~ (m1_subset_1 @ X7 @ 
% 0.44/0.67               (k1_zfmisc_1 @ 
% 0.44/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.44/0.67          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.44/0.67          | ~ (v1_funct_1 @ X7)
% 0.44/0.67          | ~ (l1_orders_2 @ X8))),
% 0.44/0.67      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.44/0.67  thf('91', plain,
% 0.44/0.67      ((~ (l1_orders_2 @ sk_C)
% 0.44/0.67        | ~ (v1_funct_1 @ sk_E_1)
% 0.44/0.67        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.44/0.67             (u1_struct_0 @ sk_D_1))
% 0.44/0.67        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.44/0.67        | (m1_subset_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.44/0.67        | ~ (l1_orders_2 @ sk_D_1))),
% 0.44/0.67      inference('sup-', [status(thm)], ['89', '90'])).
% 0.44/0.67  thf('92', plain, ((l1_orders_2 @ sk_C)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('93', plain, ((v1_funct_1 @ sk_E_1)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('94', plain,
% 0.44/0.67      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.44/0.67      inference('demod', [status(thm)], ['7', '8'])).
% 0.44/0.67  thf('95', plain, ((l1_orders_2 @ sk_D_1)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('96', plain,
% 0.44/0.67      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.44/0.67        | (m1_subset_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C)))),
% 0.44/0.67      inference('demod', [status(thm)], ['91', '92', '93', '94', '95'])).
% 0.44/0.67  thf('97', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.44/0.67      inference('demod', [status(thm)], ['12', '13'])).
% 0.44/0.67  thf('98', plain,
% 0.44/0.67      ((m1_subset_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))),
% 0.44/0.67      inference('clc', [status(thm)], ['96', '97'])).
% 0.44/0.67  thf('99', plain,
% 0.44/0.67      ((r1_orders_2 @ sk_A @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.67        (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))),
% 0.44/0.67      inference('demod', [status(thm)], ['88', '98'])).
% 0.44/0.67  thf('100', plain,
% 0.44/0.67      ((m1_subset_1 @ sk_E_1 @ 
% 0.44/0.67        (k1_zfmisc_1 @ 
% 0.44/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.44/0.67      inference('demod', [status(thm)], ['0', '1'])).
% 0.44/0.67  thf('101', plain,
% 0.44/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.67         (~ (l1_orders_2 @ X6)
% 0.44/0.67          | ((sk_G @ X7 @ X6 @ X8) = (k1_funct_1 @ X7 @ (sk_E @ X7 @ X6 @ X8)))
% 0.44/0.67          | (v5_orders_3 @ X7 @ X8 @ X6)
% 0.44/0.67          | ~ (m1_subset_1 @ X7 @ 
% 0.44/0.67               (k1_zfmisc_1 @ 
% 0.44/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.44/0.67          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.44/0.67          | ~ (v1_funct_1 @ X7)
% 0.44/0.67          | ~ (l1_orders_2 @ X8))),
% 0.44/0.67      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.44/0.67  thf('102', plain,
% 0.44/0.67      ((~ (l1_orders_2 @ sk_C)
% 0.44/0.67        | ~ (v1_funct_1 @ sk_E_1)
% 0.44/0.67        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.44/0.67             (u1_struct_0 @ sk_D_1))
% 0.44/0.67        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.44/0.67        | ((sk_G @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.44/0.67            = (k1_funct_1 @ sk_E_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C)))
% 0.44/0.67        | ~ (l1_orders_2 @ sk_D_1))),
% 0.44/0.67      inference('sup-', [status(thm)], ['100', '101'])).
% 0.44/0.67  thf('103', plain, ((l1_orders_2 @ sk_C)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('104', plain, ((v1_funct_1 @ sk_E_1)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('105', plain,
% 0.44/0.67      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.44/0.67      inference('demod', [status(thm)], ['7', '8'])).
% 0.44/0.67  thf('106', plain, ((l1_orders_2 @ sk_D_1)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('107', plain,
% 0.44/0.67      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.44/0.67        | ((sk_G @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.44/0.67            = (k1_funct_1 @ sk_E_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))))),
% 0.44/0.67      inference('demod', [status(thm)], ['102', '103', '104', '105', '106'])).
% 0.44/0.67  thf('108', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.44/0.67      inference('demod', [status(thm)], ['12', '13'])).
% 0.44/0.67  thf('109', plain,
% 0.44/0.67      (((sk_G @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.44/0.67         = (k1_funct_1 @ sk_E_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.44/0.67      inference('clc', [status(thm)], ['107', '108'])).
% 0.44/0.67  thf('110', plain,
% 0.44/0.67      ((m1_subset_1 @ sk_E_1 @ 
% 0.44/0.67        (k1_zfmisc_1 @ 
% 0.44/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('111', plain,
% 0.44/0.67      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.44/0.67         (~ (l1_orders_2 @ X6)
% 0.44/0.67          | ~ (v5_orders_3 @ X7 @ X8 @ X6)
% 0.44/0.67          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.44/0.67          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X6))
% 0.44/0.67          | (r1_orders_2 @ X6 @ X11 @ X10)
% 0.44/0.67          | ((X10) != (k1_funct_1 @ X7 @ X9))
% 0.44/0.67          | ((X11) != (k1_funct_1 @ X7 @ X12))
% 0.44/0.67          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X6))
% 0.44/0.67          | ~ (r1_orders_2 @ X8 @ X12 @ X9)
% 0.44/0.67          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X8))
% 0.44/0.67          | ~ (m1_subset_1 @ X7 @ 
% 0.44/0.67               (k1_zfmisc_1 @ 
% 0.44/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.44/0.67          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.44/0.67          | ~ (v1_funct_1 @ X7)
% 0.44/0.67          | ~ (l1_orders_2 @ X8))),
% 0.44/0.67      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.44/0.67  thf('112', plain,
% 0.44/0.67      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X12 : $i]:
% 0.44/0.67         (~ (l1_orders_2 @ X8)
% 0.44/0.67          | ~ (v1_funct_1 @ X7)
% 0.44/0.67          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.44/0.67          | ~ (m1_subset_1 @ X7 @ 
% 0.44/0.67               (k1_zfmisc_1 @ 
% 0.44/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.44/0.67          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X8))
% 0.44/0.67          | ~ (r1_orders_2 @ X8 @ X12 @ X9)
% 0.44/0.67          | ~ (m1_subset_1 @ (k1_funct_1 @ X7 @ X12) @ (u1_struct_0 @ X6))
% 0.44/0.67          | (r1_orders_2 @ X6 @ (k1_funct_1 @ X7 @ X12) @ 
% 0.44/0.67             (k1_funct_1 @ X7 @ X9))
% 0.44/0.67          | ~ (m1_subset_1 @ (k1_funct_1 @ X7 @ X9) @ (u1_struct_0 @ X6))
% 0.44/0.67          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.44/0.67          | ~ (v5_orders_3 @ X7 @ X8 @ X6)
% 0.44/0.67          | ~ (l1_orders_2 @ X6))),
% 0.44/0.67      inference('simplify', [status(thm)], ['111'])).
% 0.44/0.67  thf('113', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (~ (l1_orders_2 @ sk_B)
% 0.44/0.67          | ~ (v5_orders_3 @ sk_E_1 @ sk_A @ sk_B)
% 0.44/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X0) @ (u1_struct_0 @ sk_B))
% 0.44/0.67          | (r1_orders_2 @ sk_B @ (k1_funct_1 @ sk_E_1 @ X1) @ 
% 0.44/0.67             (k1_funct_1 @ sk_E_1 @ X0))
% 0.44/0.67          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X1) @ (u1_struct_0 @ sk_B))
% 0.44/0.67          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.44/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.44/0.67          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.44/0.67               (u1_struct_0 @ sk_B))
% 0.44/0.67          | ~ (v1_funct_1 @ sk_E_1)
% 0.44/0.67          | ~ (l1_orders_2 @ sk_A))),
% 0.44/0.67      inference('sup-', [status(thm)], ['110', '112'])).
% 0.44/0.67  thf('114', plain, ((l1_orders_2 @ sk_B)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('115', plain, ((v5_orders_3 @ sk_E_1 @ sk_A @ sk_B)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('116', plain,
% 0.44/0.67      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('117', plain, ((v1_funct_1 @ sk_E_1)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('118', plain, ((l1_orders_2 @ sk_A)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('119', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.44/0.67          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X0) @ (u1_struct_0 @ sk_B))
% 0.44/0.67          | (r1_orders_2 @ sk_B @ (k1_funct_1 @ sk_E_1 @ X1) @ 
% 0.44/0.67             (k1_funct_1 @ sk_E_1 @ X0))
% 0.44/0.67          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X1) @ (u1_struct_0 @ sk_B))
% 0.44/0.67          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.44/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.44/0.67      inference('demod', [status(thm)],
% 0.44/0.67                ['113', '114', '115', '116', '117', '118'])).
% 0.44/0.67  thf('120', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.44/0.67      inference('simplify', [status(thm)], ['69'])).
% 0.44/0.67  thf('121', plain,
% 0.44/0.67      (((g1_orders_2 @ (u1_struct_0 @ sk_B) @ (u1_orders_2 @ sk_B))
% 0.44/0.67         = (g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1)))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('122', plain,
% 0.44/0.67      (![X5 : $i]:
% 0.44/0.67         (((k7_lattice3 @ (k7_lattice3 @ X5))
% 0.44/0.67            = (g1_orders_2 @ (u1_struct_0 @ X5) @ (u1_orders_2 @ X5)))
% 0.44/0.67          | ~ (l1_orders_2 @ X5))),
% 0.44/0.67      inference('cnf', [status(esa)], [t8_lattice3])).
% 0.44/0.67  thf('123', plain,
% 0.44/0.67      ((((k7_lattice3 @ (k7_lattice3 @ sk_B))
% 0.44/0.67          = (g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1)))
% 0.44/0.67        | ~ (l1_orders_2 @ sk_B))),
% 0.44/0.67      inference('sup+', [status(thm)], ['121', '122'])).
% 0.44/0.67  thf('124', plain, ((l1_orders_2 @ sk_B)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('125', plain,
% 0.44/0.67      (((k7_lattice3 @ (k7_lattice3 @ sk_B))
% 0.44/0.67         = (g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1)))),
% 0.44/0.67      inference('demod', [status(thm)], ['123', '124'])).
% 0.44/0.67  thf('126', plain,
% 0.44/0.67      (![X5 : $i]:
% 0.44/0.67         (((k7_lattice3 @ (k7_lattice3 @ X5))
% 0.44/0.67            = (g1_orders_2 @ (u1_struct_0 @ X5) @ (u1_orders_2 @ X5)))
% 0.44/0.67          | ~ (l1_orders_2 @ X5))),
% 0.44/0.67      inference('cnf', [status(esa)], [t8_lattice3])).
% 0.44/0.67  thf('127', plain,
% 0.44/0.67      (((k7_lattice3 @ (k7_lattice3 @ sk_B))
% 0.44/0.67         = (g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1)))),
% 0.44/0.67      inference('demod', [status(thm)], ['123', '124'])).
% 0.44/0.67  thf('128', plain,
% 0.44/0.67      ((((k7_lattice3 @ (k7_lattice3 @ sk_B))
% 0.44/0.67          = (k7_lattice3 @ (k7_lattice3 @ sk_D_1)))
% 0.44/0.67        | ~ (l1_orders_2 @ sk_D_1))),
% 0.44/0.67      inference('sup+', [status(thm)], ['126', '127'])).
% 0.44/0.67  thf('129', plain, ((l1_orders_2 @ sk_D_1)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('130', plain,
% 0.44/0.67      (((k7_lattice3 @ (k7_lattice3 @ sk_B))
% 0.44/0.67         = (k7_lattice3 @ (k7_lattice3 @ sk_D_1)))),
% 0.44/0.67      inference('demod', [status(thm)], ['128', '129'])).
% 0.44/0.67  thf('131', plain,
% 0.44/0.67      (((k7_lattice3 @ (k7_lattice3 @ sk_D_1))
% 0.44/0.67         = (g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1)))),
% 0.44/0.67      inference('demod', [status(thm)], ['125', '130'])).
% 0.44/0.67  thf('132', plain,
% 0.44/0.67      (((g1_orders_2 @ (u1_struct_0 @ sk_B) @ (u1_orders_2 @ sk_B))
% 0.44/0.67         = (g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1)))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('133', plain,
% 0.44/0.67      (((k7_lattice3 @ (k7_lattice3 @ sk_B))
% 0.44/0.67         = (g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1)))),
% 0.44/0.67      inference('demod', [status(thm)], ['123', '124'])).
% 0.44/0.67  thf('134', plain,
% 0.44/0.67      (((g1_orders_2 @ (u1_struct_0 @ sk_B) @ (u1_orders_2 @ sk_B))
% 0.44/0.67         = (k7_lattice3 @ (k7_lattice3 @ sk_B)))),
% 0.44/0.67      inference('demod', [status(thm)], ['132', '133'])).
% 0.44/0.67  thf('135', plain,
% 0.44/0.67      (((k7_lattice3 @ (k7_lattice3 @ sk_B))
% 0.44/0.67         = (k7_lattice3 @ (k7_lattice3 @ sk_D_1)))),
% 0.44/0.67      inference('demod', [status(thm)], ['128', '129'])).
% 0.44/0.67  thf('136', plain,
% 0.44/0.67      (((g1_orders_2 @ (u1_struct_0 @ sk_B) @ (u1_orders_2 @ sk_B))
% 0.44/0.67         = (k7_lattice3 @ (k7_lattice3 @ sk_D_1)))),
% 0.44/0.67      inference('demod', [status(thm)], ['134', '135'])).
% 0.44/0.67  thf('137', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.67         (~ (l1_orders_2 @ X0)
% 0.44/0.67          | ((u1_struct_0 @ X0) = (X1))
% 0.44/0.67          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.44/0.67              != (g1_orders_2 @ X1 @ X2)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['63', '64'])).
% 0.44/0.67  thf('138', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (((k7_lattice3 @ (k7_lattice3 @ sk_D_1)) != (g1_orders_2 @ X1 @ X0))
% 0.44/0.67          | ((u1_struct_0 @ sk_B) = (X1))
% 0.44/0.67          | ~ (l1_orders_2 @ sk_B))),
% 0.44/0.67      inference('sup-', [status(thm)], ['136', '137'])).
% 0.44/0.67  thf('139', plain, ((l1_orders_2 @ sk_B)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('140', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (((k7_lattice3 @ (k7_lattice3 @ sk_D_1)) != (g1_orders_2 @ X1 @ X0))
% 0.44/0.67          | ((u1_struct_0 @ sk_B) = (X1)))),
% 0.44/0.67      inference('demod', [status(thm)], ['138', '139'])).
% 0.44/0.67  thf('141', plain,
% 0.44/0.67      ((((k7_lattice3 @ (k7_lattice3 @ sk_D_1))
% 0.44/0.67          != (k7_lattice3 @ (k7_lattice3 @ sk_D_1)))
% 0.44/0.67        | ((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_D_1)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['131', '140'])).
% 0.44/0.67  thf('142', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_D_1))),
% 0.44/0.67      inference('simplify', [status(thm)], ['141'])).
% 0.44/0.67  thf('143', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_D_1))),
% 0.44/0.67      inference('simplify', [status(thm)], ['141'])).
% 0.44/0.67  thf('144', plain, (((u1_struct_0 @ sk_C) = (u1_struct_0 @ sk_A))),
% 0.44/0.67      inference('simplify', [status(thm)], ['69'])).
% 0.44/0.67  thf('145', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.44/0.67          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X0) @ 
% 0.44/0.67               (u1_struct_0 @ sk_D_1))
% 0.44/0.67          | (r1_orders_2 @ sk_B @ (k1_funct_1 @ sk_E_1 @ X1) @ 
% 0.44/0.67             (k1_funct_1 @ sk_E_1 @ X0))
% 0.44/0.67          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X1) @ 
% 0.44/0.67               (u1_struct_0 @ sk_D_1))
% 0.44/0.67          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.44/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C)))),
% 0.44/0.67      inference('demod', [status(thm)], ['119', '120', '142', '143', '144'])).
% 0.44/0.67  thf('146', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (~ (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.67             (u1_struct_0 @ sk_D_1))
% 0.44/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.44/0.67          | ~ (r1_orders_2 @ sk_A @ X0 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.44/0.67          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X0) @ 
% 0.44/0.67               (u1_struct_0 @ sk_D_1))
% 0.44/0.67          | (r1_orders_2 @ sk_B @ (k1_funct_1 @ sk_E_1 @ X0) @ 
% 0.44/0.67             (k1_funct_1 @ sk_E_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C)))
% 0.44/0.67          | ~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.67               (u1_struct_0 @ sk_C)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['109', '145'])).
% 0.44/0.67  thf('147', plain,
% 0.44/0.67      ((m1_subset_1 @ sk_E_1 @ 
% 0.44/0.67        (k1_zfmisc_1 @ 
% 0.44/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.44/0.67      inference('demod', [status(thm)], ['0', '1'])).
% 0.44/0.67  thf('148', plain,
% 0.44/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.67         (~ (l1_orders_2 @ X6)
% 0.44/0.67          | (m1_subset_1 @ (sk_G @ X7 @ X6 @ X8) @ (u1_struct_0 @ X6))
% 0.44/0.67          | (v5_orders_3 @ X7 @ X8 @ X6)
% 0.44/0.67          | ~ (m1_subset_1 @ X7 @ 
% 0.44/0.67               (k1_zfmisc_1 @ 
% 0.44/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.44/0.67          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.44/0.67          | ~ (v1_funct_1 @ X7)
% 0.44/0.67          | ~ (l1_orders_2 @ X8))),
% 0.44/0.67      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.44/0.67  thf('149', plain,
% 0.44/0.67      ((~ (l1_orders_2 @ sk_C)
% 0.44/0.67        | ~ (v1_funct_1 @ sk_E_1)
% 0.44/0.67        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.44/0.67             (u1_struct_0 @ sk_D_1))
% 0.44/0.67        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.44/0.67        | (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.67           (u1_struct_0 @ sk_D_1))
% 0.44/0.67        | ~ (l1_orders_2 @ sk_D_1))),
% 0.44/0.67      inference('sup-', [status(thm)], ['147', '148'])).
% 0.44/0.67  thf('150', plain, ((l1_orders_2 @ sk_C)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('151', plain, ((v1_funct_1 @ sk_E_1)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('152', plain,
% 0.44/0.67      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.44/0.67      inference('demod', [status(thm)], ['7', '8'])).
% 0.44/0.67  thf('153', plain, ((l1_orders_2 @ sk_D_1)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('154', plain,
% 0.44/0.67      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.44/0.67        | (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.67           (u1_struct_0 @ sk_D_1)))),
% 0.44/0.67      inference('demod', [status(thm)], ['149', '150', '151', '152', '153'])).
% 0.44/0.67  thf('155', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.44/0.67      inference('demod', [status(thm)], ['12', '13'])).
% 0.44/0.67  thf('156', plain,
% 0.44/0.67      ((m1_subset_1 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.44/0.67      inference('clc', [status(thm)], ['154', '155'])).
% 0.44/0.67  thf('157', plain,
% 0.44/0.67      (((sk_G @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.44/0.67         = (k1_funct_1 @ sk_E_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.44/0.67      inference('clc', [status(thm)], ['107', '108'])).
% 0.44/0.67  thf('158', plain,
% 0.44/0.67      ((m1_subset_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))),
% 0.44/0.67      inference('clc', [status(thm)], ['33', '34'])).
% 0.44/0.67  thf('159', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.44/0.67          | ~ (r1_orders_2 @ sk_A @ X0 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.44/0.67          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X0) @ 
% 0.44/0.67               (u1_struct_0 @ sk_D_1))
% 0.44/0.67          | (r1_orders_2 @ sk_B @ (k1_funct_1 @ sk_E_1 @ X0) @ 
% 0.44/0.67             (sk_G @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.44/0.67      inference('demod', [status(thm)], ['146', '156', '157', '158'])).
% 0.44/0.67  thf('160', plain,
% 0.44/0.67      (((r1_orders_2 @ sk_B @ 
% 0.44/0.67         (k1_funct_1 @ sk_E_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C)) @ 
% 0.44/0.67         (sk_G @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.44/0.67        | ~ (m1_subset_1 @ 
% 0.44/0.67             (k1_funct_1 @ sk_E_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C)) @ 
% 0.44/0.67             (u1_struct_0 @ sk_D_1))
% 0.44/0.67        | ~ (m1_subset_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.67             (u1_struct_0 @ sk_C)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['99', '159'])).
% 0.44/0.67  thf('161', plain,
% 0.44/0.67      ((m1_subset_1 @ sk_E_1 @ 
% 0.44/0.67        (k1_zfmisc_1 @ 
% 0.44/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.44/0.67      inference('demod', [status(thm)], ['0', '1'])).
% 0.44/0.67  thf('162', plain,
% 0.44/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.67         (~ (l1_orders_2 @ X6)
% 0.44/0.67          | ((sk_F @ X7 @ X6 @ X8) = (k1_funct_1 @ X7 @ (sk_D @ X7 @ X6 @ X8)))
% 0.44/0.67          | (v5_orders_3 @ X7 @ X8 @ X6)
% 0.44/0.67          | ~ (m1_subset_1 @ X7 @ 
% 0.44/0.67               (k1_zfmisc_1 @ 
% 0.44/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.44/0.67          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.44/0.67          | ~ (v1_funct_1 @ X7)
% 0.44/0.67          | ~ (l1_orders_2 @ X8))),
% 0.44/0.67      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.44/0.67  thf('163', plain,
% 0.44/0.67      ((~ (l1_orders_2 @ sk_C)
% 0.44/0.67        | ~ (v1_funct_1 @ sk_E_1)
% 0.44/0.67        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.44/0.67             (u1_struct_0 @ sk_D_1))
% 0.44/0.67        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.44/0.67        | ((sk_F @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.44/0.67            = (k1_funct_1 @ sk_E_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C)))
% 0.44/0.67        | ~ (l1_orders_2 @ sk_D_1))),
% 0.44/0.67      inference('sup-', [status(thm)], ['161', '162'])).
% 0.44/0.67  thf('164', plain, ((l1_orders_2 @ sk_C)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('165', plain, ((v1_funct_1 @ sk_E_1)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('166', plain,
% 0.44/0.67      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.44/0.67      inference('demod', [status(thm)], ['7', '8'])).
% 0.44/0.67  thf('167', plain, ((l1_orders_2 @ sk_D_1)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('168', plain,
% 0.44/0.67      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.44/0.67        | ((sk_F @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.44/0.67            = (k1_funct_1 @ sk_E_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C))))),
% 0.44/0.67      inference('demod', [status(thm)], ['163', '164', '165', '166', '167'])).
% 0.44/0.67  thf('169', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.44/0.67      inference('demod', [status(thm)], ['12', '13'])).
% 0.44/0.67  thf('170', plain,
% 0.44/0.67      (((sk_F @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.44/0.67         = (k1_funct_1 @ sk_E_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.44/0.67      inference('clc', [status(thm)], ['168', '169'])).
% 0.44/0.67  thf('171', plain,
% 0.44/0.67      (((sk_F @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.44/0.67         = (k1_funct_1 @ sk_E_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.44/0.67      inference('clc', [status(thm)], ['168', '169'])).
% 0.44/0.67  thf('172', plain,
% 0.44/0.67      ((m1_subset_1 @ sk_E_1 @ 
% 0.44/0.67        (k1_zfmisc_1 @ 
% 0.44/0.67         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.44/0.67      inference('demod', [status(thm)], ['0', '1'])).
% 0.44/0.67  thf('173', plain,
% 0.44/0.67      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.44/0.67         (~ (l1_orders_2 @ X6)
% 0.44/0.67          | (m1_subset_1 @ (sk_F @ X7 @ X6 @ X8) @ (u1_struct_0 @ X6))
% 0.44/0.67          | (v5_orders_3 @ X7 @ X8 @ X6)
% 0.44/0.67          | ~ (m1_subset_1 @ X7 @ 
% 0.44/0.67               (k1_zfmisc_1 @ 
% 0.44/0.67                (k2_zfmisc_1 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))))
% 0.44/0.67          | ~ (v1_funct_2 @ X7 @ (u1_struct_0 @ X8) @ (u1_struct_0 @ X6))
% 0.44/0.67          | ~ (v1_funct_1 @ X7)
% 0.44/0.67          | ~ (l1_orders_2 @ X8))),
% 0.44/0.67      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.44/0.67  thf('174', plain,
% 0.44/0.67      ((~ (l1_orders_2 @ sk_C)
% 0.44/0.67        | ~ (v1_funct_1 @ sk_E_1)
% 0.44/0.67        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.44/0.67             (u1_struct_0 @ sk_D_1))
% 0.44/0.67        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.44/0.67        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.67           (u1_struct_0 @ sk_D_1))
% 0.44/0.67        | ~ (l1_orders_2 @ sk_D_1))),
% 0.44/0.67      inference('sup-', [status(thm)], ['172', '173'])).
% 0.44/0.67  thf('175', plain, ((l1_orders_2 @ sk_C)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('176', plain, ((v1_funct_1 @ sk_E_1)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('177', plain,
% 0.44/0.67      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.44/0.67      inference('demod', [status(thm)], ['7', '8'])).
% 0.44/0.67  thf('178', plain, ((l1_orders_2 @ sk_D_1)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('179', plain,
% 0.44/0.67      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.44/0.67        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.67           (u1_struct_0 @ sk_D_1)))),
% 0.44/0.67      inference('demod', [status(thm)], ['174', '175', '176', '177', '178'])).
% 0.44/0.67  thf('180', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.44/0.67      inference('demod', [status(thm)], ['12', '13'])).
% 0.44/0.67  thf('181', plain,
% 0.44/0.67      ((m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.44/0.67      inference('clc', [status(thm)], ['179', '180'])).
% 0.44/0.67  thf('182', plain,
% 0.44/0.67      ((m1_subset_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))),
% 0.44/0.67      inference('clc', [status(thm)], ['96', '97'])).
% 0.44/0.67  thf('183', plain,
% 0.44/0.67      ((r1_orders_2 @ sk_B @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.67        (sk_G @ sk_E_1 @ sk_D_1 @ sk_C))),
% 0.44/0.67      inference('demod', [status(thm)], ['160', '170', '171', '181', '182'])).
% 0.44/0.67  thf('184', plain,
% 0.44/0.67      ((m1_subset_1 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.44/0.67      inference('clc', [status(thm)], ['154', '155'])).
% 0.44/0.67  thf('185', plain,
% 0.44/0.67      (((k7_lattice3 @ (k7_lattice3 @ sk_B))
% 0.44/0.67         = (k7_lattice3 @ (k7_lattice3 @ sk_D_1)))),
% 0.44/0.67      inference('demod', [status(thm)], ['128', '129'])).
% 0.44/0.67  thf('186', plain,
% 0.44/0.67      (((k7_lattice3 @ (k7_lattice3 @ sk_D_1))
% 0.44/0.67         = (g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1)))),
% 0.44/0.67      inference('demod', [status(thm)], ['125', '130'])).
% 0.44/0.67  thf('187', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.67         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X0))
% 0.44/0.67          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X1))
% 0.44/0.67          | ~ (r1_orders_2 @ X0 @ X3 @ X2)
% 0.44/0.67          | (r1_orders_2 @ X1 @ X3 @ X2)
% 0.44/0.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.44/0.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.44/0.67          | ~ (l1_orders_2 @ X1)
% 0.44/0.67          | ~ (l1_orders_2 @ X0)
% 0.44/0.67          | ((k7_lattice3 @ (k7_lattice3 @ X0))
% 0.44/0.67              != (g1_orders_2 @ (u1_struct_0 @ X1) @ (u1_orders_2 @ X1))))),
% 0.44/0.67      inference('simplify', [status(thm)], ['74'])).
% 0.44/0.67  thf('188', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.67         (((k7_lattice3 @ (k7_lattice3 @ X0))
% 0.44/0.67            != (k7_lattice3 @ (k7_lattice3 @ sk_D_1)))
% 0.44/0.67          | ~ (l1_orders_2 @ X0)
% 0.44/0.67          | ~ (l1_orders_2 @ sk_D_1)
% 0.44/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.44/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.44/0.67          | (r1_orders_2 @ sk_D_1 @ X2 @ X1)
% 0.44/0.67          | ~ (r1_orders_2 @ X0 @ X2 @ X1)
% 0.44/0.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.44/0.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['186', '187'])).
% 0.44/0.67  thf('189', plain, ((l1_orders_2 @ sk_D_1)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('190', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.67         (((k7_lattice3 @ (k7_lattice3 @ X0))
% 0.44/0.67            != (k7_lattice3 @ (k7_lattice3 @ sk_D_1)))
% 0.44/0.67          | ~ (l1_orders_2 @ X0)
% 0.44/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.44/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.44/0.67          | (r1_orders_2 @ sk_D_1 @ X2 @ X1)
% 0.44/0.67          | ~ (r1_orders_2 @ X0 @ X2 @ X1)
% 0.44/0.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ sk_D_1))
% 0.44/0.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.44/0.67      inference('demod', [status(thm)], ['188', '189'])).
% 0.44/0.67  thf('191', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (((k7_lattice3 @ (k7_lattice3 @ sk_D_1))
% 0.44/0.67            != (k7_lattice3 @ (k7_lattice3 @ sk_D_1)))
% 0.44/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.44/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.44/0.67          | ~ (r1_orders_2 @ sk_B @ X0 @ X1)
% 0.44/0.67          | (r1_orders_2 @ sk_D_1 @ X0 @ X1)
% 0.44/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.44/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.44/0.67          | ~ (l1_orders_2 @ sk_B))),
% 0.44/0.67      inference('sup-', [status(thm)], ['185', '190'])).
% 0.44/0.67  thf('192', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_D_1))),
% 0.44/0.67      inference('simplify', [status(thm)], ['141'])).
% 0.44/0.67  thf('193', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_D_1))),
% 0.44/0.67      inference('simplify', [status(thm)], ['141'])).
% 0.44/0.67  thf('194', plain, ((l1_orders_2 @ sk_B)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('195', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (((k7_lattice3 @ (k7_lattice3 @ sk_D_1))
% 0.44/0.67            != (k7_lattice3 @ (k7_lattice3 @ sk_D_1)))
% 0.44/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.44/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.44/0.67          | ~ (r1_orders_2 @ sk_B @ X0 @ X1)
% 0.44/0.67          | (r1_orders_2 @ sk_D_1 @ X0 @ X1)
% 0.44/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.44/0.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1)))),
% 0.44/0.67      inference('demod', [status(thm)], ['191', '192', '193', '194'])).
% 0.44/0.67  thf('196', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.44/0.67          | (r1_orders_2 @ sk_D_1 @ X0 @ X1)
% 0.44/0.67          | ~ (r1_orders_2 @ sk_B @ X0 @ X1)
% 0.44/0.67          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.44/0.67      inference('simplify', [status(thm)], ['195'])).
% 0.44/0.67  thf('197', plain,
% 0.44/0.67      (![X0 : $i]:
% 0.44/0.67         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.44/0.67          | ~ (r1_orders_2 @ sk_B @ X0 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.44/0.67          | (r1_orders_2 @ sk_D_1 @ X0 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['184', '196'])).
% 0.44/0.67  thf('198', plain,
% 0.44/0.67      (((r1_orders_2 @ sk_D_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.67         (sk_G @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.44/0.67        | ~ (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.67             (u1_struct_0 @ sk_D_1)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['183', '197'])).
% 0.44/0.67  thf('199', plain,
% 0.44/0.67      ((m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.44/0.67      inference('clc', [status(thm)], ['179', '180'])).
% 0.44/0.67  thf('200', plain,
% 0.44/0.67      ((r1_orders_2 @ sk_D_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.44/0.67        (sk_G @ sk_E_1 @ sk_D_1 @ sk_C))),
% 0.44/0.67      inference('demod', [status(thm)], ['198', '199'])).
% 0.44/0.67  thf('201', plain, ($false), inference('demod', [status(thm)], ['15', '200'])).
% 0.44/0.67  
% 0.44/0.67  % SZS output end Refutation
% 0.44/0.67  
% 0.44/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
