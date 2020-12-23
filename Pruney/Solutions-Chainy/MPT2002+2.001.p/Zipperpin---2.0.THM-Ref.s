%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.afV5mNc5tY

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 980 expanded)
%              Number of leaves         :   30 ( 292 expanded)
%              Depth                    :   19
%              Number of atoms          : 2286 (38469 expanded)
%              Number of equality atoms :   73 (1604 expanded)
%              Maximal formula depth    :   25 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(sk_F_1_type,type,(
    sk_F_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_orders_3_type,type,(
    v5_orders_3: $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ~ ( r1_orders_2 @ X8 @ ( sk_F @ X9 @ X8 @ X10 ) @ ( sk_G @ X9 @ X8 @ X10 ) )
      | ( v5_orders_3 @ X9 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( r1_orders_2 @ X10 @ ( sk_D @ X9 @ X8 @ X10 ) @ ( sk_E @ X9 @ X8 @ X10 ) )
      | ( v5_orders_3 @ X9 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( sk_D @ X9 @ X8 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ( v5_orders_3 @ X9 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('28',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
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
    | ( m1_subset_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,(
    ~ ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('35',plain,(
    m1_subset_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['33','34'])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( u1_orders_2 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ X0 ) @ ( u1_orders_2 @ sk_C ) )
      | ~ ( r1_orders_2 @ sk_C @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ X0 ) @ ( u1_orders_2 @ sk_C ) )
      | ~ ( r1_orders_2 @ sk_C @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ X0 ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ) @ ( u1_orders_2 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('42',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( sk_E @ X9 @ X8 @ X10 ) @ ( u1_struct_0 @ X10 ) )
      | ( v5_orders_3 @ X9 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('43',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
    | ~ ( l1_orders_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('47',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf('49',plain,(
    ~ ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('50',plain,(
    m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ) @ ( u1_orders_2 @ sk_C ) ),
    inference(demod,[status(thm)],['40','50'])).

thf('52',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('53',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_orders_2 @ X3 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( g1_orders_2 @ X6 @ X7 )
       != ( g1_orders_2 @ X4 @ X5 ) )
      | ( X7 = X5 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X6 ) ) ) ) ),
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
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_A )
        = X0 )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_A )
        = X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( u1_orders_2 @ sk_A )
    = ( u1_orders_2 @ sk_C ) ),
    inference(eq_res,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( u1_orders_2 @ X1 ) )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_C ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( u1_orders_2 @ sk_A )
    = ( u1_orders_2 @ sk_C ) ),
    inference(eq_res,[status(thm)],['58'])).

thf('65',plain,(
    ! [X3: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X3 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X3 ) @ ( u1_struct_0 @ X3 ) ) ) )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('66',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( ( g1_orders_2 @ X6 @ X7 )
       != ( g1_orders_2 @ X4 @ X5 ) )
      | ( X6 = X4 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_C ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_A )
        = X1 )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_C ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_A )
        = X1 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( u1_orders_2 @ sk_A )
    = ( u1_orders_2 @ sk_C ) ),
    inference(eq_res,[status(thm)],['58'])).

thf('73',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_C ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_C ) @ ( u1_orders_2 @ sk_C ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_A )
        = X1 ) ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['74'])).

thf('76',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['74'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_C ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['63','75','76'])).

thf('78',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','77'])).

thf('79',plain,(
    m1_subset_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('80',plain,(
    m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('81',plain,(
    r1_orders_2 @ sk_A @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('83',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( ( sk_G @ X9 @ X8 @ X10 )
        = ( k1_funct_1 @ X9 @ ( sk_E @ X9 @ X8 @ X10 ) ) )
      | ( v5_orders_3 @ X9 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('84',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C )
      = ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ) )
    | ~ ( l1_orders_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('88',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C )
      = ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['84','85','86','87','88'])).

thf('90',plain,(
    ~ ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('91',plain,
    ( ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C )
    = ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_3 @ X9 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X8 ) )
      | ( r1_orders_2 @ X8 @ X13 @ X12 )
      | ( X12
       != ( k1_funct_1 @ X9 @ X11 ) )
      | ( X13
       != ( k1_funct_1 @ X9 @ X14 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_orders_2 @ X10 @ X14 @ X11 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('94',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r1_orders_2 @ X10 @ X14 @ X11 )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ X9 @ X14 ) @ ( u1_struct_0 @ X8 ) )
      | ( r1_orders_2 @ X8 @ ( k1_funct_1 @ X9 @ X14 ) @ ( k1_funct_1 @ X9 @ X11 ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ X9 @ X11 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( v5_orders_3 @ X9 @ X10 @ X8 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
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
    inference('sup-',[status(thm)],['92','94'])).

thf('96',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v5_orders_3 @ sk_E_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ X0 ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_orders_2 @ sk_B @ ( k1_funct_1 @ sk_E_1 @ X1 ) @ ( k1_funct_1 @ sk_E_1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ X1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99','100'])).

thf('102',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['74'])).

thf('103',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B )
        = X1 )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B )
        = X1 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_D_1 ) ),
    inference(eq_res,[status(thm)],['107'])).

thf('109',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_D_1 ) ),
    inference(eq_res,[status(thm)],['107'])).

thf('110',plain,
    ( ( u1_struct_0 @ sk_A )
    = ( u1_struct_0 @ sk_C ) ),
    inference(eq_res,[status(thm)],['74'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_orders_2 @ sk_B @ ( k1_funct_1 @ sk_E_1 @ X1 ) @ ( k1_funct_1 @ sk_E_1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ X1 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( r1_orders_2 @ sk_A @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['101','102','108','109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_orders_2 @ sk_B @ ( k1_funct_1 @ sk_E_1 @ X0 ) @ ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ) )
      | ~ ( m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['91','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('114',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( sk_G @ X9 @ X8 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ( v5_orders_3 @ X9 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('115',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( l1_orders_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('119',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['115','116','117','118','119'])).

thf('121',plain,(
    ~ ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('122',plain,(
    m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,
    ( ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C )
    = ( k1_funct_1 @ sk_E_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('124',plain,(
    m1_subset_1 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_C ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_E @ sk_E_1 @ sk_D_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ X0 ) @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r1_orders_2 @ sk_B @ ( k1_funct_1 @ sk_E_1 @ X0 ) @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['112','122','123','124'])).

thf('126',plain,
    ( ( r1_orders_2 @ sk_B @ ( k1_funct_1 @ sk_E_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) ) @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( k1_funct_1 @ sk_E_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['81','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('128',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( ( sk_F @ X9 @ X8 @ X10 )
        = ( k1_funct_1 @ X9 @ ( sk_D @ X9 @ X8 @ X10 ) ) )
      | ( v5_orders_3 @ X9 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('129',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C )
      = ( k1_funct_1 @ sk_E_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) ) )
    | ~ ( l1_orders_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('133',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C )
      = ( k1_funct_1 @ sk_E_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['129','130','131','132','133'])).

thf('135',plain,(
    ~ ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('136',plain,
    ( ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C )
    = ( k1_funct_1 @ sk_E_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C )
    = ( k1_funct_1 @ sk_E_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('138',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('139',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ( m1_subset_1 @ ( sk_F @ X9 @ X8 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ( v5_orders_3 @ X9 @ X10 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) ) ) )
      | ~ ( v1_funct_2 @ X9 @ ( u1_struct_0 @ X10 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_orders_3])).

thf('140',plain,
    ( ~ ( l1_orders_2 @ sk_C )
    | ~ ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ~ ( l1_orders_2 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    l1_orders_2 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_2 @ sk_E_1 @ ( u1_struct_0 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('144',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,
    ( ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 )
    | ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['140','141','142','143','144'])).

thf('146',plain,(
    ~ ( v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('147',plain,(
    m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,(
    m1_subset_1 @ ( sk_D @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_C ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('149',plain,(
    r1_orders_2 @ sk_B @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['126','136','137','147','148'])).

thf('150',plain,(
    m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('151',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_D_1 ) ),
    inference(eq_res,[status(thm)],['107'])).

thf('152',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( u1_orders_2 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('153',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( l1_orders_2 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( u1_orders_2 @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_B @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_D_1 ) ),
    inference(eq_res,[status(thm)],['107'])).

thf('156',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_B )
        = X0 )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['156','157'])).

thf('159',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_D_1 ) @ ( u1_orders_2 @ sk_D_1 ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_B )
        = X0 ) ) ),
    inference(demod,[status(thm)],['158','159'])).

thf('161',plain,
    ( ( u1_orders_2 @ sk_B )
    = ( u1_orders_2 @ sk_D_1 ) ),
    inference(eq_res,[status(thm)],['160'])).

thf('162',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_D_1 ) )
      | ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ ( u1_orders_2 @ sk_D_1 ) )
      | ~ ( r1_orders_2 @ sk_B @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['153','154','155','161'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( r1_orders_2 @ sk_B @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ X0 ) @ ( u1_orders_2 @ sk_D_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['150','162'])).

thf('164',plain,
    ( ~ ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) ) @ ( u1_orders_2 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['149','163'])).

thf('165',plain,(
    m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('166',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) ) @ ( u1_orders_2 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['164','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( u1_orders_2 @ X1 ) )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('168',plain,
    ( ~ ( l1_orders_2 @ sk_D_1 )
    | ~ ( m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) )
    | ( r1_orders_2 @ sk_D_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    l1_orders_2 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    m1_subset_1 @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('171',plain,(
    m1_subset_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( u1_struct_0 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('172',plain,(
    r1_orders_2 @ sk_D_1 @ ( sk_F @ sk_E_1 @ sk_D_1 @ sk_C ) @ ( sk_G @ sk_E_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['168','169','170','171'])).

thf('173',plain,(
    $false ),
    inference(demod,[status(thm)],['15','172'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.afV5mNc5tY
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 215 iterations in 0.096s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.55  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.20/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.55  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.20/0.55  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.55  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.55  thf(sk_G_type, type, sk_G: $i > $i > $i > $i).
% 0.20/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.55  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.20/0.55  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.20/0.55  thf(sk_F_1_type, type, sk_F_1: $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(v5_orders_3_type, type, v5_orders_3: $i > $i > $i > $o).
% 0.20/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.55  thf(t1_waybel_9, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_orders_2 @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( l1_orders_2 @ B ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( ( ~( v2_struct_0 @ C ) ) & ( l1_orders_2 @ C ) ) =>
% 0.20/0.55               ( ![D:$i]:
% 0.20/0.55                 ( ( ( ~( v2_struct_0 @ D ) ) & ( l1_orders_2 @ D ) ) =>
% 0.20/0.55                   ( ![E:$i]:
% 0.20/0.55                     ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.55                         ( v1_funct_2 @
% 0.20/0.55                           E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.55                         ( m1_subset_1 @
% 0.20/0.55                           E @ 
% 0.20/0.55                           ( k1_zfmisc_1 @
% 0.20/0.55                             ( k2_zfmisc_1 @
% 0.20/0.55                               ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.55                       ( ![F:$i]:
% 0.20/0.55                         ( ( ( v1_funct_1 @ F ) & 
% 0.20/0.55                             ( v1_funct_2 @
% 0.20/0.55                               F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) & 
% 0.20/0.55                             ( m1_subset_1 @
% 0.20/0.55                               F @ 
% 0.20/0.55                               ( k1_zfmisc_1 @
% 0.20/0.55                                 ( k2_zfmisc_1 @
% 0.20/0.55                                   ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) ) =>
% 0.20/0.55                           ( ( ( ( g1_orders_2 @
% 0.20/0.55                                   ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) =
% 0.20/0.55                                 ( g1_orders_2 @
% 0.20/0.55                                   ( u1_struct_0 @ C ) @ ( u1_orders_2 @ C ) ) ) & 
% 0.20/0.55                               ( ( g1_orders_2 @
% 0.20/0.55                                   ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) =
% 0.20/0.55                                 ( g1_orders_2 @
% 0.20/0.55                                   ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) ) ) & 
% 0.20/0.55                               ( ( E ) = ( F ) ) & ( v5_orders_3 @ E @ A @ B ) ) =>
% 0.20/0.55                             ( v5_orders_3 @ F @ C @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( l1_orders_2 @ A ) =>
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ( l1_orders_2 @ B ) =>
% 0.20/0.55              ( ![C:$i]:
% 0.20/0.55                ( ( ( ~( v2_struct_0 @ C ) ) & ( l1_orders_2 @ C ) ) =>
% 0.20/0.55                  ( ![D:$i]:
% 0.20/0.55                    ( ( ( ~( v2_struct_0 @ D ) ) & ( l1_orders_2 @ D ) ) =>
% 0.20/0.55                      ( ![E:$i]:
% 0.20/0.55                        ( ( ( v1_funct_1 @ E ) & 
% 0.20/0.55                            ( v1_funct_2 @
% 0.20/0.55                              E @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.55                            ( m1_subset_1 @
% 0.20/0.55                              E @ 
% 0.20/0.55                              ( k1_zfmisc_1 @
% 0.20/0.55                                ( k2_zfmisc_1 @
% 0.20/0.55                                  ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.55                          ( ![F:$i]:
% 0.20/0.55                            ( ( ( v1_funct_1 @ F ) & 
% 0.20/0.55                                ( v1_funct_2 @
% 0.20/0.55                                  F @ ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) & 
% 0.20/0.55                                ( m1_subset_1 @
% 0.20/0.55                                  F @ 
% 0.20/0.55                                  ( k1_zfmisc_1 @
% 0.20/0.55                                    ( k2_zfmisc_1 @
% 0.20/0.55                                      ( u1_struct_0 @ C ) @ ( u1_struct_0 @ D ) ) ) ) ) =>
% 0.20/0.55                              ( ( ( ( g1_orders_2 @
% 0.20/0.55                                      ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) =
% 0.20/0.55                                    ( g1_orders_2 @
% 0.20/0.55                                      ( u1_struct_0 @ C ) @ ( u1_orders_2 @ C ) ) ) & 
% 0.20/0.55                                  ( ( g1_orders_2 @
% 0.20/0.55                                      ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) =
% 0.20/0.55                                    ( g1_orders_2 @
% 0.20/0.55                                      ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) ) ) & 
% 0.20/0.55                                  ( ( E ) = ( F ) ) & 
% 0.20/0.55                                  ( v5_orders_3 @ E @ A @ B ) ) =>
% 0.20/0.55                                ( v5_orders_3 @ F @ C @ D ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t1_waybel_9])).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_F_1 @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain, (((sk_E_1) = (sk_F_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_E_1 @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.20/0.55      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf(d5_orders_3, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_orders_2 @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( l1_orders_2 @ B ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.55                 ( v1_funct_2 @ C @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) & 
% 0.20/0.55                 ( m1_subset_1 @
% 0.20/0.55                   C @ 
% 0.20/0.55                   ( k1_zfmisc_1 @
% 0.20/0.55                     ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ B ) ) ) ) ) =>
% 0.20/0.55               ( ( v5_orders_3 @ C @ A @ B ) <=>
% 0.20/0.55                 ( ![D:$i]:
% 0.20/0.55                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.55                     ( ![E:$i]:
% 0.20/0.55                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.55                         ( ( r1_orders_2 @ A @ D @ E ) =>
% 0.20/0.55                           ( ![F:$i]:
% 0.20/0.55                             ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.55                               ( ![G:$i]:
% 0.20/0.55                                 ( ( m1_subset_1 @ G @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.55                                   ( ( ( ( F ) = ( k1_funct_1 @ C @ D ) ) & 
% 0.20/0.55                                       ( ( G ) = ( k1_funct_1 @ C @ E ) ) ) =>
% 0.20/0.55                                     ( r1_orders_2 @ B @ F @ G ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.55         (~ (l1_orders_2 @ X8)
% 0.20/0.55          | ~ (r1_orders_2 @ X8 @ (sk_F @ X9 @ X8 @ X10) @ 
% 0.20/0.55               (sk_G @ X9 @ X8 @ X10))
% 0.20/0.55          | (v5_orders_3 @ X9 @ X10 @ X8)
% 0.20/0.55          | ~ (m1_subset_1 @ X9 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 0.20/0.55          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 0.20/0.55          | ~ (v1_funct_1 @ X9)
% 0.20/0.55          | ~ (l1_orders_2 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      ((~ (l1_orders_2 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_E_1)
% 0.20/0.55        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.55             (u1_struct_0 @ sk_D_1))
% 0.20/0.55        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.20/0.55        | ~ (r1_orders_2 @ sk_D_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55             (sk_G @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.20/0.55        | ~ (l1_orders_2 @ sk_D_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf('5', plain, ((l1_orders_2 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('6', plain, ((v1_funct_1 @ sk_E_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_F_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('8', plain, (((sk_E_1) = (sk_F_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('10', plain, ((l1_orders_2 @ sk_D_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.20/0.55        | ~ (r1_orders_2 @ sk_D_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55             (sk_G @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['4', '5', '6', '9', '10'])).
% 0.20/0.55  thf('12', plain, (~ (v5_orders_3 @ sk_F_1 @ sk_C @ sk_D_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('13', plain, (((sk_E_1) = (sk_F_1))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('14', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (~ (r1_orders_2 @ sk_D_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55          (sk_G @ sk_E_1 @ sk_D_1 @ sk_C))),
% 0.20/0.55      inference('clc', [status(thm)], ['11', '14'])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_E_1 @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.20/0.55      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf('17', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.55         (~ (l1_orders_2 @ X8)
% 0.20/0.55          | (r1_orders_2 @ X10 @ (sk_D @ X9 @ X8 @ X10) @ 
% 0.20/0.55             (sk_E @ X9 @ X8 @ X10))
% 0.20/0.55          | (v5_orders_3 @ X9 @ X10 @ X8)
% 0.20/0.55          | ~ (m1_subset_1 @ X9 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 0.20/0.55          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 0.20/0.55          | ~ (v1_funct_1 @ X9)
% 0.20/0.55          | ~ (l1_orders_2 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      ((~ (l1_orders_2 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_E_1)
% 0.20/0.55        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.55             (u1_struct_0 @ sk_D_1))
% 0.20/0.55        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.20/0.55        | (r1_orders_2 @ sk_C @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55           (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.20/0.55        | ~ (l1_orders_2 @ sk_D_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.55  thf('19', plain, ((l1_orders_2 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('20', plain, ((v1_funct_1 @ sk_E_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('22', plain, ((l1_orders_2 @ sk_D_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.20/0.55        | (r1_orders_2 @ sk_C @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55           (sk_E @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['18', '19', '20', '21', '22'])).
% 0.20/0.55  thf('24', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      ((r1_orders_2 @ sk_C @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55        (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))),
% 0.20/0.55      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_E_1 @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.20/0.55      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.55         (~ (l1_orders_2 @ X8)
% 0.20/0.55          | (m1_subset_1 @ (sk_D @ X9 @ X8 @ X10) @ (u1_struct_0 @ X10))
% 0.20/0.55          | (v5_orders_3 @ X9 @ X10 @ X8)
% 0.20/0.55          | ~ (m1_subset_1 @ X9 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 0.20/0.55          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 0.20/0.55          | ~ (v1_funct_1 @ X9)
% 0.20/0.55          | ~ (l1_orders_2 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      ((~ (l1_orders_2 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_E_1)
% 0.20/0.55        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.55             (u1_struct_0 @ sk_D_1))
% 0.20/0.55        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.20/0.55        | (m1_subset_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.20/0.55        | ~ (l1_orders_2 @ sk_D_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.55  thf('29', plain, ((l1_orders_2 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('30', plain, ((v1_funct_1 @ sk_E_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('32', plain, ((l1_orders_2 @ sk_D_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('33', plain,
% 0.20/0.55      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.20/0.55        | (m1_subset_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 0.20/0.55  thf('34', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))),
% 0.20/0.55      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.55  thf(d9_orders_2, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_orders_2 @ A ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.55               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.20/0.55                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.55          | ~ (r1_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.55          | (r2_hidden @ (k4_tarski @ X0 @ X2) @ (u1_orders_2 @ X1))
% 0.20/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.55          | ~ (l1_orders_2 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (l1_orders_2 @ sk_C)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.55          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ X0) @ 
% 0.20/0.55             (u1_orders_2 @ sk_C))
% 0.20/0.55          | ~ (r1_orders_2 @ sk_C @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ X0))),
% 0.20/0.55      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.55  thf('38', plain, ((l1_orders_2 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.55          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ X0) @ 
% 0.20/0.55             (u1_orders_2 @ sk_C))
% 0.20/0.55          | ~ (r1_orders_2 @ sk_C @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.55  thf('40', plain,
% 0.20/0.55      (((r2_hidden @ 
% 0.20/0.55         (k4_tarski @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55          (sk_E @ sk_E_1 @ sk_D_1 @ sk_C)) @ 
% 0.20/0.55         (u1_orders_2 @ sk_C))
% 0.20/0.55        | ~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55             (u1_struct_0 @ sk_C)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['25', '39'])).
% 0.20/0.55  thf('41', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_E_1 @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.20/0.55      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf('42', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.55         (~ (l1_orders_2 @ X8)
% 0.20/0.55          | (m1_subset_1 @ (sk_E @ X9 @ X8 @ X10) @ (u1_struct_0 @ X10))
% 0.20/0.55          | (v5_orders_3 @ X9 @ X10 @ X8)
% 0.20/0.55          | ~ (m1_subset_1 @ X9 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 0.20/0.55          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 0.20/0.55          | ~ (v1_funct_1 @ X9)
% 0.20/0.55          | ~ (l1_orders_2 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      ((~ (l1_orders_2 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_E_1)
% 0.20/0.55        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.55             (u1_struct_0 @ sk_D_1))
% 0.20/0.55        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.20/0.55        | (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.20/0.55        | ~ (l1_orders_2 @ sk_D_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.55  thf('44', plain, ((l1_orders_2 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('45', plain, ((v1_funct_1 @ sk_E_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('47', plain, ((l1_orders_2 @ sk_D_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('48', plain,
% 0.20/0.55      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.20/0.55        | (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 0.20/0.55  thf('49', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('50', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))),
% 0.20/0.55      inference('clc', [status(thm)], ['48', '49'])).
% 0.20/0.55  thf('51', plain,
% 0.20/0.55      ((r2_hidden @ 
% 0.20/0.55        (k4_tarski @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55         (sk_E @ sk_E_1 @ sk_D_1 @ sk_C)) @ 
% 0.20/0.55        (u1_orders_2 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['40', '50'])).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.20/0.55         = (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(dt_u1_orders_2, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( l1_orders_2 @ A ) =>
% 0.20/0.55       ( m1_subset_1 @
% 0.20/0.55         ( u1_orders_2 @ A ) @ 
% 0.20/0.55         ( k1_zfmisc_1 @
% 0.20/0.55           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      (![X3 : $i]:
% 0.20/0.55         ((m1_subset_1 @ (u1_orders_2 @ X3) @ 
% 0.20/0.55           (k1_zfmisc_1 @ 
% 0.20/0.55            (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X3))))
% 0.20/0.55          | ~ (l1_orders_2 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.20/0.55  thf(free_g1_orders_2, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.55       ( ![C:$i,D:$i]:
% 0.20/0.55         ( ( ( g1_orders_2 @ A @ B ) = ( g1_orders_2 @ C @ D ) ) =>
% 0.20/0.55           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.20/0.55  thf('54', plain,
% 0.20/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.55         (((g1_orders_2 @ X6 @ X7) != (g1_orders_2 @ X4 @ X5))
% 0.20/0.55          | ((X7) = (X5))
% 0.20/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X6))))),
% 0.20/0.55      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.20/0.55  thf('55', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (l1_orders_2 @ X0)
% 0.20/0.55          | ((u1_orders_2 @ X0) = (X1))
% 0.20/0.55          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.20/0.55              != (g1_orders_2 @ X2 @ X1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.55  thf('56', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C))
% 0.20/0.55            != (g1_orders_2 @ X1 @ X0))
% 0.20/0.55          | ((u1_orders_2 @ sk_A) = (X0))
% 0.20/0.55          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['52', '55'])).
% 0.20/0.55  thf('57', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C))
% 0.20/0.55            != (g1_orders_2 @ X1 @ X0))
% 0.20/0.55          | ((u1_orders_2 @ sk_A) = (X0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['56', '57'])).
% 0.20/0.55  thf('59', plain, (((u1_orders_2 @ sk_A) = (u1_orders_2 @ sk_C))),
% 0.20/0.55      inference('eq_res', [status(thm)], ['58'])).
% 0.20/0.55  thf('60', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.55          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (u1_orders_2 @ X1))
% 0.20/0.55          | (r1_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.55          | ~ (l1_orders_2 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.20/0.55  thf('61', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (u1_orders_2 @ sk_C))
% 0.20/0.55          | ~ (l1_orders_2 @ sk_A)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.55          | (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.55  thf('62', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (u1_orders_2 @ sk_C))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.55          | (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['61', '62'])).
% 0.20/0.55  thf('64', plain, (((u1_orders_2 @ sk_A) = (u1_orders_2 @ sk_C))),
% 0.20/0.55      inference('eq_res', [status(thm)], ['58'])).
% 0.20/0.55  thf('65', plain,
% 0.20/0.55      (![X3 : $i]:
% 0.20/0.55         ((m1_subset_1 @ (u1_orders_2 @ X3) @ 
% 0.20/0.55           (k1_zfmisc_1 @ 
% 0.20/0.55            (k2_zfmisc_1 @ (u1_struct_0 @ X3) @ (u1_struct_0 @ X3))))
% 0.20/0.55          | ~ (l1_orders_2 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.20/0.55  thf('66', plain,
% 0.20/0.55      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.55         (((g1_orders_2 @ X6 @ X7) != (g1_orders_2 @ X4 @ X5))
% 0.20/0.55          | ((X6) = (X4))
% 0.20/0.55          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X6))))),
% 0.20/0.55      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.20/0.55  thf('67', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (l1_orders_2 @ X0)
% 0.20/0.55          | ((u1_struct_0 @ X0) = (X1))
% 0.20/0.55          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.20/0.55              != (g1_orders_2 @ X1 @ X2)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.55  thf('68', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_C))
% 0.20/0.55            != (g1_orders_2 @ X1 @ X0))
% 0.20/0.55          | ((u1_struct_0 @ sk_A) = (X1))
% 0.20/0.55          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['64', '67'])).
% 0.20/0.55  thf('69', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('70', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_C))
% 0.20/0.55            != (g1_orders_2 @ X1 @ X0))
% 0.20/0.55          | ((u1_struct_0 @ sk_A) = (X1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['68', '69'])).
% 0.20/0.55  thf('71', plain,
% 0.20/0.55      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.20/0.55         = (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('72', plain, (((u1_orders_2 @ sk_A) = (u1_orders_2 @ sk_C))),
% 0.20/0.55      inference('eq_res', [status(thm)], ['58'])).
% 0.20/0.55  thf('73', plain,
% 0.20/0.55      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_C))
% 0.20/0.55         = (g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['71', '72'])).
% 0.20/0.55  thf('74', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((g1_orders_2 @ (u1_struct_0 @ sk_C) @ (u1_orders_2 @ sk_C))
% 0.20/0.55            != (g1_orders_2 @ X1 @ X0))
% 0.20/0.55          | ((u1_struct_0 @ sk_A) = (X1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['70', '73'])).
% 0.20/0.55  thf('75', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_C))),
% 0.20/0.55      inference('eq_res', [status(thm)], ['74'])).
% 0.20/0.55  thf('76', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_C))),
% 0.20/0.55      inference('eq_res', [status(thm)], ['74'])).
% 0.20/0.55  thf('77', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (u1_orders_2 @ sk_C))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.55          | (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['63', '75', '76'])).
% 0.20/0.55  thf('78', plain,
% 0.20/0.55      ((~ (m1_subset_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))
% 0.20/0.55        | (r1_orders_2 @ sk_A @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55           (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.20/0.55        | ~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55             (u1_struct_0 @ sk_C)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['51', '77'])).
% 0.20/0.55  thf('79', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))),
% 0.20/0.55      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.55  thf('80', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))),
% 0.20/0.55      inference('clc', [status(thm)], ['48', '49'])).
% 0.20/0.55  thf('81', plain,
% 0.20/0.55      ((r1_orders_2 @ sk_A @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55        (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.20/0.55  thf('82', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_E_1 @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.20/0.55      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf('83', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.55         (~ (l1_orders_2 @ X8)
% 0.20/0.55          | ((sk_G @ X9 @ X8 @ X10)
% 0.20/0.55              = (k1_funct_1 @ X9 @ (sk_E @ X9 @ X8 @ X10)))
% 0.20/0.55          | (v5_orders_3 @ X9 @ X10 @ X8)
% 0.20/0.55          | ~ (m1_subset_1 @ X9 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 0.20/0.55          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 0.20/0.55          | ~ (v1_funct_1 @ X9)
% 0.20/0.55          | ~ (l1_orders_2 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.20/0.55  thf('84', plain,
% 0.20/0.55      ((~ (l1_orders_2 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_E_1)
% 0.20/0.55        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.55             (u1_struct_0 @ sk_D_1))
% 0.20/0.55        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.20/0.55        | ((sk_G @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.20/0.55            = (k1_funct_1 @ sk_E_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C)))
% 0.20/0.55        | ~ (l1_orders_2 @ sk_D_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['82', '83'])).
% 0.20/0.55  thf('85', plain, ((l1_orders_2 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('86', plain, ((v1_funct_1 @ sk_E_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('87', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('88', plain, ((l1_orders_2 @ sk_D_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('89', plain,
% 0.20/0.55      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.20/0.55        | ((sk_G @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.20/0.55            = (k1_funct_1 @ sk_E_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))))),
% 0.20/0.55      inference('demod', [status(thm)], ['84', '85', '86', '87', '88'])).
% 0.20/0.55  thf('90', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('91', plain,
% 0.20/0.55      (((sk_G @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.20/0.55         = (k1_funct_1 @ sk_E_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.20/0.55      inference('clc', [status(thm)], ['89', '90'])).
% 0.20/0.55  thf('92', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_E_1 @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('93', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.55         (~ (l1_orders_2 @ X8)
% 0.20/0.55          | ~ (v5_orders_3 @ X9 @ X10 @ X8)
% 0.20/0.55          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.20/0.55          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X8))
% 0.20/0.55          | (r1_orders_2 @ X8 @ X13 @ X12)
% 0.20/0.55          | ((X12) != (k1_funct_1 @ X9 @ X11))
% 0.20/0.55          | ((X13) != (k1_funct_1 @ X9 @ X14))
% 0.20/0.55          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X8))
% 0.20/0.55          | ~ (r1_orders_2 @ X10 @ X14 @ X11)
% 0.20/0.55          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X10))
% 0.20/0.55          | ~ (m1_subset_1 @ X9 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 0.20/0.55          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 0.20/0.55          | ~ (v1_funct_1 @ X9)
% 0.20/0.55          | ~ (l1_orders_2 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.20/0.55  thf('94', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X14 : $i]:
% 0.20/0.55         (~ (l1_orders_2 @ X10)
% 0.20/0.55          | ~ (v1_funct_1 @ X9)
% 0.20/0.55          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 0.20/0.55          | ~ (m1_subset_1 @ X9 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 0.20/0.55          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X10))
% 0.20/0.55          | ~ (r1_orders_2 @ X10 @ X14 @ X11)
% 0.20/0.55          | ~ (m1_subset_1 @ (k1_funct_1 @ X9 @ X14) @ (u1_struct_0 @ X8))
% 0.20/0.55          | (r1_orders_2 @ X8 @ (k1_funct_1 @ X9 @ X14) @ 
% 0.20/0.55             (k1_funct_1 @ X9 @ X11))
% 0.20/0.55          | ~ (m1_subset_1 @ (k1_funct_1 @ X9 @ X11) @ (u1_struct_0 @ X8))
% 0.20/0.55          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.20/0.55          | ~ (v5_orders_3 @ X9 @ X10 @ X8)
% 0.20/0.55          | ~ (l1_orders_2 @ X8))),
% 0.20/0.55      inference('simplify', [status(thm)], ['93'])).
% 0.20/0.55  thf('95', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (l1_orders_2 @ sk_B)
% 0.20/0.55          | ~ (v5_orders_3 @ sk_E_1 @ sk_A @ sk_B)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.55          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X0) @ (u1_struct_0 @ sk_B))
% 0.20/0.55          | (r1_orders_2 @ sk_B @ (k1_funct_1 @ sk_E_1 @ X1) @ 
% 0.20/0.55             (k1_funct_1 @ sk_E_1 @ X0))
% 0.20/0.55          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X1) @ (u1_struct_0 @ sk_B))
% 0.20/0.55          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.20/0.55          | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ 
% 0.20/0.55               (u1_struct_0 @ sk_B))
% 0.20/0.55          | ~ (v1_funct_1 @ sk_E_1)
% 0.20/0.55          | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['92', '94'])).
% 0.20/0.55  thf('96', plain, ((l1_orders_2 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('97', plain, ((v5_orders_3 @ sk_E_1 @ sk_A @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('98', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_B))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('99', plain, ((v1_funct_1 @ sk_E_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('100', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('101', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.55          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X0) @ (u1_struct_0 @ sk_B))
% 0.20/0.55          | (r1_orders_2 @ sk_B @ (k1_funct_1 @ sk_E_1 @ X1) @ 
% 0.20/0.55             (k1_funct_1 @ sk_E_1 @ X0))
% 0.20/0.55          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X1) @ (u1_struct_0 @ sk_B))
% 0.20/0.55          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['95', '96', '97', '98', '99', '100'])).
% 0.20/0.55  thf('102', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_C))),
% 0.20/0.55      inference('eq_res', [status(thm)], ['74'])).
% 0.20/0.55  thf('103', plain,
% 0.20/0.55      (((g1_orders_2 @ (u1_struct_0 @ sk_B) @ (u1_orders_2 @ sk_B))
% 0.20/0.55         = (g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('104', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (l1_orders_2 @ X0)
% 0.20/0.55          | ((u1_struct_0 @ X0) = (X1))
% 0.20/0.55          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.20/0.55              != (g1_orders_2 @ X1 @ X2)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['65', '66'])).
% 0.20/0.55  thf('105', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1))
% 0.20/0.55            != (g1_orders_2 @ X1 @ X0))
% 0.20/0.55          | ((u1_struct_0 @ sk_B) = (X1))
% 0.20/0.55          | ~ (l1_orders_2 @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['103', '104'])).
% 0.20/0.55  thf('106', plain, ((l1_orders_2 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('107', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1))
% 0.20/0.55            != (g1_orders_2 @ X1 @ X0))
% 0.20/0.55          | ((u1_struct_0 @ sk_B) = (X1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['105', '106'])).
% 0.20/0.55  thf('108', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('eq_res', [status(thm)], ['107'])).
% 0.20/0.55  thf('109', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('eq_res', [status(thm)], ['107'])).
% 0.20/0.55  thf('110', plain, (((u1_struct_0 @ sk_A) = (u1_struct_0 @ sk_C))),
% 0.20/0.55      inference('eq_res', [status(thm)], ['74'])).
% 0.20/0.55  thf('111', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.55          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X0) @ 
% 0.20/0.55               (u1_struct_0 @ sk_D_1))
% 0.20/0.55          | (r1_orders_2 @ sk_B @ (k1_funct_1 @ sk_E_1 @ X1) @ 
% 0.20/0.55             (k1_funct_1 @ sk_E_1 @ X0))
% 0.20/0.55          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X1) @ 
% 0.20/0.55               (u1_struct_0 @ sk_D_1))
% 0.20/0.55          | ~ (r1_orders_2 @ sk_A @ X1 @ X0)
% 0.20/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['101', '102', '108', '109', '110'])).
% 0.20/0.55  thf('112', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55             (u1_struct_0 @ sk_D_1))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.55          | ~ (r1_orders_2 @ sk_A @ X0 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.20/0.55          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X0) @ 
% 0.20/0.55               (u1_struct_0 @ sk_D_1))
% 0.20/0.55          | (r1_orders_2 @ sk_B @ (k1_funct_1 @ sk_E_1 @ X0) @ 
% 0.20/0.55             (k1_funct_1 @ sk_E_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C)))
% 0.20/0.55          | ~ (m1_subset_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55               (u1_struct_0 @ sk_C)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['91', '111'])).
% 0.20/0.55  thf('113', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_E_1 @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.20/0.55      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf('114', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.55         (~ (l1_orders_2 @ X8)
% 0.20/0.55          | (m1_subset_1 @ (sk_G @ X9 @ X8 @ X10) @ (u1_struct_0 @ X8))
% 0.20/0.55          | (v5_orders_3 @ X9 @ X10 @ X8)
% 0.20/0.55          | ~ (m1_subset_1 @ X9 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 0.20/0.55          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 0.20/0.55          | ~ (v1_funct_1 @ X9)
% 0.20/0.55          | ~ (l1_orders_2 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.20/0.55  thf('115', plain,
% 0.20/0.55      ((~ (l1_orders_2 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_E_1)
% 0.20/0.55        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.55             (u1_struct_0 @ sk_D_1))
% 0.20/0.55        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.20/0.55        | (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55           (u1_struct_0 @ sk_D_1))
% 0.20/0.55        | ~ (l1_orders_2 @ sk_D_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['113', '114'])).
% 0.20/0.55  thf('116', plain, ((l1_orders_2 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('117', plain, ((v1_funct_1 @ sk_E_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('118', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('119', plain, ((l1_orders_2 @ sk_D_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('120', plain,
% 0.20/0.55      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.20/0.55        | (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55           (u1_struct_0 @ sk_D_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['115', '116', '117', '118', '119'])).
% 0.20/0.55  thf('121', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('122', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('clc', [status(thm)], ['120', '121'])).
% 0.20/0.55  thf('123', plain,
% 0.20/0.55      (((sk_G @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.20/0.55         = (k1_funct_1 @ sk_E_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.20/0.55      inference('clc', [status(thm)], ['89', '90'])).
% 0.20/0.55  thf('124', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))),
% 0.20/0.55      inference('clc', [status(thm)], ['48', '49'])).
% 0.20/0.55  thf('125', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_C))
% 0.20/0.55          | ~ (r1_orders_2 @ sk_A @ X0 @ (sk_E @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.20/0.55          | ~ (m1_subset_1 @ (k1_funct_1 @ sk_E_1 @ X0) @ 
% 0.20/0.55               (u1_struct_0 @ sk_D_1))
% 0.20/0.55          | (r1_orders_2 @ sk_B @ (k1_funct_1 @ sk_E_1 @ X0) @ 
% 0.20/0.55             (sk_G @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['112', '122', '123', '124'])).
% 0.20/0.55  thf('126', plain,
% 0.20/0.55      (((r1_orders_2 @ sk_B @ 
% 0.20/0.55         (k1_funct_1 @ sk_E_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C)) @ 
% 0.20/0.55         (sk_G @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.20/0.55        | ~ (m1_subset_1 @ 
% 0.20/0.55             (k1_funct_1 @ sk_E_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C)) @ 
% 0.20/0.55             (u1_struct_0 @ sk_D_1))
% 0.20/0.55        | ~ (m1_subset_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55             (u1_struct_0 @ sk_C)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['81', '125'])).
% 0.20/0.55  thf('127', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_E_1 @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.20/0.55      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf('128', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.55         (~ (l1_orders_2 @ X8)
% 0.20/0.55          | ((sk_F @ X9 @ X8 @ X10)
% 0.20/0.55              = (k1_funct_1 @ X9 @ (sk_D @ X9 @ X8 @ X10)))
% 0.20/0.55          | (v5_orders_3 @ X9 @ X10 @ X8)
% 0.20/0.55          | ~ (m1_subset_1 @ X9 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 0.20/0.55          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 0.20/0.55          | ~ (v1_funct_1 @ X9)
% 0.20/0.55          | ~ (l1_orders_2 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.20/0.55  thf('129', plain,
% 0.20/0.55      ((~ (l1_orders_2 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_E_1)
% 0.20/0.55        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.55             (u1_struct_0 @ sk_D_1))
% 0.20/0.55        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.20/0.55        | ((sk_F @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.20/0.55            = (k1_funct_1 @ sk_E_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C)))
% 0.20/0.55        | ~ (l1_orders_2 @ sk_D_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['127', '128'])).
% 0.20/0.55  thf('130', plain, ((l1_orders_2 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('131', plain, ((v1_funct_1 @ sk_E_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('132', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('133', plain, ((l1_orders_2 @ sk_D_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('134', plain,
% 0.20/0.55      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.20/0.55        | ((sk_F @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.20/0.55            = (k1_funct_1 @ sk_E_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C))))),
% 0.20/0.55      inference('demod', [status(thm)], ['129', '130', '131', '132', '133'])).
% 0.20/0.55  thf('135', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('136', plain,
% 0.20/0.55      (((sk_F @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.20/0.55         = (k1_funct_1 @ sk_E_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.20/0.55      inference('clc', [status(thm)], ['134', '135'])).
% 0.20/0.55  thf('137', plain,
% 0.20/0.55      (((sk_F @ sk_E_1 @ sk_D_1 @ sk_C)
% 0.20/0.55         = (k1_funct_1 @ sk_E_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C)))),
% 0.20/0.55      inference('clc', [status(thm)], ['134', '135'])).
% 0.20/0.55  thf('138', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_E_1 @ 
% 0.20/0.55        (k1_zfmisc_1 @ 
% 0.20/0.55         (k2_zfmisc_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))))),
% 0.20/0.55      inference('demod', [status(thm)], ['0', '1'])).
% 0.20/0.55  thf('139', plain,
% 0.20/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.55         (~ (l1_orders_2 @ X8)
% 0.20/0.55          | (m1_subset_1 @ (sk_F @ X9 @ X8 @ X10) @ (u1_struct_0 @ X8))
% 0.20/0.55          | (v5_orders_3 @ X9 @ X10 @ X8)
% 0.20/0.55          | ~ (m1_subset_1 @ X9 @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))))
% 0.20/0.55          | ~ (v1_funct_2 @ X9 @ (u1_struct_0 @ X10) @ (u1_struct_0 @ X8))
% 0.20/0.55          | ~ (v1_funct_1 @ X9)
% 0.20/0.55          | ~ (l1_orders_2 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [d5_orders_3])).
% 0.20/0.55  thf('140', plain,
% 0.20/0.55      ((~ (l1_orders_2 @ sk_C)
% 0.20/0.55        | ~ (v1_funct_1 @ sk_E_1)
% 0.20/0.55        | ~ (v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ 
% 0.20/0.55             (u1_struct_0 @ sk_D_1))
% 0.20/0.55        | (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.20/0.55        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55           (u1_struct_0 @ sk_D_1))
% 0.20/0.55        | ~ (l1_orders_2 @ sk_D_1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['138', '139'])).
% 0.20/0.55  thf('141', plain, ((l1_orders_2 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('142', plain, ((v1_funct_1 @ sk_E_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('143', plain,
% 0.20/0.55      ((v1_funct_2 @ sk_E_1 @ (u1_struct_0 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.55  thf('144', plain, ((l1_orders_2 @ sk_D_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('145', plain,
% 0.20/0.55      (((v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)
% 0.20/0.55        | (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55           (u1_struct_0 @ sk_D_1)))),
% 0.20/0.55      inference('demod', [status(thm)], ['140', '141', '142', '143', '144'])).
% 0.20/0.55  thf('146', plain, (~ (v5_orders_3 @ sk_E_1 @ sk_C @ sk_D_1)),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.55  thf('147', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('clc', [status(thm)], ['145', '146'])).
% 0.20/0.55  thf('148', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_D @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_C))),
% 0.20/0.55      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.55  thf('149', plain,
% 0.20/0.55      ((r1_orders_2 @ sk_B @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55        (sk_G @ sk_E_1 @ sk_D_1 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['126', '136', '137', '147', '148'])).
% 0.20/0.55  thf('150', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('clc', [status(thm)], ['145', '146'])).
% 0.20/0.55  thf('151', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('eq_res', [status(thm)], ['107'])).
% 0.20/0.55  thf('152', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.55          | ~ (r1_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.55          | (r2_hidden @ (k4_tarski @ X0 @ X2) @ (u1_orders_2 @ X1))
% 0.20/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.55          | ~ (l1_orders_2 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.20/0.55  thf('153', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.55          | ~ (l1_orders_2 @ sk_B)
% 0.20/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B))
% 0.20/0.55          | (r2_hidden @ (k4_tarski @ X0 @ X1) @ (u1_orders_2 @ sk_B))
% 0.20/0.55          | ~ (r1_orders_2 @ sk_B @ X0 @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['151', '152'])).
% 0.20/0.55  thf('154', plain, ((l1_orders_2 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('155', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('eq_res', [status(thm)], ['107'])).
% 0.20/0.55  thf('156', plain,
% 0.20/0.55      (((g1_orders_2 @ (u1_struct_0 @ sk_B) @ (u1_orders_2 @ sk_B))
% 0.20/0.55         = (g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('157', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (l1_orders_2 @ X0)
% 0.20/0.55          | ((u1_orders_2 @ X0) = (X1))
% 0.20/0.55          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.20/0.55              != (g1_orders_2 @ X2 @ X1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.55  thf('158', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1))
% 0.20/0.55            != (g1_orders_2 @ X1 @ X0))
% 0.20/0.55          | ((u1_orders_2 @ sk_B) = (X0))
% 0.20/0.55          | ~ (l1_orders_2 @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['156', '157'])).
% 0.20/0.55  thf('159', plain, ((l1_orders_2 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('160', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (((g1_orders_2 @ (u1_struct_0 @ sk_D_1) @ (u1_orders_2 @ sk_D_1))
% 0.20/0.55            != (g1_orders_2 @ X1 @ X0))
% 0.20/0.55          | ((u1_orders_2 @ sk_B) = (X0)))),
% 0.20/0.55      inference('demod', [status(thm)], ['158', '159'])).
% 0.20/0.55  thf('161', plain, (((u1_orders_2 @ sk_B) = (u1_orders_2 @ sk_D_1))),
% 0.20/0.55      inference('eq_res', [status(thm)], ['160'])).
% 0.20/0.55  thf('162', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.55          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_D_1))
% 0.20/0.55          | (r2_hidden @ (k4_tarski @ X0 @ X1) @ (u1_orders_2 @ sk_D_1))
% 0.20/0.55          | ~ (r1_orders_2 @ sk_B @ X0 @ X1))),
% 0.20/0.55      inference('demod', [status(thm)], ['153', '154', '155', '161'])).
% 0.20/0.55  thf('163', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (r1_orders_2 @ sk_B @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ X0)
% 0.20/0.55          | (r2_hidden @ (k4_tarski @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ X0) @ 
% 0.20/0.55             (u1_orders_2 @ sk_D_1))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_D_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['150', '162'])).
% 0.20/0.55  thf('164', plain,
% 0.20/0.55      ((~ (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55           (u1_struct_0 @ sk_D_1))
% 0.20/0.55        | (r2_hidden @ 
% 0.20/0.55           (k4_tarski @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55            (sk_G @ sk_E_1 @ sk_D_1 @ sk_C)) @ 
% 0.20/0.55           (u1_orders_2 @ sk_D_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['149', '163'])).
% 0.20/0.55  thf('165', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('clc', [status(thm)], ['120', '121'])).
% 0.20/0.55  thf('166', plain,
% 0.20/0.55      ((r2_hidden @ 
% 0.20/0.55        (k4_tarski @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55         (sk_G @ sk_E_1 @ sk_D_1 @ sk_C)) @ 
% 0.20/0.55        (u1_orders_2 @ sk_D_1))),
% 0.20/0.55      inference('demod', [status(thm)], ['164', '165'])).
% 0.20/0.55  thf('167', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.55          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (u1_orders_2 @ X1))
% 0.20/0.55          | (r1_orders_2 @ X1 @ X0 @ X2)
% 0.20/0.55          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.55          | ~ (l1_orders_2 @ X1))),
% 0.20/0.55      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.20/0.55  thf('168', plain,
% 0.20/0.55      ((~ (l1_orders_2 @ sk_D_1)
% 0.20/0.55        | ~ (m1_subset_1 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55             (u1_struct_0 @ sk_D_1))
% 0.20/0.55        | (r1_orders_2 @ sk_D_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55           (sk_G @ sk_E_1 @ sk_D_1 @ sk_C))
% 0.20/0.55        | ~ (m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55             (u1_struct_0 @ sk_D_1)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['166', '167'])).
% 0.20/0.55  thf('169', plain, ((l1_orders_2 @ sk_D_1)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('170', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_G @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('clc', [status(thm)], ['120', '121'])).
% 0.20/0.55  thf('171', plain,
% 0.20/0.55      ((m1_subset_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ (u1_struct_0 @ sk_D_1))),
% 0.20/0.55      inference('clc', [status(thm)], ['145', '146'])).
% 0.20/0.55  thf('172', plain,
% 0.20/0.55      ((r1_orders_2 @ sk_D_1 @ (sk_F @ sk_E_1 @ sk_D_1 @ sk_C) @ 
% 0.20/0.55        (sk_G @ sk_E_1 @ sk_D_1 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['168', '169', '170', '171'])).
% 0.20/0.55  thf('173', plain, ($false), inference('demod', [status(thm)], ['15', '172'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
