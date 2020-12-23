%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1623+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.DVqS4olnFG

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:51 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  169 (2564 expanded)
%              Number of leaves         :   23 ( 701 expanded)
%              Depth                    :   25
%              Number of atoms          : 1973 (47349 expanded)
%              Number of equality atoms :   48 (3241 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_waybel_0_type,type,(
    v1_waybel_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t3_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( l1_orders_2 @ B )
         => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
              = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                   => ( ( ( C = D )
                        & ( v1_waybel_0 @ C @ A ) )
                     => ( v1_waybel_0 @ D @ B ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( l1_orders_2 @ B )
           => ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) )
                = ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                 => ! [D: $i] :
                      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
                     => ( ( ( C = D )
                          & ( v1_waybel_0 @ C @ A ) )
                       => ( v1_waybel_0 @ D @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_waybel_0])).

thf('0',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X5 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( ( g1_orders_2 @ X8 @ X9 )
       != ( g1_orders_2 @ X6 @ X7 ) )
      | ( X9 = X7 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_B )
        = X0 )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_B )
        = X0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( u1_orders_2 @ sk_B )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('9',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X5 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X5 ) ) ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('10',plain,
    ( ( m1_subset_1 @ ( u1_orders_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_orders_2 @ sk_B ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( u1_orders_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( ( g1_orders_2 @ X8 @ X9 )
       != ( g1_orders_2 @ X6 @ X7 ) )
      | ( X8 = X6 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( u1_orders_2 @ sk_B )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('17',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf(d1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_waybel_0 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ~ ( ( r2_hidden @ C @ B )
                        & ( r2_hidden @ D @ B )
                        & ! [E: $i] :
                            ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                           => ~ ( ( r2_hidden @ E @ B )
                                & ( r1_orders_2 @ A @ C @ E )
                                & ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( v1_waybel_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_B )
      | ( v1_waybel_0 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_waybel_0 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_waybel_0 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','24'])).

thf('26',plain,(
    ~ ( v1_waybel_0 @ sk_D_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_C_1 = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ~ ( v1_waybel_0 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['25','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ( v1_waybel_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_B )
      | ( v1_waybel_0 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_waybel_0 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ X0 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_waybel_0 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    ~ ( v1_waybel_0 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('39',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v1_waybel_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_orders_2 @ X1 @ X2 @ ( sk_E @ X2 @ X3 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r1_orders_2 @ sk_A @ X1 @ ( sk_E @ X1 @ X0 @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_waybel_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r1_orders_2 @ sk_A @ X1 @ ( sk_E @ X1 @ X0 @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r1_orders_2 @ sk_A @ X0 @ ( sk_E @ X0 @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['39','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    sk_C_1 = sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 ) @ X0 )
      | ( v1_waybel_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_0])).

thf('51',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ( v1_waybel_0 @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( v1_waybel_0 @ sk_C_1 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ~ ( v1_waybel_0 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('55',plain,(
    r2_hidden @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r1_orders_2 @ sk_A @ X0 @ ( sk_E @ X0 @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['46','55'])).

thf('57',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( v1_waybel_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_B )
      | ( v1_waybel_0 @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_waybel_0 @ X0 @ sk_B )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ X0 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 )
    | ( v1_waybel_0 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    ~ ( v1_waybel_0 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('66',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    r1_orders_2 @ sk_A @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['57','66'])).

thf('68',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['25','28'])).

thf('69',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('70',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v1_waybel_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( m1_subset_1 @ ( sk_E @ X2 @ X3 @ X0 @ X1 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_E @ X1 @ X0 @ sk_C_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_waybel_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_E @ X1 @ X0 @ sk_C_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_E @ X0 @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,(
    r2_hidden @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['53','54'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( m1_subset_1 @ ( sk_E @ X0 @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,
    ( ( m1_subset_1 @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['68','78'])).

thf('80',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['64','65'])).

thf('81',plain,(
    m1_subset_1 @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

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

thf('83',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r1_orders_2 @ X12 @ X14 @ X11 )
      | ( r1_orders_2 @ X10 @ X15 @ X13 )
      | ( X11 != X13 )
      | ( X14 != X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X12 ) @ ( u1_orders_2 @ X12 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X10 ) @ ( u1_orders_2 @ X10 ) ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t1_yellow_0])).

thf('84',plain,(
    ! [X10: $i,X12: $i,X13: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X12 ) @ ( u1_orders_2 @ X12 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X10 ) @ ( u1_orders_2 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X10 ) )
      | ( r1_orders_2 @ X10 @ X15 @ X13 )
      | ~ ( r1_orders_2 @ X12 @ X15 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X10 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_B ) ) )
      | ~ ( l1_orders_2 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ( r1_orders_2 @ sk_B @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_B ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,
    ( ( u1_orders_2 @ sk_B )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['7'])).

thf('87',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('89',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ X0 @ X2 @ X1 )
      | ( r1_orders_2 @ sk_B @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['85','86','87','88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_B @ X0 @ X1 )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(eq_res,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_B @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r1_orders_2 @ sk_B @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_B @ X0 @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['81','94'])).

thf('96',plain,
    ( ( r1_orders_2 @ sk_B @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','95'])).

thf('97',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['25','28'])).

thf('98',plain,(
    r1_orders_2 @ sk_B @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X4 @ X0 )
      | ~ ( r1_orders_2 @ X1 @ ( sk_C @ X0 @ X1 ) @ X4 )
      | ~ ( r1_orders_2 @ X1 @ ( sk_D @ X0 @ X1 ) @ X4 )
      | ( v1_waybel_0 @ X0 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_0])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_B )
      | ( v1_waybel_0 @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_B @ ( sk_D @ X0 @ sk_B ) @ X1 )
      | ~ ( r1_orders_2 @ sk_B @ ( sk_C @ X0 @ sk_B ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['18'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( v1_waybel_0 @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_B @ ( sk_D @ X0 @ sk_B ) @ X1 )
      | ~ ( r1_orders_2 @ sk_B @ ( sk_C @ X0 @ sk_B ) @ X1 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ~ ( r1_orders_2 @ sk_B @ ( sk_C @ sk_C_1 @ sk_B ) @ X0 )
      | ~ ( r1_orders_2 @ sk_B @ ( sk_D @ sk_C_1 @ sk_B ) @ X0 )
      | ( v1_waybel_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['99','105'])).

thf('107',plain,
    ( ( v1_waybel_0 @ sk_C_1 @ sk_B )
    | ~ ( r1_orders_2 @ sk_B @ ( sk_D @ sk_C_1 @ sk_B ) @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_C_1 )
    | ~ ( m1_subset_1 @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['98','106'])).

thf('108',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['25','28'])).

thf('109',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('110',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v1_waybel_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( r2_hidden @ ( sk_E @ X2 @ X3 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_0])).

thf('112',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_E @ X1 @ X0 @ sk_C_1 @ sk_A ) @ sk_C_1 )
      | ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_waybel_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_E @ X1 @ X0 @ sk_C_1 @ sk_A ) @ sk_C_1 )
      | ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_E @ X0 @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_C_1 )
      | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['109','115'])).

thf('117',plain,(
    r2_hidden @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['53','54'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r2_hidden @ ( sk_E @ X0 @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['116','117'])).

thf('119',plain,
    ( ( r2_hidden @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_C_1 )
    | ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['108','118'])).

thf('120',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['64','65'])).

thf('121',plain,(
    r2_hidden @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ sk_C_1 ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    m1_subset_1 @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('123',plain,
    ( ( v1_waybel_0 @ sk_C_1 @ sk_B )
    | ~ ( r1_orders_2 @ sk_B @ ( sk_D @ sk_C_1 @ sk_B ) @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','121','122'])).

thf('124',plain,(
    ~ ( v1_waybel_0 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('125',plain,(
    ~ ( r1_orders_2 @ sk_B @ ( sk_D @ sk_C_1 @ sk_B ) @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ ( sk_C @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['25','28'])).

thf('127',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('128',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) )
      | ~ ( v1_waybel_0 @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_orders_2 @ X1 @ X3 @ ( sk_E @ X2 @ X3 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X3 @ X0 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_waybel_0])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r1_orders_2 @ sk_A @ X0 @ ( sk_E @ X1 @ X0 @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v1_waybel_0 @ sk_C_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_waybel_0 @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r1_orders_2 @ sk_A @ X0 @ ( sk_E @ X1 @ X0 @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ sk_B ) @ ( sk_E @ X0 @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['127','133'])).

thf('135',plain,(
    r2_hidden @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['53','54'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ sk_B ) @ ( sk_E @ X0 @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ sk_B ) @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['126','136'])).

thf('138',plain,(
    r2_hidden @ ( sk_C @ sk_C_1 @ sk_B ) @ sk_C_1 ),
    inference(clc,[status(thm)],['64','65'])).

thf('139',plain,(
    r1_orders_2 @ sk_A @ ( sk_D @ sk_C_1 @ sk_B ) @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_B @ X0 @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['81','94'])).

thf('141',plain,
    ( ( r1_orders_2 @ sk_B @ ( sk_D @ sk_C_1 @ sk_B ) @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_1 @ sk_B ) @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('143',plain,(
    r1_orders_2 @ sk_B @ ( sk_D @ sk_C_1 @ sk_B ) @ ( sk_E @ ( sk_C @ sk_C_1 @ sk_B ) @ ( sk_D @ sk_C_1 @ sk_B ) @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['141','142'])).

thf('144',plain,(
    $false ),
    inference(demod,[status(thm)],['125','143'])).


%------------------------------------------------------------------------------
