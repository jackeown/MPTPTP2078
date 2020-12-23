%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xS7Davml6o

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 572 expanded)
%              Number of leaves         :   22 ( 166 expanded)
%              Depth                    :   18
%              Number of atoms          : 1032 (13896 expanded)
%              Number of equality atoms :   48 ( 889 expanded)
%              Maximal formula depth    :   21 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t1_yellow_0,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
                                   => ( r2_orders_2 @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t1_yellow_0])).

thf('0',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_orders_2 @ sk_B @ sk_E @ sk_F )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_orders_2 @ A @ B @ C )
              <=> ( ( r1_orders_2 @ A @ B @ C )
                  & ( B != C ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_A @ sk_C @ X0 )
      | ~ ( r2_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X5 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( u1_orders_2 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_C @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_C @ sk_D ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C @ sk_D ) @ ( u1_orders_2 @ sk_A ) )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X6 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( ( g1_orders_2 @ X9 @ X10 )
       != ( g1_orders_2 @ X7 @ X8 ) )
      | ( X10 = X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_B )
        = X0 )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_B )
        = X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,
    ( ( u1_orders_2 @ sk_B )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('29',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X5 ) @ ( u1_orders_2 @ X4 ) )
      | ( r1_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_orders_2 @ sk_B @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r1_orders_2 @ sk_B @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( u1_orders_2 @ sk_B )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('34',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X6 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X6 ) ) ) )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('35',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( ( g1_orders_2 @ X9 @ X10 )
       != ( g1_orders_2 @ X7 @ X8 ) )
      | ( X9 = X7 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B )
        = X1 )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( u1_orders_2 @ sk_B )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['27'])).

thf('40',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_struct_0 @ sk_B )
        = X1 ) ) ),
    inference(demod,[status(thm)],['37','40','41'])).

thf('43',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['42'])).

thf('44',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['42'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_B @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','43','44'])).

thf('46',plain,
    ( ( ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_B @ sk_C @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['20','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( r1_orders_2 @ sk_B @ sk_C @ sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_E @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    sk_C = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r1_orders_2 @ X1 @ X0 @ X2 )
      | ( X0 = X2 )
      | ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_orders_2 @ sk_B @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( r1_orders_2 @ sk_B @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_orders_2 @ sk_B @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( r1_orders_2 @ sk_B @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['42'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_B @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( r1_orders_2 @ sk_B @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r1_orders_2 @ sk_B @ sk_C @ sk_D )
    | ( sk_C = sk_D )
    | ( r2_orders_2 @ sk_B @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['50','59'])).

thf('61',plain,
    ( ( ( r2_orders_2 @ sk_B @ sk_C @ sk_D )
      | ( sk_C = sk_D ) )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['49','60'])).

thf('62',plain,
    ( ~ ( r1_orders_2 @ sk_B @ sk_E @ sk_F )
    | ~ ( r2_orders_2 @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ~ ( r2_orders_2 @ sk_B @ sk_E @ sk_F )
   <= ~ ( r2_orders_2 @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,(
    sk_C = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    sk_D = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ~ ( r2_orders_2 @ sk_B @ sk_C @ sk_D )
   <= ~ ( r2_orders_2 @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ~ ( r2_orders_2 @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_orders_2 @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['62'])).

thf('68',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ~ ( r2_orders_2 @ sk_B @ sk_E @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ~ ( r2_orders_2 @ sk_B @ sk_E @ sk_F )
    | ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['68'])).

thf('70',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['68'])).

thf('71',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D )
    | ( r2_hidden @ ( k4_tarski @ sk_C @ sk_D ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('72',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_C @ sk_D ) @ ( u1_orders_2 @ sk_A ) )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ ( u1_orders_2 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_B @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['32','43','44'])).

thf('74',plain,
    ( ( ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r1_orders_2 @ sk_B @ sk_C @ sk_D )
      | ~ ( m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_D @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( r1_orders_2 @ sk_B @ sk_C @ sk_D )
   <= ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,
    ( ~ ( r1_orders_2 @ sk_B @ sk_E @ sk_F )
   <= ~ ( r1_orders_2 @ sk_B @ sk_E @ sk_F ) ),
    inference(split,[status(esa)],['62'])).

thf('79',plain,(
    sk_C = sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    sk_D = sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ~ ( r1_orders_2 @ sk_B @ sk_C @ sk_D )
   <= ~ ( r1_orders_2 @ sk_B @ sk_E @ sk_F ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,
    ( ( r1_orders_2 @ sk_B @ sk_E @ sk_F )
    | ~ ( r1_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['77','81'])).

thf('83',plain,(
    ~ ( r2_orders_2 @ sk_B @ sk_E @ sk_F ) ),
    inference('sat_resolution*',[status(thm)],['67','69','82'])).

thf('84',plain,(
    ~ ( r2_orders_2 @ sk_B @ sk_C @ sk_D ) ),
    inference(simpl_trail,[status(thm)],['66','83'])).

thf('85',plain,
    ( ( sk_C = sk_D )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['61','84'])).

thf('86',plain,
    ( ( r2_orders_2 @ sk_A @ sk_C @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['3','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( r2_orders_2 @ X1 @ X0 @ X2 )
      | ( X0 != X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('89',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ~ ( r2_orders_2 @ X1 @ X2 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_C )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['87','89'])).

thf('91',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['86','92'])).

thf('94',plain,
    ( ~ ( r1_orders_2 @ sk_B @ sk_E @ sk_F )
    | ( r2_orders_2 @ sk_A @ sk_C @ sk_D ) ),
    inference(split,[status(esa)],['2'])).

thf('95',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','93','94','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xS7Davml6o
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:21:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 154 iterations in 0.050s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.50  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.21/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.50  thf(sk_E_type, type, sk_E: $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(sk_F_type, type, sk_F: $i).
% 0.21/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.50  thf(t1_yellow_0, conjecture,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_orders_2 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( l1_orders_2 @ B ) =>
% 0.21/0.50           ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) =
% 0.21/0.50               ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) ) =>
% 0.21/0.50             ( ![C:$i]:
% 0.21/0.50               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50                 ( ![D:$i]:
% 0.21/0.50                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50                     ( ![E:$i]:
% 0.21/0.50                       ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.50                         ( ![F:$i]:
% 0.21/0.50                           ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.50                             ( ( ( ( C ) = ( E ) ) & ( ( D ) = ( F ) ) ) =>
% 0.21/0.50                               ( ( ( r1_orders_2 @ A @ C @ D ) =>
% 0.21/0.50                                   ( r1_orders_2 @ B @ E @ F ) ) & 
% 0.21/0.50                                 ( ( r2_orders_2 @ A @ C @ D ) =>
% 0.21/0.50                                   ( r2_orders_2 @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i]:
% 0.21/0.50        ( ( l1_orders_2 @ A ) =>
% 0.21/0.50          ( ![B:$i]:
% 0.21/0.50            ( ( l1_orders_2 @ B ) =>
% 0.21/0.50              ( ( ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) =
% 0.21/0.50                  ( g1_orders_2 @ ( u1_struct_0 @ B ) @ ( u1_orders_2 @ B ) ) ) =>
% 0.21/0.50                ( ![C:$i]:
% 0.21/0.50                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50                    ( ![D:$i]:
% 0.21/0.50                      ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50                        ( ![E:$i]:
% 0.21/0.50                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.50                            ( ![F:$i]:
% 0.21/0.50                              ( ( m1_subset_1 @ F @ ( u1_struct_0 @ B ) ) =>
% 0.21/0.50                                ( ( ( ( C ) = ( E ) ) & ( ( D ) = ( F ) ) ) =>
% 0.21/0.50                                  ( ( ( r1_orders_2 @ A @ C @ D ) =>
% 0.21/0.50                                      ( r1_orders_2 @ B @ E @ F ) ) & 
% 0.21/0.50                                    ( ( r2_orders_2 @ A @ C @ D ) =>
% 0.21/0.50                                      ( r2_orders_2 @ B @ E @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t1_yellow_0])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      (((r1_orders_2 @ sk_A @ sk_C @ sk_D) | (r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (((r1_orders_2 @ sk_A @ sk_C @ sk_D)) | 
% 0.21/0.50       ((r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      ((~ (r1_orders_2 @ sk_B @ sk_E @ sk_F)
% 0.21/0.50        | (r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (((r2_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.21/0.50         <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (((r2_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.21/0.50         <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('5', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('6', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d10_orders_2, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_orders_2 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.21/0.50                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.21/0.50          | ~ (r2_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.50          | (r1_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.50          | ~ (l1_orders_2 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l1_orders_2 @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.21/0.50          | ~ (r2_orders_2 @ sk_A @ sk_C @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.50  thf('9', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (r1_orders_2 @ sk_A @ sk_C @ X0)
% 0.21/0.50          | ~ (r2_orders_2 @ sk_A @ sk_C @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('11', plain,
% 0.21/0.50      ((~ (r2_orders_2 @ sk_A @ sk_C @ sk_D)
% 0.21/0.50        | (r1_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '10'])).
% 0.21/0.50  thf('12', plain,
% 0.21/0.50      (((r1_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.21/0.50         <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['4', '11'])).
% 0.21/0.50  thf('13', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(d9_orders_2, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_orders_2 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50           ( ![C:$i]:
% 0.21/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.50               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.21/0.50                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.21/0.50          | ~ (r1_orders_2 @ X4 @ X3 @ X5)
% 0.21/0.50          | (r2_hidden @ (k4_tarski @ X3 @ X5) @ (u1_orders_2 @ X4))
% 0.21/0.50          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.21/0.50          | ~ (l1_orders_2 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l1_orders_2 @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (r2_hidden @ (k4_tarski @ sk_C @ X0) @ (u1_orders_2 @ sk_A))
% 0.21/0.50          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.21/0.50  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (r2_hidden @ (k4_tarski @ sk_C @ X0) @ (u1_orders_2 @ sk_A))
% 0.21/0.50          | ~ (r1_orders_2 @ sk_A @ sk_C @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      ((~ (r1_orders_2 @ sk_A @ sk_C @ sk_D)
% 0.21/0.50        | (r2_hidden @ (k4_tarski @ sk_C @ sk_D) @ (u1_orders_2 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '18'])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (((r2_hidden @ (k4_tarski @ sk_C @ sk_D) @ (u1_orders_2 @ sk_A)))
% 0.21/0.50         <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['12', '19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.21/0.50         = (g1_orders_2 @ (u1_struct_0 @ sk_B) @ (u1_orders_2 @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(dt_u1_orders_2, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( l1_orders_2 @ A ) =>
% 0.21/0.50       ( m1_subset_1 @
% 0.21/0.50         ( u1_orders_2 @ A ) @ 
% 0.21/0.50         ( k1_zfmisc_1 @
% 0.21/0.50           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X6 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (u1_orders_2 @ X6) @ 
% 0.21/0.50           (k1_zfmisc_1 @ 
% 0.21/0.50            (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X6))))
% 0.21/0.50          | ~ (l1_orders_2 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.21/0.50  thf(free_g1_orders_2, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.21/0.50       ( ![C:$i,D:$i]:
% 0.21/0.50         ( ( ( g1_orders_2 @ A @ B ) = ( g1_orders_2 @ C @ D ) ) =>
% 0.21/0.50           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.50         (((g1_orders_2 @ X9 @ X10) != (g1_orders_2 @ X7 @ X8))
% 0.21/0.50          | ((X10) = (X8))
% 0.21/0.50          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X9))))),
% 0.21/0.50      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (l1_orders_2 @ X0)
% 0.21/0.50          | ((u1_orders_2 @ X0) = (X1))
% 0.21/0.50          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.21/0.50              != (g1_orders_2 @ X2 @ X1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.21/0.50            != (g1_orders_2 @ X1 @ X0))
% 0.21/0.50          | ((u1_orders_2 @ sk_B) = (X0))
% 0.21/0.50          | ~ (l1_orders_2 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['21', '24'])).
% 0.21/0.50  thf('26', plain, ((l1_orders_2 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.21/0.50            != (g1_orders_2 @ X1 @ X0))
% 0.21/0.50          | ((u1_orders_2 @ sk_B) = (X0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf('28', plain, (((u1_orders_2 @ sk_B) = (u1_orders_2 @ sk_A))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['27'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.21/0.50          | ~ (r2_hidden @ (k4_tarski @ X3 @ X5) @ (u1_orders_2 @ X4))
% 0.21/0.50          | (r1_orders_2 @ X4 @ X3 @ X5)
% 0.21/0.50          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.21/0.50          | ~ (l1_orders_2 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.21/0.50          | ~ (l1_orders_2 @ sk_B)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.50          | (r1_orders_2 @ sk_B @ X1 @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.50  thf('31', plain, ((l1_orders_2 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.50          | (r1_orders_2 @ sk_B @ X1 @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_B)))),
% 0.21/0.50      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.50  thf('33', plain, (((u1_orders_2 @ sk_B) = (u1_orders_2 @ sk_A))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['27'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X6 : $i]:
% 0.21/0.50         ((m1_subset_1 @ (u1_orders_2 @ X6) @ 
% 0.21/0.50           (k1_zfmisc_1 @ 
% 0.21/0.50            (k2_zfmisc_1 @ (u1_struct_0 @ X6) @ (u1_struct_0 @ X6))))
% 0.21/0.50          | ~ (l1_orders_2 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.21/0.50  thf('35', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.50         (((g1_orders_2 @ X9 @ X10) != (g1_orders_2 @ X7 @ X8))
% 0.21/0.50          | ((X9) = (X7))
% 0.21/0.50          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X9))))),
% 0.21/0.50      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (l1_orders_2 @ X0)
% 0.21/0.50          | ((u1_struct_0 @ X0) = (X1))
% 0.21/0.50          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.21/0.50              != (g1_orders_2 @ X1 @ X2)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((g1_orders_2 @ (u1_struct_0 @ sk_B) @ (u1_orders_2 @ sk_A))
% 0.21/0.50            != (g1_orders_2 @ X1 @ X0))
% 0.21/0.50          | ((u1_struct_0 @ sk_B) = (X1))
% 0.21/0.50          | ~ (l1_orders_2 @ sk_B))),
% 0.21/0.50      inference('sup-', [status(thm)], ['33', '36'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.21/0.50         = (g1_orders_2 @ (u1_struct_0 @ sk_B) @ (u1_orders_2 @ sk_B)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('39', plain, (((u1_orders_2 @ sk_B) = (u1_orders_2 @ sk_A))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['27'])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.21/0.50         = (g1_orders_2 @ (u1_struct_0 @ sk_B) @ (u1_orders_2 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['38', '39'])).
% 0.21/0.50  thf('41', plain, ((l1_orders_2 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (((g1_orders_2 @ (u1_struct_0 @ sk_A) @ (u1_orders_2 @ sk_A))
% 0.21/0.50            != (g1_orders_2 @ X1 @ X0))
% 0.21/0.50          | ((u1_struct_0 @ sk_B) = (X1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['37', '40', '41'])).
% 0.21/0.50  thf('43', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['42'])).
% 0.21/0.50  thf('44', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['42'])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (r1_orders_2 @ sk_B @ X1 @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['32', '43', '44'])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      (((~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.21/0.50         | (r1_orders_2 @ sk_B @ sk_C @ sk_D)
% 0.21/0.50         | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))))
% 0.21/0.50         <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['20', '45'])).
% 0.21/0.50  thf('47', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('48', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (((r1_orders_2 @ sk_B @ sk_C @ sk_D))
% 0.21/0.50         <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.50      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.21/0.50  thf('50', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('51', plain, ((m1_subset_1 @ sk_E @ (u1_struct_0 @ sk_B))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('52', plain, (((sk_C) = (sk_E))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('53', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.21/0.50      inference('demod', [status(thm)], ['51', '52'])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.21/0.50          | ~ (r1_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.50          | ((X0) = (X2))
% 0.21/0.50          | (r2_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.50          | ~ (l1_orders_2 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (l1_orders_2 @ sk_B)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.50          | (r2_orders_2 @ sk_B @ sk_C @ X0)
% 0.21/0.50          | ((sk_C) = (X0))
% 0.21/0.50          | ~ (r1_orders_2 @ sk_B @ sk_C @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.50  thf('56', plain, ((l1_orders_2 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B))
% 0.21/0.50          | (r2_orders_2 @ sk_B @ sk_C @ X0)
% 0.21/0.50          | ((sk_C) = (X0))
% 0.21/0.50          | ~ (r1_orders_2 @ sk_B @ sk_C @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['55', '56'])).
% 0.21/0.50  thf('58', plain, (((u1_struct_0 @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('eq_res', [status(thm)], ['42'])).
% 0.21/0.50  thf('59', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (r2_orders_2 @ sk_B @ sk_C @ X0)
% 0.21/0.50          | ((sk_C) = (X0))
% 0.21/0.50          | ~ (r1_orders_2 @ sk_B @ sk_C @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['57', '58'])).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      ((~ (r1_orders_2 @ sk_B @ sk_C @ sk_D)
% 0.21/0.50        | ((sk_C) = (sk_D))
% 0.21/0.50        | (r2_orders_2 @ sk_B @ sk_C @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['50', '59'])).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      ((((r2_orders_2 @ sk_B @ sk_C @ sk_D) | ((sk_C) = (sk_D))))
% 0.21/0.50         <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['49', '60'])).
% 0.21/0.50  thf('62', plain,
% 0.21/0.50      ((~ (r1_orders_2 @ sk_B @ sk_E @ sk_F)
% 0.21/0.50        | ~ (r2_orders_2 @ sk_B @ sk_E @ sk_F))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      ((~ (r2_orders_2 @ sk_B @ sk_E @ sk_F))
% 0.21/0.50         <= (~ ((r2_orders_2 @ sk_B @ sk_E @ sk_F)))),
% 0.21/0.50      inference('split', [status(esa)], ['62'])).
% 0.21/0.50  thf('64', plain, (((sk_C) = (sk_E))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('65', plain, (((sk_D) = (sk_F))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('66', plain,
% 0.21/0.50      ((~ (r2_orders_2 @ sk_B @ sk_C @ sk_D))
% 0.21/0.50         <= (~ ((r2_orders_2 @ sk_B @ sk_E @ sk_F)))),
% 0.21/0.50      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.21/0.50  thf('67', plain,
% 0.21/0.50      (~ ((r2_orders_2 @ sk_B @ sk_E @ sk_F)) | 
% 0.21/0.50       ~ ((r1_orders_2 @ sk_B @ sk_E @ sk_F))),
% 0.21/0.50      inference('split', [status(esa)], ['62'])).
% 0.21/0.50  thf('68', plain,
% 0.21/0.50      (((r1_orders_2 @ sk_A @ sk_C @ sk_D)
% 0.21/0.50        | ~ (r2_orders_2 @ sk_B @ sk_E @ sk_F))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('69', plain,
% 0.21/0.50      (~ ((r2_orders_2 @ sk_B @ sk_E @ sk_F)) | 
% 0.21/0.50       ((r1_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.50      inference('split', [status(esa)], ['68'])).
% 0.21/0.50  thf('70', plain,
% 0.21/0.50      (((r1_orders_2 @ sk_A @ sk_C @ sk_D))
% 0.21/0.50         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.50      inference('split', [status(esa)], ['68'])).
% 0.21/0.50  thf('71', plain,
% 0.21/0.50      ((~ (r1_orders_2 @ sk_A @ sk_C @ sk_D)
% 0.21/0.50        | (r2_hidden @ (k4_tarski @ sk_C @ sk_D) @ (u1_orders_2 @ sk_A)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['13', '18'])).
% 0.21/0.50  thf('72', plain,
% 0.21/0.50      (((r2_hidden @ (k4_tarski @ sk_C @ sk_D) @ (u1_orders_2 @ sk_A)))
% 0.21/0.50         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.50  thf('73', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r2_hidden @ (k4_tarski @ X1 @ X0) @ (u1_orders_2 @ sk_A))
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.21/0.50          | (r1_orders_2 @ sk_B @ X1 @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.21/0.50      inference('demod', [status(thm)], ['32', '43', '44'])).
% 0.21/0.50  thf('74', plain,
% 0.21/0.50      (((~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.21/0.50         | (r1_orders_2 @ sk_B @ sk_C @ sk_D)
% 0.21/0.50         | ~ (m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))))
% 0.21/0.50         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['72', '73'])).
% 0.21/0.50  thf('75', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('76', plain, ((m1_subset_1 @ sk_D @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('77', plain,
% 0.21/0.50      (((r1_orders_2 @ sk_B @ sk_C @ sk_D))
% 0.21/0.50         <= (((r1_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.50      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.21/0.50  thf('78', plain,
% 0.21/0.50      ((~ (r1_orders_2 @ sk_B @ sk_E @ sk_F))
% 0.21/0.50         <= (~ ((r1_orders_2 @ sk_B @ sk_E @ sk_F)))),
% 0.21/0.50      inference('split', [status(esa)], ['62'])).
% 0.21/0.50  thf('79', plain, (((sk_C) = (sk_E))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('80', plain, (((sk_D) = (sk_F))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('81', plain,
% 0.21/0.50      ((~ (r1_orders_2 @ sk_B @ sk_C @ sk_D))
% 0.21/0.50         <= (~ ((r1_orders_2 @ sk_B @ sk_E @ sk_F)))),
% 0.21/0.50      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.21/0.50  thf('82', plain,
% 0.21/0.50      (((r1_orders_2 @ sk_B @ sk_E @ sk_F)) | 
% 0.21/0.50       ~ ((r1_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['77', '81'])).
% 0.21/0.50  thf('83', plain, (~ ((r2_orders_2 @ sk_B @ sk_E @ sk_F))),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['67', '69', '82'])).
% 0.21/0.50  thf('84', plain, (~ (r2_orders_2 @ sk_B @ sk_C @ sk_D)),
% 0.21/0.50      inference('simpl_trail', [status(thm)], ['66', '83'])).
% 0.21/0.50  thf('85', plain,
% 0.21/0.50      ((((sk_C) = (sk_D))) <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.50      inference('clc', [status(thm)], ['61', '84'])).
% 0.21/0.50  thf('86', plain,
% 0.21/0.50      (((r2_orders_2 @ sk_A @ sk_C @ sk_C))
% 0.21/0.50         <= (((r2_orders_2 @ sk_A @ sk_C @ sk_D)))),
% 0.21/0.50      inference('demod', [status(thm)], ['3', '85'])).
% 0.21/0.50  thf('87', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('88', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.21/0.50          | ~ (r2_orders_2 @ X1 @ X0 @ X2)
% 0.21/0.50          | ((X0) != (X2))
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.21/0.50          | ~ (l1_orders_2 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.21/0.50  thf('89', plain,
% 0.21/0.50      (![X1 : $i, X2 : $i]:
% 0.21/0.50         (~ (l1_orders_2 @ X1)
% 0.21/0.50          | ~ (r2_orders_2 @ X1 @ X2 @ X2)
% 0.21/0.50          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1)))),
% 0.21/0.50      inference('simplify', [status(thm)], ['88'])).
% 0.21/0.50  thf('90', plain,
% 0.21/0.50      ((~ (r2_orders_2 @ sk_A @ sk_C @ sk_C) | ~ (l1_orders_2 @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['87', '89'])).
% 0.21/0.50  thf('91', plain, ((l1_orders_2 @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('92', plain, (~ (r2_orders_2 @ sk_A @ sk_C @ sk_C)),
% 0.21/0.50      inference('demod', [status(thm)], ['90', '91'])).
% 0.21/0.50  thf('93', plain, (~ ((r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.50      inference('sup-', [status(thm)], ['86', '92'])).
% 0.21/0.50  thf('94', plain,
% 0.21/0.50      (~ ((r1_orders_2 @ sk_B @ sk_E @ sk_F)) | 
% 0.21/0.50       ((r2_orders_2 @ sk_A @ sk_C @ sk_D))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('95', plain, ($false),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['1', '93', '94', '82'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
