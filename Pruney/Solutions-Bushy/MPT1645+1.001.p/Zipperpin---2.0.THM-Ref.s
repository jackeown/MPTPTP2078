%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1645+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OJzVcA0Q53

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 353 expanded)
%              Number of leaves         :   22 ( 104 expanded)
%              Depth                    :   20
%              Number of atoms          : 1097 (6899 expanded)
%              Number of equality atoms :   65 ( 432 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v12_waybel_0_type,type,(
    v12_waybel_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_waybel_0_type,type,(
    k4_waybel_0: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_waybel_0_type,type,(
    k3_waybel_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(t25_waybel_0,conjecture,(
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
                   => ( ( C = D )
                     => ( ( ( v12_waybel_0 @ C @ A )
                         => ( v12_waybel_0 @ D @ B ) )
                        & ( ( v13_waybel_0 @ C @ A )
                         => ( v13_waybel_0 @ D @ B ) ) ) ) ) ) ) ) ) )).

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
                     => ( ( C = D )
                       => ( ( ( v12_waybel_0 @ C @ A )
                           => ( v12_waybel_0 @ D @ B ) )
                          & ( ( v13_waybel_0 @ C @ A )
                           => ( v13_waybel_0 @ D @ B ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_waybel_0])).

thf('0',plain,
    ( ( v12_waybel_0 @ sk_C @ sk_A )
    | ( v13_waybel_0 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( v12_waybel_0 @ sk_C @ sk_A )
    | ( v13_waybel_0 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v12_waybel_0 @ sk_D @ sk_B )
    | ~ ( v13_waybel_0 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v12_waybel_0 @ sk_D @ sk_B )
    | ~ ( v13_waybel_0 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( v12_waybel_0 @ sk_C @ sk_A )
    | ~ ( v13_waybel_0 @ sk_D @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v12_waybel_0 @ sk_C @ sk_A )
    | ~ ( v13_waybel_0 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ~ ( v12_waybel_0 @ sk_D @ sk_B )
    | ( v13_waybel_0 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v13_waybel_0 @ sk_C @ sk_A )
   <= ( v13_waybel_0 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v13_waybel_0 @ B @ A )
          <=> ( r1_tarski @ ( k4_waybel_0 @ A @ B ) @ B ) ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v13_waybel_0 @ X11 @ X12 )
      | ( r1_tarski @ ( k4_waybel_0 @ X12 @ X11 ) @ X11 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t24_waybel_0])).

thf('10',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_tarski @ ( k4_waybel_0 @ sk_A @ sk_C ) @ sk_C )
    | ~ ( v13_waybel_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r1_tarski @ ( k4_waybel_0 @ sk_A @ sk_C ) @ sk_C )
    | ~ ( v13_waybel_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r1_tarski @ ( k4_waybel_0 @ sk_A @ sk_C ) @ sk_C )
   <= ( v13_waybel_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( r1_tarski @ ( k4_waybel_0 @ X12 @ X11 ) @ X11 )
      | ( v13_waybel_0 @ X11 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t24_waybel_0])).

thf('18',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ( v13_waybel_0 @ sk_C @ sk_B )
    | ~ ( r1_tarski @ ( k4_waybel_0 @ sk_B @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v13_waybel_0 @ sk_C @ sk_B )
    | ~ ( r1_tarski @ ( k4_waybel_0 @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('23',plain,(
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

thf('24',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( g1_orders_2 @ X3 @ X4 )
       != ( g1_orders_2 @ X1 @ X2 ) )
      | ( X4 = X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_B )
        = X0 )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X1 @ X0 ) )
      | ( ( u1_orders_2 @ sk_B )
        = X0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( u1_orders_2 @ sk_B )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('31',plain,
    ( ( m1_subset_1 @ ( u1_orders_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) )
    | ~ ( l1_orders_2 @ sk_B ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ ( u1_orders_2 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ sk_B ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( g1_orders_2 @ X3 @ X4 )
       != ( g1_orders_2 @ X1 @ X2 ) )
      | ( X3 = X1 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( u1_orders_2 @ sk_B )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['28'])).

thf('38',plain,
    ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
    = ( g1_orders_2 @ ( u1_struct_0 @ sk_B ) @ ( u1_orders_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( u1_struct_0 @ sk_B )
        = X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','38'])).

thf('40',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['39'])).

thf(t13_waybel_0,axiom,(
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
                   => ( ( C = D )
                     => ( ( ( k3_waybel_0 @ A @ C )
                          = ( k3_waybel_0 @ B @ D ) )
                        & ( ( k4_waybel_0 @ A @ C )
                          = ( k4_waybel_0 @ B @ D ) ) ) ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( ( k4_waybel_0 @ X7 @ X8 )
        = ( k4_waybel_0 @ X5 @ X6 ) )
      | ( X8 != X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X7 ) @ ( u1_orders_2 @ X7 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X5 ) @ ( u1_orders_2 @ X5 ) ) )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t13_waybel_0])).

thf('42',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_orders_2 @ X7 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X7 ) @ ( u1_orders_2 @ X7 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X5 ) @ ( u1_orders_2 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( k4_waybel_0 @ X7 @ X6 )
        = ( k4_waybel_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_B ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k4_waybel_0 @ sk_B @ X1 )
        = ( k4_waybel_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ( u1_orders_2 @ sk_B )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['28'])).

thf('45',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['39'])).

thf('46',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k4_waybel_0 @ sk_B @ X1 )
        = ( k4_waybel_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k4_waybel_0 @ sk_B @ X0 )
        = ( k4_waybel_0 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( ( k4_waybel_0 @ sk_B @ X0 )
        = ( k4_waybel_0 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k4_waybel_0 @ sk_B @ X0 )
        = ( k4_waybel_0 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k4_waybel_0 @ sk_B @ sk_C )
    = ( k4_waybel_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['21','51'])).

thf('53',plain,
    ( ( v13_waybel_0 @ sk_C @ sk_B )
    | ~ ( r1_tarski @ ( k4_waybel_0 @ sk_A @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['20','52'])).

thf('54',plain,
    ( ( v13_waybel_0 @ sk_C @ sk_B )
   <= ( v13_waybel_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['13','53'])).

thf('55',plain,
    ( ~ ( v13_waybel_0 @ sk_D @ sk_B )
   <= ~ ( v13_waybel_0 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('56',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ~ ( v13_waybel_0 @ sk_C @ sk_B )
   <= ~ ( v13_waybel_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v13_waybel_0 @ sk_C @ sk_A )
    | ( v13_waybel_0 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,
    ( ~ ( v12_waybel_0 @ sk_D @ sk_B )
    | ( v13_waybel_0 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['6'])).

thf('60',plain,
    ( ( v12_waybel_0 @ sk_C @ sk_A )
   <= ( v12_waybel_0 @ sk_C @ sk_A ) ),
    inference(split,[status(esa)],['4'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v12_waybel_0 @ B @ A )
          <=> ( r1_tarski @ ( k3_waybel_0 @ A @ B ) @ B ) ) ) ) )).

thf('62',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v12_waybel_0 @ X9 @ X10 )
      | ( r1_tarski @ ( k3_waybel_0 @ X10 @ X9 ) @ X9 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t23_waybel_0])).

thf('63',plain,
    ( ~ ( l1_orders_2 @ sk_A )
    | ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_C ) @ sk_C )
    | ~ ( v12_waybel_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_C ) @ sk_C )
    | ~ ( v12_waybel_0 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_C ) @ sk_C )
   <= ( v12_waybel_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('68',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( r1_tarski @ ( k3_waybel_0 @ X10 @ X9 ) @ X9 )
      | ( v12_waybel_0 @ X9 @ X10 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t23_waybel_0])).

thf('69',plain,
    ( ~ ( l1_orders_2 @ sk_B )
    | ( v12_waybel_0 @ sk_C @ sk_B )
    | ~ ( r1_tarski @ ( k3_waybel_0 @ sk_B @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( v12_waybel_0 @ sk_C @ sk_B )
    | ~ ( r1_tarski @ ( k3_waybel_0 @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['39'])).

thf('74',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ( ( k3_waybel_0 @ X7 @ X8 )
        = ( k3_waybel_0 @ X5 @ X6 ) )
      | ( X8 != X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X7 ) @ ( u1_orders_2 @ X7 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X5 ) @ ( u1_orders_2 @ X5 ) ) )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t13_waybel_0])).

thf('75',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( l1_orders_2 @ X7 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X7 ) @ ( u1_orders_2 @ X7 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X5 ) @ ( u1_orders_2 @ X5 ) ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ( ( k3_waybel_0 @ X7 @ X6 )
        = ( k3_waybel_0 @ X5 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_orders_2 @ X5 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_B ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k3_waybel_0 @ sk_B @ X1 )
        = ( k3_waybel_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
      | ~ ( l1_orders_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,
    ( ( u1_orders_2 @ sk_B )
    = ( u1_orders_2 @ sk_A ) ),
    inference(eq_res,[status(thm)],['28'])).

thf('78',plain,
    ( ( u1_struct_0 @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(eq_res,[status(thm)],['39'])).

thf('79',plain,(
    l1_orders_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ sk_A ) @ ( u1_orders_2 @ sk_A ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( ( k3_waybel_0 @ sk_B @ X1 )
        = ( k3_waybel_0 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( k3_waybel_0 @ sk_B @ X0 )
        = ( k3_waybel_0 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference(eq_res,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ( ( k3_waybel_0 @ sk_B @ X0 )
        = ( k3_waybel_0 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k3_waybel_0 @ sk_B @ X0 )
        = ( k3_waybel_0 @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k3_waybel_0 @ sk_B @ sk_C )
    = ( k3_waybel_0 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['72','84'])).

thf('86',plain,
    ( ( v12_waybel_0 @ sk_C @ sk_B )
    | ~ ( r1_tarski @ ( k3_waybel_0 @ sk_A @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['71','85'])).

thf('87',plain,
    ( ( v12_waybel_0 @ sk_C @ sk_B )
   <= ( v12_waybel_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['66','86'])).

thf('88',plain,
    ( ~ ( v12_waybel_0 @ sk_D @ sk_B )
   <= ~ ( v12_waybel_0 @ sk_D @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('89',plain,(
    sk_C = sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ~ ( v12_waybel_0 @ sk_C @ sk_B )
   <= ~ ( v12_waybel_0 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v12_waybel_0 @ sk_D @ sk_B )
    | ~ ( v12_waybel_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','5','58','59','91'])).


%------------------------------------------------------------------------------
