%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1915+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hbAlIPWBi2

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:34 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   61 (  82 expanded)
%              Number of leaves         :   23 (  34 expanded)
%              Depth                    :   16
%              Number of atoms          :  620 (1002 expanded)
%              Number of equality atoms :   28 (  48 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k8_funcop_1_type,type,(
    k8_funcop_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_yellow_6_type,type,(
    k3_yellow_6: $i > $i > $i > $i )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(t13_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( ( u1_struct_0 @ ( k3_yellow_6 @ A @ B @ C ) )
                = ( u1_struct_0 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_orders_2 @ A )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_struct_0 @ B ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
               => ( ( u1_struct_0 @ ( k3_yellow_6 @ A @ B @ C ) )
                  = ( u1_struct_0 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_yellow_6])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k3_yellow_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_orders_2 @ A )
        & ~ ( v2_struct_0 @ B )
        & ( l1_struct_0 @ B )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) )
     => ( ( v6_waybel_0 @ ( k3_yellow_6 @ A @ B @ C ) @ B )
        & ( l1_waybel_0 @ ( k3_yellow_6 @ A @ B @ C ) @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ( l1_waybel_0 @ ( k3_yellow_6 @ X5 @ X4 @ X6 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_6])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) @ sk_B )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( l1_waybel_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) @ sk_B )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( l1_waybel_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ( v6_waybel_0 @ ( k3_yellow_6 @ X5 @ X4 @ X6 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_6])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v6_waybel_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) @ sk_B )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v6_waybel_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) @ sk_B )
      | ~ ( l1_orders_2 @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v6_waybel_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_yellow_6,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_struct_0 @ B ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ! [D: $i] :
                  ( ( ( v6_waybel_0 @ D @ B )
                    & ( l1_waybel_0 @ D @ B ) )
                 => ( ( D
                      = ( k3_yellow_6 @ A @ B @ C ) )
                  <=> ( ( ( g1_orders_2 @ ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) )
                        = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) )
                      & ( r2_funct_2 @ ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ ( u1_waybel_0 @ B @ D ) @ ( k8_funcop_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) @ C ) ) ) ) ) ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v6_waybel_0 @ X1 @ X0 )
      | ~ ( l1_waybel_0 @ X1 @ X0 )
      | ( X1
       != ( k3_yellow_6 @ X2 @ X0 @ X3 ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X1 ) @ ( u1_orders_2 @ X1 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X2 ) @ ( u1_orders_2 @ X2 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d7_yellow_6])).

thf('16',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( l1_orders_2 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X0 ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_yellow_6 @ X2 @ X0 @ X3 ) ) @ ( u1_orders_2 @ ( k3_yellow_6 @ X2 @ X0 @ X3 ) ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X2 ) @ ( u1_orders_2 @ X2 ) ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow_6 @ X2 @ X0 @ X3 ) @ X0 )
      | ~ ( v6_waybel_0 @ ( k3_yellow_6 @ X2 @ X0 @ X3 ) @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ sk_B )
      | ~ ( v6_waybel_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) @ sk_B )
      | ~ ( l1_waybel_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) @ sk_B )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    l1_struct_0 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( v6_waybel_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) @ sk_B )
      | ~ ( l1_waybel_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) @ sk_B )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) @ sk_B )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) @ sk_B )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) ) @ ( u1_orders_2 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X7 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X7 ) @ ( u1_struct_0 @ X7 ) ) ) )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( ( g1_orders_2 @ X10 @ X11 )
       != ( g1_orders_2 @ X8 @ X9 ) )
      | ( X10 = X8 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X1 ) @ ( u1_orders_2 @ X1 ) )
       != ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X1 )
        = ( u1_struct_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(eq_res,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( u1_struct_0 @ ( k3_yellow_6 @ X0 @ sk_B @ sk_C ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ( u1_struct_0 @ ( k3_yellow_6 @ sk_A @ sk_B @ sk_C ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ( u1_struct_0 @ sk_A )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(simplify,[status(thm)],['35'])).


%------------------------------------------------------------------------------
