%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KfGEFbo9xi

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 (  82 expanded)
%              Number of leaves         :   23 (  34 expanded)
%              Depth                    :   16
%              Number of atoms          :  620 (1002 expanded)
%              Number of equality atoms :   28 (  48 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_yellow_6_type,type,(
    k3_yellow_6: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(u1_waybel_0_type,type,(
    u1_waybel_0: $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(v6_waybel_0_type,type,(
    v6_waybel_0: $i > $i > $o )).

thf(k8_funcop_1_type,type,(
    k8_funcop_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ( l1_waybel_0 @ ( k3_yellow_6 @ X10 @ X9 @ X11 ) @ X9 ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ( v6_waybel_0 @ ( k3_yellow_6 @ X10 @ X9 @ X11 ) @ X9 ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( l1_struct_0 @ X5 )
      | ~ ( v6_waybel_0 @ X6 @ X5 )
      | ~ ( l1_waybel_0 @ X6 @ X5 )
      | ( X6
       != ( k3_yellow_6 @ X7 @ X5 @ X8 ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X6 ) @ ( u1_orders_2 @ X6 ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X7 ) @ ( u1_orders_2 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_yellow_6])).

thf('16',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( l1_orders_2 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X5 ) )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ ( k3_yellow_6 @ X7 @ X5 @ X8 ) ) @ ( u1_orders_2 @ ( k3_yellow_6 @ X7 @ X5 @ X8 ) ) )
        = ( g1_orders_2 @ ( u1_struct_0 @ X7 ) @ ( u1_orders_2 @ X7 ) ) )
      | ~ ( l1_waybel_0 @ ( k3_yellow_6 @ X7 @ X5 @ X8 ) @ X5 )
      | ~ ( v6_waybel_0 @ ( k3_yellow_6 @ X7 @ X5 @ X8 ) @ X5 )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
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

thf('27',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( ( g1_orders_2 @ X3 @ X4 )
       != ( g1_orders_2 @ X1 @ X2 ) )
      | ( X3 = X1 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X3 ) ) ) ) ),
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
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KfGEFbo9xi
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 21 iterations in 0.021s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(k3_yellow_6_type, type, k3_yellow_6: $i > $i > $i > $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.20/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.47  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.20/0.47  thf(u1_waybel_0_type, type, u1_waybel_0: $i > $i > $i).
% 0.20/0.47  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.20/0.47  thf(v6_waybel_0_type, type, v6_waybel_0: $i > $i > $o).
% 0.20/0.47  thf(k8_funcop_1_type, type, k8_funcop_1: $i > $i > $i > $i).
% 0.20/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.47  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.20/0.47  thf(t13_yellow_6, conjecture,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_orders_2 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.47               ( ( u1_struct_0 @ ( k3_yellow_6 @ A @ B @ C ) ) =
% 0.20/0.47                 ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]:
% 0.20/0.47        ( ( l1_orders_2 @ A ) =>
% 0.20/0.47          ( ![B:$i]:
% 0.20/0.47            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.20/0.47              ( ![C:$i]:
% 0.20/0.47                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.47                  ( ( u1_struct_0 @ ( k3_yellow_6 @ A @ B @ C ) ) =
% 0.20/0.47                    ( u1_struct_0 @ A ) ) ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t13_yellow_6])).
% 0.20/0.47  thf('0', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_k3_yellow_6, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( l1_orders_2 @ A ) & ( ~( v2_struct_0 @ B ) ) & 
% 0.20/0.47         ( l1_struct_0 @ B ) & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) ) =>
% 0.20/0.47       ( ( v6_waybel_0 @ ( k3_yellow_6 @ A @ B @ C ) @ B ) & 
% 0.20/0.47         ( l1_waybel_0 @ ( k3_yellow_6 @ A @ B @ C ) @ B ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.47         (~ (l1_struct_0 @ X9)
% 0.20/0.47          | (v2_struct_0 @ X9)
% 0.20/0.47          | ~ (l1_orders_2 @ X10)
% 0.20/0.47          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 0.20/0.47          | (l1_waybel_0 @ (k3_yellow_6 @ X10 @ X9 @ X11) @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k3_yellow_6])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((l1_waybel_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C) @ sk_B)
% 0.20/0.47          | ~ (l1_orders_2 @ X0)
% 0.20/0.47          | (v2_struct_0 @ sk_B)
% 0.20/0.47          | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf('3', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((l1_waybel_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C) @ sk_B)
% 0.20/0.47          | ~ (l1_orders_2 @ X0)
% 0.20/0.47          | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf('5', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (l1_orders_2 @ X0)
% 0.20/0.47          | (l1_waybel_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C) @ sk_B))),
% 0.20/0.47      inference('clc', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf('7', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.47         (~ (l1_struct_0 @ X9)
% 0.20/0.47          | (v2_struct_0 @ X9)
% 0.20/0.47          | ~ (l1_orders_2 @ X10)
% 0.20/0.47          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 0.20/0.47          | (v6_waybel_0 @ (k3_yellow_6 @ X10 @ X9 @ X11) @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k3_yellow_6])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v6_waybel_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C) @ sk_B)
% 0.20/0.47          | ~ (l1_orders_2 @ X0)
% 0.20/0.47          | (v2_struct_0 @ sk_B)
% 0.20/0.47          | ~ (l1_struct_0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf('10', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v6_waybel_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C) @ sk_B)
% 0.20/0.47          | ~ (l1_orders_2 @ X0)
% 0.20/0.47          | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (l1_orders_2 @ X0)
% 0.20/0.47          | (v6_waybel_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C) @ sk_B))),
% 0.20/0.47      inference('clc', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('14', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_B))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d7_yellow_6, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_orders_2 @ A ) =>
% 0.20/0.47       ( ![B:$i]:
% 0.20/0.47         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) ) =>
% 0.20/0.47           ( ![C:$i]:
% 0.20/0.47             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.47               ( ![D:$i]:
% 0.20/0.47                 ( ( ( v6_waybel_0 @ D @ B ) & ( l1_waybel_0 @ D @ B ) ) =>
% 0.20/0.47                   ( ( ( D ) = ( k3_yellow_6 @ A @ B @ C ) ) <=>
% 0.20/0.47                     ( ( ( g1_orders_2 @
% 0.20/0.47                           ( u1_struct_0 @ D ) @ ( u1_orders_2 @ D ) ) =
% 0.20/0.47                         ( g1_orders_2 @
% 0.20/0.47                           ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) & 
% 0.20/0.47                       ( r2_funct_2 @
% 0.20/0.47                         ( u1_struct_0 @ D ) @ ( u1_struct_0 @ B ) @ 
% 0.20/0.47                         ( u1_waybel_0 @ B @ D ) @ 
% 0.20/0.47                         ( k8_funcop_1 @
% 0.20/0.47                           ( u1_struct_0 @ B ) @ ( u1_struct_0 @ D ) @ C ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.47         ((v2_struct_0 @ X5)
% 0.20/0.47          | ~ (l1_struct_0 @ X5)
% 0.20/0.47          | ~ (v6_waybel_0 @ X6 @ X5)
% 0.20/0.47          | ~ (l1_waybel_0 @ X6 @ X5)
% 0.20/0.47          | ((X6) != (k3_yellow_6 @ X7 @ X5 @ X8))
% 0.20/0.47          | ((g1_orders_2 @ (u1_struct_0 @ X6) @ (u1_orders_2 @ X6))
% 0.20/0.47              = (g1_orders_2 @ (u1_struct_0 @ X7) @ (u1_orders_2 @ X7)))
% 0.20/0.47          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X5))
% 0.20/0.47          | ~ (l1_orders_2 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [d7_yellow_6])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.20/0.47         (~ (l1_orders_2 @ X7)
% 0.20/0.47          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X5))
% 0.20/0.47          | ((g1_orders_2 @ (u1_struct_0 @ (k3_yellow_6 @ X7 @ X5 @ X8)) @ 
% 0.20/0.47              (u1_orders_2 @ (k3_yellow_6 @ X7 @ X5 @ X8)))
% 0.20/0.47              = (g1_orders_2 @ (u1_struct_0 @ X7) @ (u1_orders_2 @ X7)))
% 0.20/0.47          | ~ (l1_waybel_0 @ (k3_yellow_6 @ X7 @ X5 @ X8) @ X5)
% 0.20/0.47          | ~ (v6_waybel_0 @ (k3_yellow_6 @ X7 @ X5 @ X8) @ X5)
% 0.20/0.47          | ~ (l1_struct_0 @ X5)
% 0.20/0.47          | (v2_struct_0 @ X5))),
% 0.20/0.47      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_B)
% 0.20/0.47          | ~ (l1_struct_0 @ sk_B)
% 0.20/0.47          | ~ (v6_waybel_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C) @ sk_B)
% 0.20/0.47          | ~ (l1_waybel_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C) @ sk_B)
% 0.20/0.47          | ((g1_orders_2 @ (u1_struct_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C)) @ 
% 0.20/0.47              (u1_orders_2 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C)))
% 0.20/0.47              = (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 0.20/0.47          | ~ (l1_orders_2 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['14', '16'])).
% 0.20/0.47  thf('18', plain, ((l1_struct_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_B)
% 0.20/0.47          | ~ (v6_waybel_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C) @ sk_B)
% 0.20/0.47          | ~ (l1_waybel_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C) @ sk_B)
% 0.20/0.47          | ((g1_orders_2 @ (u1_struct_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C)) @ 
% 0.20/0.47              (u1_orders_2 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C)))
% 0.20/0.47              = (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 0.20/0.47          | ~ (l1_orders_2 @ X0))),
% 0.20/0.47      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (l1_orders_2 @ X0)
% 0.20/0.47          | ~ (l1_orders_2 @ X0)
% 0.20/0.47          | ((g1_orders_2 @ (u1_struct_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C)) @ 
% 0.20/0.47              (u1_orders_2 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C)))
% 0.20/0.47              = (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 0.20/0.47          | ~ (l1_waybel_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C) @ sk_B)
% 0.20/0.47          | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['13', '19'])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_B)
% 0.20/0.47          | ~ (l1_waybel_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C) @ sk_B)
% 0.20/0.47          | ((g1_orders_2 @ (u1_struct_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C)) @ 
% 0.20/0.47              (u1_orders_2 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C)))
% 0.20/0.47              = (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 0.20/0.47          | ~ (l1_orders_2 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (l1_orders_2 @ X0)
% 0.20/0.47          | ~ (l1_orders_2 @ X0)
% 0.20/0.47          | ((g1_orders_2 @ (u1_struct_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C)) @ 
% 0.20/0.47              (u1_orders_2 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C)))
% 0.20/0.47              = (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 0.20/0.47          | (v2_struct_0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['6', '21'])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((v2_struct_0 @ sk_B)
% 0.20/0.47          | ((g1_orders_2 @ (u1_struct_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C)) @ 
% 0.20/0.47              (u1_orders_2 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C)))
% 0.20/0.47              = (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 0.20/0.47          | ~ (l1_orders_2 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.47  thf('24', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (l1_orders_2 @ X0)
% 0.20/0.47          | ((g1_orders_2 @ (u1_struct_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C)) @ 
% 0.20/0.47              (u1_orders_2 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C)))
% 0.20/0.47              = (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))))),
% 0.20/0.47      inference('clc', [status(thm)], ['23', '24'])).
% 0.20/0.47  thf(dt_u1_orders_2, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( l1_orders_2 @ A ) =>
% 0.20/0.47       ( m1_subset_1 @
% 0.20/0.47         ( u1_orders_2 @ A ) @ 
% 0.20/0.47         ( k1_zfmisc_1 @
% 0.20/0.47           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (u1_orders_2 @ X0) @ 
% 0.20/0.47           (k1_zfmisc_1 @ 
% 0.20/0.47            (k2_zfmisc_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))
% 0.20/0.47          | ~ (l1_orders_2 @ X0))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.20/0.47  thf(free_g1_orders_2, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.20/0.47       ( ![C:$i,D:$i]:
% 0.20/0.47         ( ( ( g1_orders_2 @ A @ B ) = ( g1_orders_2 @ C @ D ) ) =>
% 0.20/0.47           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         (((g1_orders_2 @ X3 @ X4) != (g1_orders_2 @ X1 @ X2))
% 0.20/0.47          | ((X3) = (X1))
% 0.20/0.47          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X3))))),
% 0.20/0.47      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (l1_orders_2 @ X0)
% 0.20/0.47          | ((u1_struct_0 @ X0) = (X1))
% 0.20/0.47          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.20/0.47              != (g1_orders_2 @ X1 @ X2)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((g1_orders_2 @ (u1_struct_0 @ X1) @ (u1_orders_2 @ X1))
% 0.20/0.47            != (g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0)))
% 0.20/0.47          | ~ (l1_orders_2 @ X0)
% 0.20/0.47          | ((u1_struct_0 @ X1)
% 0.20/0.47              = (u1_struct_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C)))
% 0.20/0.47          | ~ (l1_orders_2 @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['25', '28'])).
% 0.20/0.47  thf('30', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (~ (l1_orders_2 @ X0)
% 0.20/0.47          | ((u1_struct_0 @ X0)
% 0.20/0.47              = (u1_struct_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C)))
% 0.20/0.47          | ~ (l1_orders_2 @ X0))),
% 0.20/0.47      inference('eq_res', [status(thm)], ['29'])).
% 0.20/0.47  thf('31', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((u1_struct_0 @ X0)
% 0.20/0.47            = (u1_struct_0 @ (k3_yellow_6 @ X0 @ sk_B @ sk_C)))
% 0.20/0.47          | ~ (l1_orders_2 @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.47  thf('32', plain,
% 0.20/0.47      (((u1_struct_0 @ (k3_yellow_6 @ sk_A @ sk_B @ sk_C))
% 0.20/0.47         != (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('33', plain,
% 0.20/0.47      ((((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A)) | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.47  thf('34', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('35', plain, (((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.47  thf('36', plain, ($false), inference('simplify', [status(thm)], ['35'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
