%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1627+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oBQkArjOuu

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:52 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 157 expanded)
%              Number of leaves         :   20 (  56 expanded)
%              Depth                    :   18
%              Number of atoms          :  560 (3580 expanded)
%              Number of equality atoms :   19 ( 163 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_yellow_0_type,type,(
    m1_yellow_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_yellow_0_type,type,(
    v4_yellow_0: $i > $i > $o )).

thf(v4_waybel_0_type,type,(
    v4_waybel_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_waybel_0_type,type,(
    v1_waybel_0: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t7_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_yellow_0 @ B @ A )
            & ( v4_waybel_0 @ B @ A )
            & ( m1_yellow_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( ( v1_waybel_0 @ C @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
             => ( ( r1_yellow_0 @ A @ C )
               => ( ( C = k1_xboole_0 )
                  | ( ( r1_yellow_0 @ B @ C )
                    & ( ( k1_yellow_0 @ B @ C )
                      = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v4_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_yellow_0 @ B @ A )
              & ( v4_waybel_0 @ B @ A )
              & ( m1_yellow_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( ( v1_waybel_0 @ C @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
               => ( ( r1_yellow_0 @ A @ C )
                 => ( ( C = k1_xboole_0 )
                    | ( ( r1_yellow_0 @ B @ C )
                      & ( ( k1_yellow_0 @ B @ C )
                        = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_waybel_0])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_yellow_0 @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_yellow_0 @ B @ A )
         => ( ( v4_waybel_0 @ B @ A )
          <=> ! [C: $i] :
                ( ( ( v1_waybel_0 @ C @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
               => ( ( r1_yellow_0 @ A @ C )
                 => ( ( C = k1_xboole_0 )
                    | ( r2_hidden @ ( k1_yellow_0 @ A @ C ) @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_yellow_0 @ X0 @ X1 )
      | ~ ( v4_waybel_0 @ X0 @ X1 )
      | ~ ( r1_yellow_0 @ X1 @ X2 )
      | ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( k1_yellow_0 @ X1 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( v1_waybel_0 @ X2 @ X0 )
      | ~ ( l1_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d4_waybel_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_waybel_0 @ sk_C_1 @ sk_B )
      | ( r2_hidden @ ( k1_yellow_0 @ X0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r1_yellow_0 @ X0 @ sk_C_1 )
      | ~ ( v4_waybel_0 @ sk_B @ X0 )
      | ~ ( m1_yellow_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_waybel_0 @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ ( k1_yellow_0 @ X0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ( sk_C_1 = k1_xboole_0 )
      | ~ ( r1_yellow_0 @ X0 @ sk_C_1 )
      | ~ ( v4_waybel_0 @ sk_B @ X0 )
      | ~ ( m1_yellow_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    sk_C_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ ( k1_yellow_0 @ X0 @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
      | ~ ( r1_yellow_0 @ X0 @ sk_C_1 )
      | ~ ( v4_waybel_0 @ sk_B @ X0 )
      | ~ ( m1_yellow_0 @ sk_B @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( m1_yellow_0 @ sk_B @ sk_A )
    | ~ ( v4_waybel_0 @ sk_B @ sk_A )
    | ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v4_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['13','14'])).

thf(t65_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_yellow_0 @ B @ A )
            & ( m1_yellow_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) )
             => ( ( ( r1_yellow_0 @ A @ C )
                  & ( r2_hidden @ ( k1_yellow_0 @ A @ C ) @ ( u1_struct_0 @ B ) ) )
               => ( ( r1_yellow_0 @ B @ C )
                  & ( ( k1_yellow_0 @ B @ C )
                    = ( k1_yellow_0 @ A @ C ) ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v4_yellow_0 @ X3 @ X4 )
      | ~ ( m1_yellow_0 @ X3 @ X4 )
      | ~ ( r1_yellow_0 @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k1_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X3 ) )
      | ( ( k1_yellow_0 @ X3 @ X5 )
        = ( k1_yellow_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t65_yellow_0])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( ( k1_yellow_0 @ sk_B @ sk_C_1 )
      = ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
    | ~ ( r1_yellow_0 @ sk_A @ sk_C_1 )
    | ~ ( m1_yellow_0 @ sk_B @ sk_A )
    | ~ ( v4_yellow_0 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    r1_yellow_0 @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v4_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_B @ sk_C_1 )
      = ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['17','18','19','20','21','22','23'])).

thf('25',plain,
    ( ~ ( r1_yellow_0 @ sk_B @ sk_C_1 )
    | ( ( k1_yellow_0 @ sk_B @ sk_C_1 )
     != ( k1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( ( k1_yellow_0 @ sk_B @ sk_C_1 )
     != ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
   <= ( ( k1_yellow_0 @ sk_B @ sk_C_1 )
     != ( k1_yellow_0 @ sk_A @ sk_C_1 ) ) ),
    inference(split,[status(esa)],['25'])).

thf('27',plain,(
    r2_hidden @ ( k1_yellow_0 @ sk_A @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('28',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v4_yellow_0 @ X3 @ X4 )
      | ~ ( m1_yellow_0 @ X3 @ X4 )
      | ~ ( r1_yellow_0 @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k1_yellow_0 @ X4 @ X5 ) @ ( u1_struct_0 @ X3 ) )
      | ( r1_yellow_0 @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X3 ) ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v4_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t65_yellow_0])).

thf('29',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) )
    | ( r1_yellow_0 @ sk_B @ sk_C_1 )
    | ~ ( r1_yellow_0 @ sk_A @ sk_C_1 )
    | ~ ( m1_yellow_0 @ sk_B @ sk_A )
    | ~ ( v4_yellow_0 @ sk_B @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r1_yellow_0 @ sk_A @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v4_yellow_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_yellow_0 @ sk_B @ sk_C_1 )
    | ( v2_struct_0 @ sk_B ) ),
    inference(demod,[status(thm)],['29','30','31','32','33','34','35'])).

thf('37',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( r1_yellow_0 @ sk_B @ sk_C_1 ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r1_yellow_0 @ sk_B @ sk_C_1 ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r1_yellow_0 @ sk_B @ sk_C_1 )
   <= ~ ( r1_yellow_0 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['25'])).

thf('42',plain,(
    r1_yellow_0 @ sk_B @ sk_C_1 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( k1_yellow_0 @ sk_B @ sk_C_1 )
     != ( k1_yellow_0 @ sk_A @ sk_C_1 ) )
    | ~ ( r1_yellow_0 @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['25'])).

thf('44',plain,(
    ( k1_yellow_0 @ sk_B @ sk_C_1 )
 != ( k1_yellow_0 @ sk_A @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['42','43'])).

thf('45',plain,(
    ( k1_yellow_0 @ sk_B @ sk_C_1 )
 != ( k1_yellow_0 @ sk_A @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['26','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['24','45'])).

thf('47',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v2_struct_0 @ sk_B ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['0','48'])).


%------------------------------------------------------------------------------
