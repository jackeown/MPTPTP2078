%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT2043+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R0TRSus05M

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   71 (  92 expanded)
%              Number of leaves         :   33 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  384 ( 837 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(v3_lattice3_type,type,(
    v3_lattice3: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v25_waybel_0_type,type,(
    v25_waybel_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v24_waybel_0_type,type,(
    v24_waybel_0: $i > $o )).

thf(t2_yellow19,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
            & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
            & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) )
         => ! [C: $i] :
              ~ ( ( r2_hidden @ C @ B )
                & ( v1_xboole_0 @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ~ ( v1_xboole_0 @ B )
              & ( v1_subset_1 @ B @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) )
              & ( v2_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
              & ( v13_waybel_0 @ B @ ( k3_yellow_1 @ A ) )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ A ) ) ) ) )
           => ! [C: $i] :
                ~ ( ( r2_hidden @ C @ B )
                  & ( v1_xboole_0 @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_yellow19])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v1_xboole_0 @ B )
            & ( v2_waybel_0 @ B @ A )
            & ( v13_waybel_0 @ B @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
         => ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) )
          <=> ~ ( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( v2_waybel_0 @ X15 @ X16 )
      | ~ ( v13_waybel_0 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ~ ( v1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( r2_hidden @ ( k3_yellow_0 @ X16 ) @ X15 )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v1_yellow_0 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t8_waybel_7])).

thf('3',plain,
    ( ( v2_struct_0 @ ( k3_yellow_1 @ sk_A ) )
    | ~ ( v3_orders_2 @ ( k3_yellow_1 @ sk_A ) )
    | ~ ( v4_orders_2 @ ( k3_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k3_yellow_1 @ sk_A ) )
    | ~ ( v1_yellow_0 @ ( k3_yellow_1 @ sk_A ) )
    | ~ ( l1_orders_2 @ ( k3_yellow_1 @ sk_A ) )
    | ~ ( r2_hidden @ ( k3_yellow_0 @ ( k3_yellow_1 @ sk_A ) ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) )
    | ~ ( v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ~ ( v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(fc7_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k3_yellow_1 @ A ) )
      & ~ ( v2_struct_0 @ ( k3_yellow_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X6: $i] :
      ( v3_orders_2 @ ( k3_yellow_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('5',plain,(
    ! [X7: $i] :
      ( v4_orders_2 @ ( k3_yellow_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('6',plain,(
    ! [X8: $i] :
      ( v5_orders_2 @ ( k3_yellow_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('7',plain,(
    ! [X6: $i] :
      ( v3_orders_2 @ ( k3_yellow_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf(cc12_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v25_waybel_0 @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v1_yellow_0 @ A ) ) ) ) )).

thf('8',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v3_orders_2 @ X1 )
      | ~ ( v25_waybel_0 @ X1 )
      | ( v1_yellow_0 @ X1 )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc12_waybel_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ( v1_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v25_waybel_0 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(dt_k3_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k3_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k3_yellow_1 @ A ) ) ) )).

thf('10',plain,(
    ! [X3: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf('11',plain,(
    ! [X6: $i] :
      ( v3_orders_2 @ ( k3_yellow_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf(cc11_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v3_lattice3 @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v24_waybel_0 @ A )
          & ( v25_waybel_0 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v3_lattice3 @ X0 )
      | ( v25_waybel_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc11_waybel_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ ( k3_yellow_1 @ X0 ) )
      | ( v25_waybel_0 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v3_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X3: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v25_waybel_0 @ ( k3_yellow_1 @ X0 ) )
      | ~ ( v3_lattice3 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf(fc8_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v3_lattice3 @ ( k3_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k3_yellow_1 @ A ) ) ) )).

thf('16',plain,(
    ! [X10: $i] :
      ( v3_lattice3 @ ( k3_yellow_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc8_yellow_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v25_waybel_0 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X4: $i] :
      ~ ( v2_struct_0 @ ( k3_yellow_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( v25_waybel_0 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k3_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10','19'])).

thf('21',plain,(
    ! [X4: $i] :
      ~ ( v2_struct_0 @ ( k3_yellow_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( v1_yellow_0 @ ( k3_yellow_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X3: $i] :
      ( l1_orders_2 @ ( k3_yellow_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_1])).

thf(t18_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) )
      = k1_xboole_0 ) )).

thf('24',plain,(
    ! [X11: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ X11 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t18_yellow_1])).

thf('25',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_xboole_0 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('28',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ k1_xboole_0 @ sk_B ),
    inference(demod,[status(thm)],['25','28'])).

thf('30',plain,(
    v1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k3_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v13_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_waybel_0 @ sk_B @ ( k3_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ ( k3_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['3','4','5','6','22','23','24','29','30','31','32'])).

thf('34',plain,(
    ! [X4: $i] :
      ~ ( v2_struct_0 @ ( k3_yellow_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc7_yellow_1])).

thf('35',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['0','35'])).


%------------------------------------------------------------------------------
