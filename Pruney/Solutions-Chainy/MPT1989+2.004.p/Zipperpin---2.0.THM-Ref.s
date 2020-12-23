%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l3AUILYTvR

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
% Statistics : Number of formulae       :  101 ( 233 expanded)
%              Number of leaves         :   29 (  84 expanded)
%              Depth                    :    9
%              Number of atoms          :  691 (3009 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   20 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_waybel_0_type,type,(
    k5_waybel_0: $i > $i > $i )).

thf(r1_yellow_0_type,type,(
    r1_yellow_0: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_waybel_0_type,type,(
    v1_waybel_0: $i > $i > $o )).

thf(k1_yellow_0_type,type,(
    k1_yellow_0: $i > $i > $i )).

thf(v1_waybel_7_type,type,(
    v1_waybel_7: $i > $i > $o )).

thf(v4_waybel_7_type,type,(
    v4_waybel_7: $i > $i > $o )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(v5_waybel_6_type,type,(
    v5_waybel_6: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v12_waybel_0_type,type,(
    v12_waybel_0: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(t38_waybel_7,conjecture,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v5_waybel_6 @ B @ A )
           => ( v4_waybel_7 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( v1_lattice3 @ A )
          & ( v2_lattice3 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( v5_waybel_6 @ B @ A )
             => ( v4_waybel_7 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_waybel_7])).

thf('0',plain,(
    ~ ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k5_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( m1_subset_1 @ ( k5_waybel_0 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X1 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_waybel_0])).

thf('3',plain,
    ( ( m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_lattice3 @ X0 )
      | ~ ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('8',plain,
    ( ~ ( v2_struct_0 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['5','10'])).

thf(d6_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v4_waybel_7 @ B @ A )
          <=> ? [C: $i] :
                ( ( B
                  = ( k1_yellow_0 @ A @ C ) )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
                & ( v1_waybel_7 @ C @ A )
                & ( v12_waybel_0 @ C @ A )
                & ( v1_waybel_0 @ C @ A )
                & ~ ( v1_xboole_0 @ C ) ) ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( X9
       != ( k1_yellow_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( v1_waybel_7 @ X11 @ X10 )
      | ~ ( v12_waybel_0 @ X11 @ X10 )
      | ~ ( v1_waybel_0 @ X11 @ X10 )
      | ( v1_xboole_0 @ X11 )
      | ( v4_waybel_7 @ X9 @ X10 )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v2_lattice3 @ X10 )
      | ~ ( v1_lattice3 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d6_waybel_7])).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v3_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v1_lattice3 @ X10 )
      | ~ ( v2_lattice3 @ X10 )
      | ~ ( l1_orders_2 @ X10 )
      | ( v4_waybel_7 @ ( k1_yellow_0 @ X10 @ X11 ) @ X10 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( v1_waybel_0 @ X11 @ X10 )
      | ~ ( v12_waybel_0 @ X11 @ X10 )
      | ~ ( v1_waybel_7 @ X11 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ~ ( m1_subset_1 @ ( k1_yellow_0 @ X10 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,
    ( ~ ( m1_subset_1 @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) @ ( u1_struct_0 @ sk_A ) )
    | ~ ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ~ ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v4_waybel_7 @ ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) ) @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( r1_yellow_0 @ A @ ( k5_waybel_0 @ A @ B ) )
            & ( ( k1_yellow_0 @ A @ ( k5_waybel_0 @ A @ B ) )
              = B ) ) ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ( ( k1_yellow_0 @ X8 @ ( k5_waybel_0 @ X8 @ X7 ) )
        = X7 )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t34_waybel_0])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) )
      = sk_B ) ),
    inference(demod,[status(thm)],['17','18','19','20','21'])).

thf('23',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('24',plain,
    ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t37_waybel_7,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v5_waybel_6 @ B @ A )
           => ( v1_waybel_7 @ ( k5_waybel_0 @ A @ B ) @ A ) ) ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( v1_waybel_7 @ ( k5_waybel_0 @ X13 @ X12 ) @ X13 )
      | ~ ( v5_waybel_6 @ X12 @ X13 )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v2_lattice3 @ X13 )
      | ~ ( v1_lattice3 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t37_waybel_7])).

thf('28',plain,
    ( ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_lattice3 @ sk_A )
    | ~ ( v2_lattice3 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_waybel_6 @ sk_B @ sk_A )
    | ( v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v5_waybel_6 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_waybel_7 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['28','29','30','31','32','33','34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc12_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( v12_waybel_0 @ ( k5_waybel_0 @ A @ B ) @ A ) ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( l1_orders_2 @ X3 )
      | ~ ( v4_orders_2 @ X3 )
      | ( v2_struct_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X3 ) )
      | ( v12_waybel_0 @ ( k5_waybel_0 @ X3 @ X4 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc12_waybel_0])).

thf('39',plain,
    ( ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('44',plain,(
    v12_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc8_waybel_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) )
     => ( ~ ( v1_xboole_0 @ ( k5_waybel_0 @ A @ B ) )
        & ( v1_waybel_0 @ ( k5_waybel_0 @ A @ B ) @ A ) ) ) )).

thf('46',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( v1_waybel_0 @ ( k5_waybel_0 @ X5 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc8_waybel_0])).

thf('47',plain,
    ( ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('52',plain,(
    v1_waybel_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) @ sk_A ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_yellow_0 @ sk_A @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    = sk_B ),
    inference(clc,[status(thm)],['22','23'])).

thf('54',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v2_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v4_waybel_7 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['14','24','25','36','44','52','53','54','55','56','57','58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( l1_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( v1_xboole_0 @ ( k5_waybel_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[fc8_waybel_0])).

thf('63',plain,
    ( ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('68',plain,(
    ~ ( v1_xboole_0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    v4_waybel_7 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['60','68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['0','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l3AUILYTvR
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:22 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.48  % Solved by: fo/fo7.sh
% 0.20/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.48  % done 38 iterations in 0.022s
% 0.20/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.48  % SZS output start Refutation
% 0.20/0.48  thf(k5_waybel_0_type, type, k5_waybel_0: $i > $i > $i).
% 0.20/0.48  thf(r1_yellow_0_type, type, r1_yellow_0: $i > $i > $o).
% 0.20/0.48  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.48  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.48  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.48  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.48  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.48  thf(v1_waybel_0_type, type, v1_waybel_0: $i > $i > $o).
% 0.20/0.48  thf(k1_yellow_0_type, type, k1_yellow_0: $i > $i > $i).
% 0.20/0.48  thf(v1_waybel_7_type, type, v1_waybel_7: $i > $i > $o).
% 0.20/0.48  thf(v4_waybel_7_type, type, v4_waybel_7: $i > $i > $o).
% 0.20/0.48  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.20/0.48  thf(v5_waybel_6_type, type, v5_waybel_6: $i > $i > $o).
% 0.20/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.48  thf(v12_waybel_0_type, type, v12_waybel_0: $i > $i > $o).
% 0.20/0.48  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.48  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.20/0.48  thf(t38_waybel_7, conjecture,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.20/0.48         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ( v5_waybel_6 @ B @ A ) => ( v4_waybel_7 @ B @ A ) ) ) ) ))).
% 0.20/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.48    (~( ![A:$i]:
% 0.20/0.48        ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.20/0.48            ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.48          ( ![B:$i]:
% 0.20/0.48            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48              ( ( v5_waybel_6 @ B @ A ) => ( v4_waybel_7 @ B @ A ) ) ) ) ) )),
% 0.20/0.48    inference('cnf.neg', [status(esa)], [t38_waybel_7])).
% 0.20/0.48  thf('0', plain, (~ (v4_waybel_7 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(dt_k5_waybel_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) & 
% 0.20/0.48         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48       ( m1_subset_1 @
% 0.20/0.48         ( k5_waybel_0 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.48  thf('2', plain,
% 0.20/0.48      (![X1 : $i, X2 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ X1)
% 0.20/0.48          | (v2_struct_0 @ X1)
% 0.20/0.48          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.20/0.48          | (m1_subset_1 @ (k5_waybel_0 @ X1 @ X2) @ 
% 0.20/0.48             (k1_zfmisc_1 @ (u1_struct_0 @ X1))))),
% 0.20/0.48      inference('cnf', [status(esa)], [dt_k5_waybel_0])).
% 0.20/0.48  thf('3', plain,
% 0.20/0.48      (((m1_subset_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.48  thf('4', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('5', plain,
% 0.20/0.48      (((m1_subset_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ 
% 0.20/0.48         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.48  thf('6', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(cc1_lattice3, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( l1_orders_2 @ A ) =>
% 0.20/0.48       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.20/0.48  thf('7', plain,
% 0.20/0.48      (![X0 : $i]:
% 0.20/0.48         (~ (v1_lattice3 @ X0) | ~ (v2_struct_0 @ X0) | ~ (l1_orders_2 @ X0))),
% 0.20/0.48      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.20/0.48  thf('8', plain, ((~ (v2_struct_0 @ sk_A) | ~ (v1_lattice3 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.48  thf('9', plain, ((v1_lattice3 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('10', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('11', plain,
% 0.20/0.48      ((m1_subset_1 @ (k5_waybel_0 @ sk_A @ sk_B) @ 
% 0.20/0.48        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.48      inference('clc', [status(thm)], ['5', '10'])).
% 0.20/0.48  thf(d6_waybel_7, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.20/0.48         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ( v4_waybel_7 @ B @ A ) <=>
% 0.20/0.48             ( ?[C:$i]:
% 0.20/0.48               ( ( ( B ) = ( k1_yellow_0 @ A @ C ) ) & 
% 0.20/0.48                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) & 
% 0.20/0.48                 ( v1_waybel_7 @ C @ A ) & ( v12_waybel_0 @ C @ A ) & 
% 0.20/0.48                 ( v1_waybel_0 @ C @ A ) & ( ~( v1_xboole_0 @ C ) ) ) ) ) ) ) ))).
% 0.20/0.48  thf('12', plain,
% 0.20/0.48      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.20/0.48          | ((X9) != (k1_yellow_0 @ X10 @ X11))
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.48          | ~ (v1_waybel_7 @ X11 @ X10)
% 0.20/0.48          | ~ (v12_waybel_0 @ X11 @ X10)
% 0.20/0.48          | ~ (v1_waybel_0 @ X11 @ X10)
% 0.20/0.48          | (v1_xboole_0 @ X11)
% 0.20/0.48          | (v4_waybel_7 @ X9 @ X10)
% 0.20/0.48          | ~ (l1_orders_2 @ X10)
% 0.20/0.48          | ~ (v2_lattice3 @ X10)
% 0.20/0.48          | ~ (v1_lattice3 @ X10)
% 0.20/0.48          | ~ (v5_orders_2 @ X10)
% 0.20/0.48          | ~ (v4_orders_2 @ X10)
% 0.20/0.48          | ~ (v3_orders_2 @ X10))),
% 0.20/0.48      inference('cnf', [status(esa)], [d6_waybel_7])).
% 0.20/0.48  thf('13', plain,
% 0.20/0.48      (![X10 : $i, X11 : $i]:
% 0.20/0.48         (~ (v3_orders_2 @ X10)
% 0.20/0.48          | ~ (v4_orders_2 @ X10)
% 0.20/0.48          | ~ (v5_orders_2 @ X10)
% 0.20/0.48          | ~ (v1_lattice3 @ X10)
% 0.20/0.48          | ~ (v2_lattice3 @ X10)
% 0.20/0.48          | ~ (l1_orders_2 @ X10)
% 0.20/0.48          | (v4_waybel_7 @ (k1_yellow_0 @ X10 @ X11) @ X10)
% 0.20/0.48          | (v1_xboole_0 @ X11)
% 0.20/0.48          | ~ (v1_waybel_0 @ X11 @ X10)
% 0.20/0.48          | ~ (v12_waybel_0 @ X11 @ X10)
% 0.20/0.48          | ~ (v1_waybel_7 @ X11 @ X10)
% 0.20/0.48          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.20/0.48          | ~ (m1_subset_1 @ (k1_yellow_0 @ X10 @ X11) @ (u1_struct_0 @ X10)))),
% 0.20/0.48      inference('simplify', [status(thm)], ['12'])).
% 0.20/0.48  thf('14', plain,
% 0.20/0.48      ((~ (m1_subset_1 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 0.20/0.48           (u1_struct_0 @ sk_A))
% 0.20/0.48        | ~ (v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.48        | ~ (v12_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.48        | ~ (v1_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.48        | (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.20/0.48        | (v4_waybel_7 @ (k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) @ 
% 0.20/0.48           sk_A)
% 0.20/0.48        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.48        | ~ (v2_lattice3 @ sk_A)
% 0.20/0.48        | ~ (v1_lattice3 @ sk_A)
% 0.20/0.48        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.48        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.48        | ~ (v3_orders_2 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['11', '13'])).
% 0.20/0.48  thf('15', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t34_waybel_0, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.48         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ( r1_yellow_0 @ A @ ( k5_waybel_0 @ A @ B ) ) & 
% 0.20/0.48             ( ( k1_yellow_0 @ A @ ( k5_waybel_0 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.20/0.48  thf('16', plain,
% 0.20/0.48      (![X7 : $i, X8 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.20/0.48          | ((k1_yellow_0 @ X8 @ (k5_waybel_0 @ X8 @ X7)) = (X7))
% 0.20/0.48          | ~ (l1_orders_2 @ X8)
% 0.20/0.48          | ~ (v5_orders_2 @ X8)
% 0.20/0.48          | ~ (v4_orders_2 @ X8)
% 0.20/0.48          | ~ (v3_orders_2 @ X8)
% 0.20/0.48          | (v2_struct_0 @ X8))),
% 0.20/0.48      inference('cnf', [status(esa)], [t34_waybel_0])).
% 0.20/0.48  thf('17', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.48        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.48        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.48        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.48        | ((k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) = (sk_B)))),
% 0.20/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.48  thf('18', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('19', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('20', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('21', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('22', plain,
% 0.20/0.48      (((v2_struct_0 @ sk_A)
% 0.20/0.48        | ((k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) = (sk_B)))),
% 0.20/0.48      inference('demod', [status(thm)], ['17', '18', '19', '20', '21'])).
% 0.20/0.48  thf('23', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('24', plain,
% 0.20/0.48      (((k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('25', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('26', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(t37_waybel_7, axiom,
% 0.20/0.48    (![A:$i]:
% 0.20/0.48     ( ( ( v3_orders_2 @ A ) & ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & 
% 0.20/0.48         ( v1_lattice3 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.48       ( ![B:$i]:
% 0.20/0.48         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.48           ( ( v5_waybel_6 @ B @ A ) =>
% 0.20/0.48             ( v1_waybel_7 @ ( k5_waybel_0 @ A @ B ) @ A ) ) ) ) ))).
% 0.20/0.48  thf('27', plain,
% 0.20/0.48      (![X12 : $i, X13 : $i]:
% 0.20/0.48         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.20/0.48          | (v1_waybel_7 @ (k5_waybel_0 @ X13 @ X12) @ X13)
% 0.20/0.48          | ~ (v5_waybel_6 @ X12 @ X13)
% 0.20/0.48          | ~ (l1_orders_2 @ X13)
% 0.20/0.48          | ~ (v2_lattice3 @ X13)
% 0.20/0.48          | ~ (v1_lattice3 @ X13)
% 0.20/0.48          | ~ (v5_orders_2 @ X13)
% 0.20/0.48          | ~ (v4_orders_2 @ X13)
% 0.20/0.48          | ~ (v3_orders_2 @ X13))),
% 0.20/0.48      inference('cnf', [status(esa)], [t37_waybel_7])).
% 0.20/0.48  thf('28', plain,
% 0.20/0.48      ((~ (v3_orders_2 @ sk_A)
% 0.20/0.48        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.48        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.48        | ~ (v1_lattice3 @ sk_A)
% 0.20/0.48        | ~ (v2_lattice3 @ sk_A)
% 0.20/0.48        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.48        | ~ (v5_waybel_6 @ sk_B @ sk_A)
% 0.20/0.48        | (v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.48  thf('29', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('30', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('31', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('32', plain, ((v1_lattice3 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('33', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('34', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('35', plain, ((v5_waybel_6 @ sk_B @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('36', plain, ((v1_waybel_7 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)],
% 0.20/0.48                ['28', '29', '30', '31', '32', '33', '34', '35'])).
% 0.20/0.48  thf('37', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(fc12_waybel_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_orders_2 @ A ) & 
% 0.20/0.48         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48       ( v12_waybel_0 @ ( k5_waybel_0 @ A @ B ) @ A ) ))).
% 0.20/0.48  thf('38', plain,
% 0.20/0.48      (![X3 : $i, X4 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ X3)
% 0.20/0.48          | ~ (v4_orders_2 @ X3)
% 0.20/0.48          | (v2_struct_0 @ X3)
% 0.20/0.48          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X3))
% 0.20/0.48          | (v12_waybel_0 @ (k5_waybel_0 @ X3 @ X4) @ X3))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc12_waybel_0])).
% 0.20/0.48  thf('39', plain,
% 0.20/0.48      (((v12_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.48        | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.48  thf('40', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('41', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('42', plain,
% 0.20/0.48      (((v12_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.48  thf('43', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('44', plain, ((v12_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['42', '43'])).
% 0.20/0.48  thf('45', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf(fc8_waybel_0, axiom,
% 0.20/0.48    (![A:$i,B:$i]:
% 0.20/0.48     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.48         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.48       ( ( ~( v1_xboole_0 @ ( k5_waybel_0 @ A @ B ) ) ) & 
% 0.20/0.48         ( v1_waybel_0 @ ( k5_waybel_0 @ A @ B ) @ A ) ) ))).
% 0.20/0.48  thf('46', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ X5)
% 0.20/0.48          | ~ (v3_orders_2 @ X5)
% 0.20/0.48          | (v2_struct_0 @ X5)
% 0.20/0.48          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.20/0.48          | (v1_waybel_0 @ (k5_waybel_0 @ X5 @ X6) @ X5))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc8_waybel_0])).
% 0.20/0.48  thf('47', plain,
% 0.20/0.48      (((v1_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.48        | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.48  thf('48', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('49', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('50', plain,
% 0.20/0.48      (((v1_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)
% 0.20/0.48        | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.20/0.48  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('52', plain, ((v1_waybel_0 @ (k5_waybel_0 @ sk_A @ sk_B) @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['50', '51'])).
% 0.20/0.48  thf('53', plain,
% 0.20/0.48      (((k1_yellow_0 @ sk_A @ (k5_waybel_0 @ sk_A @ sk_B)) = (sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['22', '23'])).
% 0.20/0.48  thf('54', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('55', plain, ((v2_lattice3 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('56', plain, ((v1_lattice3 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('57', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('58', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('59', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('60', plain,
% 0.20/0.48      (((v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.20/0.48        | (v4_waybel_7 @ sk_B @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)],
% 0.20/0.48                ['14', '24', '25', '36', '44', '52', '53', '54', '55', '56', 
% 0.20/0.48                 '57', '58', '59'])).
% 0.20/0.48  thf('61', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('62', plain,
% 0.20/0.48      (![X5 : $i, X6 : $i]:
% 0.20/0.48         (~ (l1_orders_2 @ X5)
% 0.20/0.48          | ~ (v3_orders_2 @ X5)
% 0.20/0.48          | (v2_struct_0 @ X5)
% 0.20/0.48          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 0.20/0.48          | ~ (v1_xboole_0 @ (k5_waybel_0 @ X5 @ X6)))),
% 0.20/0.48      inference('cnf', [status(esa)], [fc8_waybel_0])).
% 0.20/0.48  thf('63', plain,
% 0.20/0.48      ((~ (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))
% 0.20/0.48        | (v2_struct_0 @ sk_A)
% 0.20/0.48        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.48        | ~ (l1_orders_2 @ sk_A))),
% 0.20/0.48      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.48  thf('64', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('65', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.48  thf('66', plain,
% 0.20/0.48      ((~ (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B)) | (v2_struct_0 @ sk_A))),
% 0.20/0.48      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.20/0.48  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.48      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.48  thf('68', plain, (~ (v1_xboole_0 @ (k5_waybel_0 @ sk_A @ sk_B))),
% 0.20/0.48      inference('clc', [status(thm)], ['66', '67'])).
% 0.20/0.48  thf('69', plain, ((v4_waybel_7 @ sk_B @ sk_A)),
% 0.20/0.48      inference('clc', [status(thm)], ['60', '68'])).
% 0.20/0.48  thf('70', plain, ($false), inference('demod', [status(thm)], ['0', '69'])).
% 0.20/0.48  
% 0.20/0.48  % SZS output end Refutation
% 0.20/0.48  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
