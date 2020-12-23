%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ry0P5B8dV5

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 221 expanded)
%              Number of leaves         :   27 (  73 expanded)
%              Depth                    :   15
%              Number of atoms          :  755 (3753 expanded)
%              Number of equality atoms :   22 (  46 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v13_waybel_0_type,type,(
    v13_waybel_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_yellow_0_type,type,(
    v1_yellow_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v2_waybel_0_type,type,(
    v2_waybel_0: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(t8_waybel_7,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
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
            <=> ~ ( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_waybel_7])).

thf('0',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X3 @ X4 ) @ X4 )
      | ( X4 = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('4',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t44_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v1_yellow_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ( r1_orders_2 @ X10 @ ( k3_yellow_0 @ X10 ) @ X9 )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v1_yellow_0 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t44_yellow_0])).

thf('6',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v1_yellow_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_yellow_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) )
    | ( ( u1_struct_0 @ sk_A )
      = sk_B ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( m1_subset_1 @ ( k3_yellow_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d20_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v13_waybel_0 @ B @ A )
          <=> ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( ( r2_hidden @ C @ B )
                        & ( r1_orders_2 @ A @ C @ D ) )
                     => ( r2_hidden @ D @ B ) ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( v13_waybel_0 @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( r2_hidden @ X13 @ X11 )
      | ~ ( r1_orders_2 @ X12 @ X14 @ X13 )
      | ~ ( r2_hidden @ X14 @ X11 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d20_waybel_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( v13_waybel_0 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v13_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 )
        | ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ! [X0: $i] :
        ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_hidden @ X0 @ sk_B )
        | ~ ( r1_orders_2 @ sk_A @ ( k3_yellow_0 @ sk_A ) @ X0 ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ~ ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['12','26'])).

thf('28',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('29',plain,
    ( ( ( r2_hidden @ ( sk_C @ sk_B @ ( u1_struct_0 @ sk_A ) ) @ sk_B )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( X4 = X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('31',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = sk_B )
      | ( ( u1_struct_0 @ sk_A )
        = sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( v1_subset_1 @ sk_B @ sk_B )
   <= ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      & ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['34','36'])).

thf('38',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(simplify,[status(thm)],['33'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_B ) )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('41',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_subset_1 @ X16 @ X15 )
      | ( X16 != X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('42',plain,(
    ! [X15: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( v1_subset_1 @ X15 @ X15 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ~ ( v1_subset_1 @ sk_B @ sk_B )
   <= ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['35'])).

thf('46',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X16 = X15 )
      | ( v1_subset_1 @ X16 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('48',plain,
    ( ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( sk_B
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(dt_k3_yellow_0,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('51',plain,(
    ! [X8: $i] :
      ( ( m1_subset_1 @ ( k3_yellow_0 @ X8 ) @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k3_yellow_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( k3_yellow_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,
    ( ( sk_B
      = ( u1_struct_0 @ sk_A ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('56',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
      | ( v1_xboole_0 @ sk_B ) )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
   <= ~ ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B ) ),
    inference(split,[status(esa)],['35'])).

thf('61',plain,
    ( ( r2_hidden @ ( k3_yellow_0 @ sk_A ) @ sk_B )
    | ( v1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','44','45','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Ry0P5B8dV5
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 109 iterations in 0.051s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.51  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.51  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(v13_waybel_0_type, type, v13_waybel_0: $i > $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.51  thf(v1_yellow_0_type, type, v1_yellow_0: $i > $o).
% 0.20/0.51  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.51  thf(v2_waybel_0_type, type, v2_waybel_0: $i > $i > $o).
% 0.20/0.51  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.51  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.20/0.51  thf(t8_waybel_7, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.51         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.20/0.51         ( l1_orders_2 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.20/0.51             ( v13_waybel_0 @ B @ A ) & 
% 0.20/0.51             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.51           ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.20/0.51             ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.51            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v1_yellow_0 @ A ) & 
% 0.20/0.51            ( l1_orders_2 @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( ( ~( v1_xboole_0 @ B ) ) & ( v2_waybel_0 @ B @ A ) & 
% 0.20/0.51                ( v13_waybel_0 @ B @ A ) & 
% 0.20/0.51                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.20/0.51              ( ( v1_subset_1 @ B @ ( u1_struct_0 @ A ) ) <=>
% 0.20/0.51                ( ~( r2_hidden @ ( k3_yellow_0 @ A ) @ B ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t8_waybel_7])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.20/0.51        | ~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.20/0.51       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t49_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 0.20/0.51         ( ( A ) = ( B ) ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (sk_C @ X3 @ X4) @ X4)
% 0.20/0.51          | ((X4) = (X3))
% 0.20/0.51          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.20/0.51        | (m1_subset_1 @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51           (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf(t44_yellow_0, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.20/0.51         ( v1_yellow_0 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51           ( r1_orders_2 @ A @ ( k3_yellow_0 @ A ) @ B ) ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X9 : $i, X10 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.20/0.51          | (r1_orders_2 @ X10 @ (k3_yellow_0 @ X10) @ X9)
% 0.20/0.51          | ~ (l1_orders_2 @ X10)
% 0.20/0.51          | ~ (v1_yellow_0 @ X10)
% 0.20/0.51          | ~ (v5_orders_2 @ X10)
% 0.20/0.51          | (v2_struct_0 @ X10))),
% 0.20/0.51      inference('cnf', [status(esa)], [t44_yellow_0])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.51        | ~ (v1_yellow_0 @ sk_A)
% 0.20/0.51        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.51        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.20/0.51           (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('7', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('8', plain, ((v1_yellow_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('9', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.20/0.51        | (v2_struct_0 @ sk_A)
% 0.20/0.51        | (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.20/0.51           (sk_C @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.20/0.51  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (((r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ 
% 0.20/0.51         (sk_C @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.20/0.51        | ((u1_struct_0 @ sk_A) = (sk_B)))),
% 0.20/0.51      inference('clc', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.20/0.51         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t4_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.51       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X5 @ X6)
% 0.20/0.51          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.51          | (m1_subset_1 @ X5 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (((m1_subset_1 @ (k3_yellow_0 @ sk_A) @ (u1_struct_0 @ sk_A)))
% 0.20/0.51         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['13', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(d20_waybel_0, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_orders_2 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.51           ( ( v13_waybel_0 @ B @ A ) <=>
% 0.20/0.51             ( ![C:$i]:
% 0.20/0.51               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51                 ( ![D:$i]:
% 0.20/0.51                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.51                     ( ( ( r2_hidden @ C @ B ) & ( r1_orders_2 @ A @ C @ D ) ) =>
% 0.20/0.51                       ( r2_hidden @ D @ B ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.20/0.51          | ~ (v13_waybel_0 @ X11 @ X12)
% 0.20/0.51          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 0.20/0.51          | (r2_hidden @ X13 @ X11)
% 0.20/0.51          | ~ (r1_orders_2 @ X12 @ X14 @ X13)
% 0.20/0.51          | ~ (r2_hidden @ X14 @ X11)
% 0.20/0.51          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.20/0.51          | ~ (l1_orders_2 @ X12))),
% 0.20/0.51      inference('cnf', [status(esa)], [d20_waybel_0])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (l1_orders_2 @ sk_A)
% 0.20/0.51          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.51          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.20/0.51          | (r2_hidden @ X1 @ sk_B)
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (v13_waybel_0 @ sk_B @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.51  thf('21', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('22', plain, ((v13_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51          | ~ (r2_hidden @ X0 @ sk_B)
% 0.20/0.51          | ~ (r1_orders_2 @ sk_A @ X0 @ X1)
% 0.20/0.51          | (r2_hidden @ X1 @ sk_B)
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51           | (r2_hidden @ X0 @ sk_B)
% 0.20/0.51           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)
% 0.20/0.51           | ~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))
% 0.20/0.51         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.20/0.51         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((![X0 : $i]:
% 0.20/0.51          (~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51           | (r2_hidden @ X0 @ sk_B)
% 0.20/0.51           | ~ (r1_orders_2 @ sk_A @ (k3_yellow_0 @ sk_A) @ X0)))
% 0.20/0.51         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (((((u1_struct_0 @ sk_A) = (sk_B))
% 0.20/0.51         | (r2_hidden @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.20/0.51         | ~ (m1_subset_1 @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51              (u1_struct_0 @ sk_A))))
% 0.20/0.51         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '26'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      ((((u1_struct_0 @ sk_A) = (sk_B))
% 0.20/0.51        | (m1_subset_1 @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ 
% 0.20/0.51           (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      ((((r2_hidden @ (sk_C @ sk_B @ (u1_struct_0 @ sk_A)) @ sk_B)
% 0.20/0.51         | ((u1_struct_0 @ sk_A) = (sk_B))))
% 0.20/0.51         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.20/0.51      inference('clc', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i]:
% 0.20/0.51         (~ (r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 0.20/0.51          | ((X4) = (X3))
% 0.20/0.51          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t49_subset_1])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (((((u1_struct_0 @ sk_A) = (sk_B))
% 0.20/0.51         | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.20/0.51         | ((u1_struct_0 @ sk_A) = (sk_B))))
% 0.20/0.51         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (((((u1_struct_0 @ sk_A) = (sk_B)) | ((u1_struct_0 @ sk_A) = (sk_B))))
% 0.20/0.51         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.20/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      ((((u1_struct_0 @ sk_A) = (sk_B)))
% 0.20/0.51         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.20/0.51        | (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.20/0.51         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('split', [status(esa)], ['35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (((v1_subset_1 @ sk_B @ sk_B))
% 0.20/0.51         <= (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))) & 
% 0.20/0.51             ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['34', '36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      ((((u1_struct_0 @ sk_A) = (sk_B)))
% 0.20/0.51         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['33'])).
% 0.20/0.51  thf('39', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_B)))
% 0.20/0.51         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf(d7_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i]:
% 0.20/0.51         (~ (v1_subset_1 @ X16 @ X15)
% 0.20/0.51          | ((X16) != (X15))
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (![X15 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X15))
% 0.20/0.51          | ~ (v1_subset_1 @ X15 @ X15))),
% 0.20/0.51      inference('simplify', [status(thm)], ['41'])).
% 0.20/0.51  thf('43', plain,
% 0.20/0.51      ((~ (v1_subset_1 @ sk_B @ sk_B))
% 0.20/0.51         <= (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['40', '42'])).
% 0.20/0.51  thf('44', plain,
% 0.20/0.51      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.20/0.51       ~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['37', '43'])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.20/0.51       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('split', [status(esa)], ['35'])).
% 0.20/0.51  thf('46', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('47', plain,
% 0.20/0.51      (![X15 : $i, X16 : $i]:
% 0.20/0.51         (((X16) = (X15))
% 0.20/0.51          | (v1_subset_1 @ X16 @ X15)
% 0.20/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X15)))),
% 0.20/0.51      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.20/0.51  thf('48', plain,
% 0.20/0.51      (((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.20/0.51        | ((sk_B) = (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      ((~ (v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))
% 0.20/0.51         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('split', [status(esa)], ['0'])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.20/0.51         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.51  thf(dt_k3_yellow_0, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( l1_orders_2 @ A ) =>
% 0.20/0.51       ( m1_subset_1 @ ( k3_yellow_0 @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 0.20/0.51  thf('51', plain,
% 0.20/0.51      (![X8 : $i]:
% 0.20/0.51         ((m1_subset_1 @ (k3_yellow_0 @ X8) @ (u1_struct_0 @ X8))
% 0.20/0.51          | ~ (l1_orders_2 @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k3_yellow_0])).
% 0.20/0.51  thf(d2_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.51       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.51         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.51  thf('52', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X0 @ X1)
% 0.20/0.51          | (r2_hidden @ X0 @ X1)
% 0.20/0.51          | (v1_xboole_0 @ X1))),
% 0.20/0.51      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.51  thf('53', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (l1_orders_2 @ X0)
% 0.20/0.51          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.20/0.51          | (r2_hidden @ (k3_yellow_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)
% 0.20/0.51         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.20/0.51         | ~ (l1_orders_2 @ sk_A)))
% 0.20/0.51         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('sup+', [status(thm)], ['50', '53'])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      ((((sk_B) = (u1_struct_0 @ sk_A)))
% 0.20/0.51         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.51  thf('56', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('57', plain,
% 0.20/0.51      ((((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B) | (v1_xboole_0 @ sk_B)))
% 0.20/0.51         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.20/0.51  thf('58', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.20/0.51         <= (~ ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))))),
% 0.20/0.51      inference('clc', [status(thm)], ['57', '58'])).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      ((~ (r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B))
% 0.20/0.51         <= (~ ((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)))),
% 0.20/0.51      inference('split', [status(esa)], ['35'])).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      (((r2_hidden @ (k3_yellow_0 @ sk_A) @ sk_B)) | 
% 0.20/0.51       ((v1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.51  thf('62', plain, ($false),
% 0.20/0.51      inference('sat_resolution*', [status(thm)], ['1', '44', '45', '61'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
