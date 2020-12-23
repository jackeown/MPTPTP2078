%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1928+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ktfn9GkP1t

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:34 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 325 expanded)
%              Number of leaves         :   24 ( 105 expanded)
%              Depth                    :   17
%              Number of atoms          :  928 (5027 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t26_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i,D: $i] :
              ~ ( ( r1_waybel_0 @ A @ B @ C )
                & ( r1_waybel_0 @ A @ B @ D )
                & ( r1_xboole_0 @ C @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ! [C: $i,D: $i] :
                ~ ( ( r1_waybel_0 @ A @ B @ C )
                  & ( r1_waybel_0 @ A @ B @ D )
                  & ( r1_xboole_0 @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t26_yellow_6])).

thf('0',plain,(
    r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d11_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r1_waybel_0 @ A @ B @ C )
            <=> ? [D: $i] :
                  ( ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
                     => ( ( r1_orders_2 @ B @ D @ E )
                       => ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) )
                  & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( r1_waybel_0 @ X1 @ X0 @ X4 )
      | ( m1_subset_1 @ ( sk_D @ X4 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('2',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['2','3','4'])).

thf('6',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X4: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( r1_waybel_0 @ X1 @ X0 @ X4 )
      | ( m1_subset_1 @ ( sk_D @ X4 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('12',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(d5_yellow_6,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( v7_waybel_0 @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ? [D: $i] :
                    ( ( r1_orders_2 @ A @ C @ D )
                    & ( r1_orders_2 @ A @ B @ D )
                    & ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( v7_waybel_0 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ( r1_orders_2 @ X6 @ X9 @ ( sk_D_1 @ X8 @ X9 @ X6 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_6])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_orders_2 @ sk_B_1 @ X0 @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_waybel_0 @ X10 @ X11 )
      | ( l1_orders_2 @ X10 )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('24',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_orders_2 @ sk_B_1 @ X0 @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['21','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_B_1 @ X0 @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    r1_orders_2 @ sk_B_1 @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( r1_waybel_0 @ X1 @ X0 @ X4 )
      | ~ ( r1_orders_2 @ X0 @ ( sk_D @ X4 @ X0 @ X1 ) @ X5 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ X0 @ X5 ) @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) @ sk_D_2 )
    | ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('36',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('37',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( v7_waybel_0 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X8 @ X9 @ X6 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_6])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('40',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) @ sk_D_2 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['33','34','44','45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) @ sk_D_2 ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) @ sk_D_2 ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('53',plain,(
    m1_subset_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['17','18'])).

thf('54',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( v7_waybel_0 @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ( r1_orders_2 @ X6 @ X8 @ ( sk_D_1 @ X8 @ X9 @ X6 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_orders_2 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_yellow_6])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_orders_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_orders_2 @ sk_B_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 ) )
      | ~ ( v7_waybel_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_orders_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['24','25'])).

thf('57',plain,(
    v7_waybel_0 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) )
      | ( r1_orders_2 @ sk_B_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_B_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    r1_orders_2 @ sk_B_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X4: $i,X5: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ~ ( r1_waybel_0 @ X1 @ X0 @ X4 )
      | ~ ( r1_orders_2 @ X0 @ ( sk_D @ X4 @ X0 @ X1 ) @ X5 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ X0 @ X5 ) @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d11_waybel_0])).

thf('63',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) @ sk_C_2 )
    | ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C_2 )
    | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_B_1 ) @ ( u1_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('66',plain,(
    r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) @ sk_C_2 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['63','64','65','66','67'])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) @ sk_C_2 ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) @ sk_C_2 ),
    inference(clc,[status(thm)],['70','71'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('73',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X12 )
      | ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_xboole_0 @ X12 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C_2 @ X0 )
      | ~ ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_D_1 @ ( sk_D @ sk_C_2 @ sk_B_1 @ sk_A ) @ ( sk_D @ sk_D_2 @ sk_B_1 @ sk_A ) @ sk_B_1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( r1_xboole_0 @ sk_C_2 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['51','74'])).

thf('76',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['75','76'])).


%------------------------------------------------------------------------------
