%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3aQheOHoln

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:13:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
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

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

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
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l1_waybel_0 @ X4 @ X5 )
      | ~ ( r1_waybel_0 @ X5 @ X4 @ X8 )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
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
    ! [X4: $i,X5: $i,X8: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l1_waybel_0 @ X4 @ X5 )
      | ~ ( r1_waybel_0 @ X5 @ X4 @ X8 )
      | ( m1_subset_1 @ ( sk_D @ X8 @ X4 @ X5 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
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
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( v7_waybel_0 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ( r1_orders_2 @ X12 @ X15 @ ( sk_D_1 @ X14 @ X15 @ X12 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
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
    ! [X4: $i,X5: $i,X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l1_waybel_0 @ X4 @ X5 )
      | ~ ( r1_waybel_0 @ X5 @ X4 @ X8 )
      | ~ ( r1_orders_2 @ X4 @ ( sk_D @ X8 @ X4 @ X5 ) @ X9 )
      | ( r2_hidden @ ( k2_waybel_0 @ X5 @ X4 @ X9 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
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
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( v7_waybel_0 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ( m1_subset_1 @ ( sk_D_1 @ X14 @ X15 @ X12 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
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
    ! [X12: $i,X14: $i,X15: $i] :
      ( ~ ( v7_waybel_0 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ( r1_orders_2 @ X12 @ X14 @ ( sk_D_1 @ X14 @ X15 @ X12 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
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
    ! [X4: $i,X5: $i,X8: $i,X9: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l1_waybel_0 @ X4 @ X5 )
      | ~ ( r1_waybel_0 @ X5 @ X4 @ X8 )
      | ~ ( r1_orders_2 @ X4 @ ( sk_D @ X8 @ X4 @ X5 ) @ X9 )
      | ( r2_hidden @ ( k2_waybel_0 @ X5 @ X4 @ X9 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
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
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
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
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3aQheOHoln
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:51:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 82 iterations in 0.087s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.54  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.20/0.54  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.54  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.20/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.54  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.54  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.20/0.54  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.54  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.54  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.54  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.54  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.20/0.54  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(t26_yellow_6, conjecture,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.54             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.54           ( ![C:$i,D:$i]:
% 0.20/0.54             ( ~( ( r1_waybel_0 @ A @ B @ C ) & ( r1_waybel_0 @ A @ B @ D ) & 
% 0.20/0.54                  ( r1_xboole_0 @ C @ D ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i]:
% 0.20/0.54        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.54          ( ![B:$i]:
% 0.20/0.54            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.20/0.54                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.54              ( ![C:$i,D:$i]:
% 0.20/0.54                ( ~( ( r1_waybel_0 @ A @ B @ C ) & 
% 0.20/0.54                     ( r1_waybel_0 @ A @ B @ D ) & ( r1_xboole_0 @ C @ D ) ) ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t26_yellow_6])).
% 0.20/0.54  thf('0', plain, ((r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d11_waybel_0, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.54           ( ![C:$i]:
% 0.20/0.54             ( ( r1_waybel_0 @ A @ B @ C ) <=>
% 0.20/0.54               ( ?[D:$i]:
% 0.20/0.54                 ( ( ![E:$i]:
% 0.20/0.54                     ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.54                       ( ( r1_orders_2 @ B @ D @ E ) =>
% 0.20/0.54                         ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) ) ) ) & 
% 0.20/0.54                   ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X4)
% 0.20/0.54          | ~ (l1_waybel_0 @ X4 @ X5)
% 0.20/0.54          | ~ (r1_waybel_0 @ X5 @ X4 @ X8)
% 0.20/0.54          | (m1_subset_1 @ (sk_D @ X8 @ X4 @ X5) @ (u1_struct_0 @ X4))
% 0.20/0.54          | ~ (l1_struct_0 @ X5)
% 0.20/0.54          | (v2_struct_0 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.54        | (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54           (u1_struct_0 @ sk_B_1))
% 0.20/0.54        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.20/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.54  thf('3', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('4', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54           (u1_struct_0 @ sk_B_1))
% 0.20/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['2', '3', '4'])).
% 0.20/0.54  thf('6', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_B_1)
% 0.20/0.54        | (m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54           (u1_struct_0 @ sk_B_1)))),
% 0.20/0.54      inference('clc', [status(thm)], ['5', '6'])).
% 0.20/0.54  thf('8', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('9', plain,
% 0.20/0.54      ((m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf('10', plain, ((r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C_2)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X8 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X4)
% 0.20/0.54          | ~ (l1_waybel_0 @ X4 @ X5)
% 0.20/0.54          | ~ (r1_waybel_0 @ X5 @ X4 @ X8)
% 0.20/0.54          | (m1_subset_1 @ (sk_D @ X8 @ X4 @ X5) @ (u1_struct_0 @ X4))
% 0.20/0.54          | ~ (l1_struct_0 @ X5)
% 0.20/0.54          | (v2_struct_0 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.54        | (m1_subset_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54           (u1_struct_0 @ sk_B_1))
% 0.20/0.54        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.20/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.54  thf('13', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('14', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | (m1_subset_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54           (u1_struct_0 @ sk_B_1))
% 0.20/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.54  thf('16', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_B_1)
% 0.20/0.54        | (m1_subset_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54           (u1_struct_0 @ sk_B_1)))),
% 0.20/0.54      inference('clc', [status(thm)], ['15', '16'])).
% 0.20/0.54  thf('18', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      ((m1_subset_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.54  thf(d5_yellow_6, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.54       ( ( v7_waybel_0 @ A ) <=>
% 0.20/0.54         ( ![B:$i]:
% 0.20/0.54           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54             ( ![C:$i]:
% 0.20/0.54               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.54                 ( ?[D:$i]:
% 0.20/0.54                   ( ( r1_orders_2 @ A @ C @ D ) & 
% 0.20/0.54                     ( r1_orders_2 @ A @ B @ D ) & 
% 0.20/0.54                     ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.20/0.54         (~ (v7_waybel_0 @ X12)
% 0.20/0.54          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.20/0.54          | (r1_orders_2 @ X12 @ X15 @ (sk_D_1 @ X14 @ X15 @ X12))
% 0.20/0.54          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X12))
% 0.20/0.54          | ~ (l1_orders_2 @ X12)
% 0.20/0.54          | (v2_struct_0 @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_yellow_6])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B_1)
% 0.20/0.54          | ~ (l1_orders_2 @ sk_B_1)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.54          | (r1_orders_2 @ sk_B_1 @ X0 @ 
% 0.20/0.54             (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ X0 @ sk_B_1))
% 0.20/0.54          | ~ (v7_waybel_0 @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.54  thf('22', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(dt_l1_waybel_0, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( l1_struct_0 @ A ) =>
% 0.20/0.54       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.20/0.54  thf('23', plain,
% 0.20/0.54      (![X10 : $i, X11 : $i]:
% 0.20/0.54         (~ (l1_waybel_0 @ X10 @ X11)
% 0.20/0.54          | (l1_orders_2 @ X10)
% 0.20/0.54          | ~ (l1_struct_0 @ X11))),
% 0.20/0.54      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.20/0.54  thf('24', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.54  thf('25', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('26', plain, ((l1_orders_2 @ sk_B_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.54  thf('27', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B_1)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.54          | (r1_orders_2 @ sk_B_1 @ X0 @ 
% 0.20/0.54             (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ X0 @ sk_B_1)))),
% 0.20/0.54      inference('demod', [status(thm)], ['21', '26', '27'])).
% 0.20/0.54  thf('29', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('30', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r1_orders_2 @ sk_B_1 @ X0 @ 
% 0.20/0.54           (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ X0 @ sk_B_1))
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.54      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.54  thf('31', plain,
% 0.20/0.54      ((r1_orders_2 @ sk_B_1 @ (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54        (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54         (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['9', '30'])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X4)
% 0.20/0.54          | ~ (l1_waybel_0 @ X4 @ X5)
% 0.20/0.54          | ~ (r1_waybel_0 @ X5 @ X4 @ X8)
% 0.20/0.54          | ~ (r1_orders_2 @ X4 @ (sk_D @ X8 @ X4 @ X5) @ X9)
% 0.20/0.54          | (r2_hidden @ (k2_waybel_0 @ X5 @ X4 @ X9) @ X8)
% 0.20/0.54          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X4))
% 0.20/0.54          | ~ (l1_struct_0 @ X5)
% 0.20/0.54          | (v2_struct_0 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.54        | ~ (m1_subset_1 @ 
% 0.20/0.54             (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54              (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_B_1) @ 
% 0.20/0.54             (u1_struct_0 @ sk_B_1))
% 0.20/0.54        | (r2_hidden @ 
% 0.20/0.54           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.54            (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54             (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_B_1)) @ 
% 0.20/0.54           sk_D_2)
% 0.20/0.54        | ~ (r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2)
% 0.20/0.54        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.20/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.54  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('35', plain,
% 0.20/0.54      ((m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      ((m1_subset_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.20/0.54         (~ (v7_waybel_0 @ X12)
% 0.20/0.54          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.20/0.54          | (m1_subset_1 @ (sk_D_1 @ X14 @ X15 @ X12) @ (u1_struct_0 @ X12))
% 0.20/0.54          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X12))
% 0.20/0.54          | ~ (l1_orders_2 @ X12)
% 0.20/0.54          | (v2_struct_0 @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_yellow_6])).
% 0.20/0.54  thf('38', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B_1)
% 0.20/0.54          | ~ (l1_orders_2 @ sk_B_1)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.54          | (m1_subset_1 @ 
% 0.20/0.54             (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ X0 @ sk_B_1) @ 
% 0.20/0.54             (u1_struct_0 @ sk_B_1))
% 0.20/0.54          | ~ (v7_waybel_0 @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.54  thf('39', plain, ((l1_orders_2 @ sk_B_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.54  thf('40', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('41', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B_1)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.54          | (m1_subset_1 @ 
% 0.20/0.54             (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ X0 @ sk_B_1) @ 
% 0.20/0.54             (u1_struct_0 @ sk_B_1)))),
% 0.20/0.54      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.20/0.54  thf('42', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((m1_subset_1 @ 
% 0.20/0.54           (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ X0 @ sk_B_1) @ 
% 0.20/0.54           (u1_struct_0 @ sk_B_1))
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.54      inference('clc', [status(thm)], ['41', '42'])).
% 0.20/0.54  thf('44', plain,
% 0.20/0.54      ((m1_subset_1 @ 
% 0.20/0.54        (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54         (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_B_1) @ 
% 0.20/0.54        (u1_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['35', '43'])).
% 0.20/0.54  thf('45', plain, ((r1_waybel_0 @ sk_A @ sk_B_1 @ sk_D_2)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('46', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | (r2_hidden @ 
% 0.20/0.54           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.54            (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54             (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_B_1)) @ 
% 0.20/0.54           sk_D_2)
% 0.20/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['33', '34', '44', '45', '46'])).
% 0.20/0.54  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_B_1)
% 0.20/0.54        | (r2_hidden @ 
% 0.20/0.54           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.54            (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54             (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_B_1)) @ 
% 0.20/0.54           sk_D_2))),
% 0.20/0.54      inference('clc', [status(thm)], ['47', '48'])).
% 0.20/0.54  thf('50', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      ((r2_hidden @ 
% 0.20/0.54        (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.54         (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54          (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_B_1)) @ 
% 0.20/0.54        sk_D_2)),
% 0.20/0.54      inference('clc', [status(thm)], ['49', '50'])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      ((m1_subset_1 @ (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf('53', plain,
% 0.20/0.54      ((m1_subset_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ (u1_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('clc', [status(thm)], ['17', '18'])).
% 0.20/0.54  thf('54', plain,
% 0.20/0.54      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.20/0.54         (~ (v7_waybel_0 @ X12)
% 0.20/0.54          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.20/0.54          | (r1_orders_2 @ X12 @ X14 @ (sk_D_1 @ X14 @ X15 @ X12))
% 0.20/0.54          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X12))
% 0.20/0.54          | ~ (l1_orders_2 @ X12)
% 0.20/0.54          | (v2_struct_0 @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [d5_yellow_6])).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B_1)
% 0.20/0.54          | ~ (l1_orders_2 @ sk_B_1)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.54          | (r1_orders_2 @ sk_B_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54             (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ X0 @ sk_B_1))
% 0.20/0.54          | ~ (v7_waybel_0 @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.54  thf('56', plain, ((l1_orders_2 @ sk_B_1)),
% 0.20/0.54      inference('demod', [status(thm)], ['24', '25'])).
% 0.20/0.54  thf('57', plain, ((v7_waybel_0 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((v2_struct_0 @ sk_B_1)
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1))
% 0.20/0.54          | (r1_orders_2 @ sk_B_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54             (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ X0 @ sk_B_1)))),
% 0.20/0.54      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.20/0.54  thf('59', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('60', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((r1_orders_2 @ sk_B_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54           (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ X0 @ sk_B_1))
% 0.20/0.54          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_B_1)))),
% 0.20/0.54      inference('clc', [status(thm)], ['58', '59'])).
% 0.20/0.54  thf('61', plain,
% 0.20/0.54      ((r1_orders_2 @ sk_B_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54        (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54         (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['52', '60'])).
% 0.20/0.54  thf('62', plain,
% 0.20/0.54      (![X4 : $i, X5 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         ((v2_struct_0 @ X4)
% 0.20/0.54          | ~ (l1_waybel_0 @ X4 @ X5)
% 0.20/0.54          | ~ (r1_waybel_0 @ X5 @ X4 @ X8)
% 0.20/0.54          | ~ (r1_orders_2 @ X4 @ (sk_D @ X8 @ X4 @ X5) @ X9)
% 0.20/0.54          | (r2_hidden @ (k2_waybel_0 @ X5 @ X4 @ X9) @ X8)
% 0.20/0.54          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X4))
% 0.20/0.54          | ~ (l1_struct_0 @ X5)
% 0.20/0.54          | (v2_struct_0 @ X5))),
% 0.20/0.54      inference('cnf', [status(esa)], [d11_waybel_0])).
% 0.20/0.54  thf('63', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.54        | ~ (m1_subset_1 @ 
% 0.20/0.54             (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54              (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_B_1) @ 
% 0.20/0.54             (u1_struct_0 @ sk_B_1))
% 0.20/0.54        | (r2_hidden @ 
% 0.20/0.54           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.54            (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54             (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_B_1)) @ 
% 0.20/0.54           sk_C_2)
% 0.20/0.54        | ~ (r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C_2)
% 0.20/0.54        | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.20/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.54  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('65', plain,
% 0.20/0.54      ((m1_subset_1 @ 
% 0.20/0.54        (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54         (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_B_1) @ 
% 0.20/0.54        (u1_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['35', '43'])).
% 0.20/0.54  thf('66', plain, ((r1_waybel_0 @ sk_A @ sk_B_1 @ sk_C_2)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('67', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('68', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_A)
% 0.20/0.54        | (r2_hidden @ 
% 0.20/0.54           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.54            (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54             (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_B_1)) @ 
% 0.20/0.54           sk_C_2)
% 0.20/0.54        | (v2_struct_0 @ sk_B_1))),
% 0.20/0.54      inference('demod', [status(thm)], ['63', '64', '65', '66', '67'])).
% 0.20/0.54  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('70', plain,
% 0.20/0.54      (((v2_struct_0 @ sk_B_1)
% 0.20/0.54        | (r2_hidden @ 
% 0.20/0.54           (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.54            (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54             (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_B_1)) @ 
% 0.20/0.54           sk_C_2))),
% 0.20/0.54      inference('clc', [status(thm)], ['68', '69'])).
% 0.20/0.54  thf('71', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('72', plain,
% 0.20/0.54      ((r2_hidden @ 
% 0.20/0.54        (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.54         (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54          (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_B_1)) @ 
% 0.20/0.54        sk_C_2)),
% 0.20/0.54      inference('clc', [status(thm)], ['70', '71'])).
% 0.20/0.54  thf(t3_xboole_0, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.54            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.54  thf('73', plain,
% 0.20/0.54      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X2 @ X0)
% 0.20/0.54          | ~ (r2_hidden @ X2 @ X3)
% 0.20/0.54          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.54  thf('74', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         (~ (r1_xboole_0 @ sk_C_2 @ X0)
% 0.20/0.54          | ~ (r2_hidden @ 
% 0.20/0.54               (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.20/0.54                (sk_D_1 @ (sk_D @ sk_C_2 @ sk_B_1 @ sk_A) @ 
% 0.20/0.54                 (sk_D @ sk_D_2 @ sk_B_1 @ sk_A) @ sk_B_1)) @ 
% 0.20/0.54               X0))),
% 0.20/0.54      inference('sup-', [status(thm)], ['72', '73'])).
% 0.20/0.54  thf('75', plain, (~ (r1_xboole_0 @ sk_C_2 @ sk_D_2)),
% 0.20/0.54      inference('sup-', [status(thm)], ['51', '74'])).
% 0.20/0.54  thf('76', plain, ((r1_xboole_0 @ sk_C_2 @ sk_D_2)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('77', plain, ($false), inference('demod', [status(thm)], ['75', '76'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
