%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qrm0Ic9GcF

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 116 expanded)
%              Number of leaves         :   25 (  44 expanded)
%              Depth                    :   18
%              Number of atoms          :  727 (1447 expanded)
%              Number of equality atoms :   13 (  14 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k4_waybel_9_type,type,(
    k4_waybel_9: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(a_3_0_waybel_9_type,type,(
    a_3_0_waybel_9: $i > $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( l1_struct_0 @ X6 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf(t13_waybel_9,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
               => ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ ( u1_struct_0 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t13_waybel_9])).

thf('1',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fraenkel_a_3_0_waybel_9,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( l1_struct_0 @ B )
        & ~ ( v2_struct_0 @ C )
        & ( l1_waybel_0 @ C @ B )
        & ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) )
     => ( ( r2_hidden @ A @ ( a_3_0_waybel_9 @ B @ C @ D ) )
      <=> ? [E: $i] :
            ( ( r1_orders_2 @ C @ D @ E )
            & ( A = E )
            & ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) )).

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_waybel_0 @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ( X13
        = ( sk_E @ X12 @ X10 @ X13 ) )
      | ~ ( r2_hidden @ X13 @ ( a_3_0_waybel_9 @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_3_0_waybel_9])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) )
      | ( X1
        = ( sk_E @ sk_C_1 @ sk_B @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_waybel_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X1 )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( sk_C @ X1 @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) )
        = ( sk_E @ sk_C_1 @ sk_B @ ( sk_C @ X1 @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
        = ( sk_E @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
        = ( sk_E @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_waybel_0 @ X10 @ X11 )
      | ( v2_struct_0 @ X10 )
      | ~ ( l1_struct_0 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ( m1_subset_1 @ ( sk_E @ X12 @ X10 @ X13 ) @ ( u1_struct_0 @ X10 ) )
      | ~ ( r2_hidden @ X13 @ ( a_3_0_waybel_9 @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_3_0_waybel_9])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( a_3_0_waybel_9 @ X2 @ X1 @ X0 ) @ X3 )
      | ( m1_subset_1 @ ( sk_E @ X0 @ X1 @ ( sk_C @ X3 @ ( a_3_0_waybel_9 @ X2 @ X1 @ X0 ) ) ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( v2_struct_0 @ X2 )
      | ~ ( l1_struct_0 @ X2 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l1_waybel_0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_E @ sk_C_1 @ sk_B @ ( sk_C @ X1 @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_E @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_E @ sk_C_1 @ sk_B @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_B ) )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_B )
      | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ X0 )
      | ( v2_struct_0 @ sk_B )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
      | ( r2_hidden @ ( sk_C @ X0 @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B )
    | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
    | ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ~ ( r1_tarski @ ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_waybel_9,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) )
             => ( ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) )
                = ( a_3_0_waybel_9 @ A @ B @ C ) ) ) ) ) )).

thf('29',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v2_struct_0 @ X15 )
      | ~ ( l1_waybel_0 @ X15 @ X16 )
      | ( ( u1_struct_0 @ ( k4_waybel_9 @ X16 @ X15 @ X17 ) )
        = ( a_3_0_waybel_9 @ X16 @ X15 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_struct_0 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t12_waybel_9])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ ( k4_waybel_9 @ X0 @ sk_B @ sk_C_1 ) )
        = ( a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1 ) )
      | ~ ( l1_waybel_0 @ sk_B @ X0 )
      | ( v2_struct_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
      = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( u1_struct_0 @ ( k4_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) )
    = ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( r1_tarski @ ( a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1 ) @ ( u1_struct_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','37'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) )
    | ( v2_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','38'])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( v2_struct_0 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['41','42'])).

thf(d1_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( v2_struct_0 @ A )
      <=> ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('44',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X9 ) )
      | ( v2_struct_0 @ X9 )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d1_struct_0])).

thf('45',plain,
    ( ~ ( l1_struct_0 @ sk_B )
    | ( v2_struct_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ~ ( l1_struct_0 @ sk_B ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','47'])).

thf('49',plain,(
    l1_waybel_0 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_waybel_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ! [B: $i] :
          ( ( l1_waybel_0 @ B @ A )
         => ( l1_orders_2 @ B ) ) ) )).

thf('50',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_waybel_0 @ X7 @ X8 )
      | ( l1_orders_2 @ X7 )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_waybel_0])).

thf('51',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( l1_orders_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    l1_orders_2 @ sk_B ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['48','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qrm0Ic9GcF
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:21:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 41 iterations in 0.037s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.50  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.20/0.50  thf(k4_waybel_9_type, type, k4_waybel_9: $i > $i > $i > $i).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.50  thf(a_3_0_waybel_9_type, type, a_3_0_waybel_9: $i > $i > $i > $i).
% 0.20/0.50  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.20/0.50  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(dt_l1_orders_2, axiom,
% 0.20/0.50    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.50  thf('0', plain, (![X6 : $i]: ((l1_struct_0 @ X6) | ~ (l1_orders_2 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.20/0.50  thf(t13_waybel_9, conjecture,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.50               ( r1_tarski @
% 0.20/0.50                 ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ 
% 0.20/0.50                 ( u1_struct_0 @ B ) ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i]:
% 0.20/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.50          ( ![B:$i]:
% 0.20/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.50              ( ![C:$i]:
% 0.20/0.50                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.50                  ( r1_tarski @
% 0.20/0.50                    ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) @ 
% 0.20/0.50                    ( u1_struct_0 @ B ) ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t13_waybel_9])).
% 0.20/0.50  thf('1', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d3_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('3', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(fraenkel_a_3_0_waybel_9, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_struct_0 @ B ) & 
% 0.20/0.50         ( ~( v2_struct_0 @ C ) ) & ( l1_waybel_0 @ C @ B ) & 
% 0.20/0.50         ( m1_subset_1 @ D @ ( u1_struct_0 @ C ) ) ) =>
% 0.20/0.50       ( ( r2_hidden @ A @ ( a_3_0_waybel_9 @ B @ C @ D ) ) <=>
% 0.20/0.50         ( ?[E:$i]:
% 0.20/0.50           ( ( r1_orders_2 @ C @ D @ E ) & ( ( A ) = ( E ) ) & 
% 0.20/0.50             ( m1_subset_1 @ E @ ( u1_struct_0 @ C ) ) ) ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.50         (~ (l1_waybel_0 @ X10 @ X11)
% 0.20/0.50          | (v2_struct_0 @ X10)
% 0.20/0.50          | ~ (l1_struct_0 @ X11)
% 0.20/0.50          | (v2_struct_0 @ X11)
% 0.20/0.50          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.20/0.50          | ((X13) = (sk_E @ X12 @ X10 @ X13))
% 0.20/0.50          | ~ (r2_hidden @ X13 @ (a_3_0_waybel_9 @ X11 @ X10 @ X12)))),
% 0.20/0.50      inference('cnf', [status(esa)], [fraenkel_a_3_0_waybel_9])).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X1 @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1))
% 0.20/0.50          | ((X1) = (sk_E @ sk_C_1 @ sk_B @ X1))
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ~ (l1_struct_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_B)
% 0.20/0.50          | ~ (l1_waybel_0 @ sk_B @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r1_tarski @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1) @ X1)
% 0.20/0.50          | ~ (l1_waybel_0 @ sk_B @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_B)
% 0.20/0.50          | ~ (l1_struct_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | ((sk_C @ X1 @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1))
% 0.20/0.50              = (sk_E @ sk_C_1 @ sk_B @ 
% 0.20/0.50                 (sk_C @ X1 @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1)))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['2', '5'])).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.20/0.50            = (sk_E @ sk_C_1 @ sk_B @ 
% 0.20/0.50               (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))))
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_B)
% 0.20/0.50          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '6'])).
% 0.20/0.50  thf('8', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.20/0.50            = (sk_E @ sk_C_1 @ sk_B @ 
% 0.20/0.50               (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))))
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_B)
% 0.20/0.50          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.20/0.50      inference('demod', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('11', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.50         (~ (l1_waybel_0 @ X10 @ X11)
% 0.20/0.50          | (v2_struct_0 @ X10)
% 0.20/0.50          | ~ (l1_struct_0 @ X11)
% 0.20/0.50          | (v2_struct_0 @ X11)
% 0.20/0.50          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 0.20/0.50          | (m1_subset_1 @ (sk_E @ X12 @ X10 @ X13) @ (u1_struct_0 @ X10))
% 0.20/0.50          | ~ (r2_hidden @ X13 @ (a_3_0_waybel_9 @ X11 @ X10 @ X12)))),
% 0.20/0.50      inference('cnf', [status(esa)], [fraenkel_a_3_0_waybel_9])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ (a_3_0_waybel_9 @ X2 @ X1 @ X0) @ X3)
% 0.20/0.50          | (m1_subset_1 @ 
% 0.20/0.50             (sk_E @ X0 @ X1 @ (sk_C @ X3 @ (a_3_0_waybel_9 @ X2 @ X1 @ X0))) @ 
% 0.20/0.50             (u1_struct_0 @ X1))
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ X1))
% 0.20/0.50          | (v2_struct_0 @ X2)
% 0.20/0.50          | ~ (l1_struct_0 @ X2)
% 0.20/0.50          | (v2_struct_0 @ X1)
% 0.20/0.50          | ~ (l1_waybel_0 @ X1 @ X2))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (l1_waybel_0 @ sk_B @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_B)
% 0.20/0.50          | ~ (l1_struct_0 @ X0)
% 0.20/0.50          | (v2_struct_0 @ X0)
% 0.20/0.50          | (m1_subset_1 @ 
% 0.20/0.50             (sk_E @ sk_C_1 @ sk_B @ 
% 0.20/0.50              (sk_C @ X1 @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1))) @ 
% 0.20/0.50             (u1_struct_0 @ sk_B))
% 0.20/0.50          | (r1_tarski @ (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1) @ X1))),
% 0.20/0.50      inference('sup-', [status(thm)], ['11', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.20/0.50          | (m1_subset_1 @ 
% 0.20/0.50             (sk_E @ sk_C_1 @ sk_B @ 
% 0.20/0.50              (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.20/0.50             (u1_struct_0 @ sk_B))
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | ~ (l1_struct_0 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '15'])).
% 0.20/0.50  thf('17', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.20/0.50          | (m1_subset_1 @ 
% 0.20/0.50             (sk_E @ sk_C_1 @ sk_B @ 
% 0.20/0.50              (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))) @ 
% 0.20/0.50             (u1_struct_0 @ sk_B))
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((m1_subset_1 @ 
% 0.20/0.50           (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.20/0.50           (u1_struct_0 @ sk_B))
% 0.20/0.50          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_B)
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_B)
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0))),
% 0.20/0.50      inference('sup+', [status(thm)], ['9', '18'])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ sk_A)
% 0.20/0.50          | (v2_struct_0 @ sk_B)
% 0.20/0.50          | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.20/0.50          | (m1_subset_1 @ 
% 0.20/0.50             (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.20/0.50             (u1_struct_0 @ sk_B)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.50  thf(t2_subset, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ A @ B ) =>
% 0.20/0.50       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         ((r2_hidden @ X4 @ X5)
% 0.20/0.50          | (v1_xboole_0 @ X5)
% 0.20/0.50          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t2_subset])).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_B)
% 0.20/0.50          | (v2_struct_0 @ sk_A)
% 0.20/0.50          | (v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.50          | (r2_hidden @ 
% 0.20/0.50             (sk_C @ X0 @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.20/0.50             (u1_struct_0 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_B)
% 0.20/0.50        | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.20/0.50           (u1_struct_0 @ sk_B))
% 0.20/0.50        | (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.20/0.50           (u1_struct_0 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (((r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.20/0.50         (u1_struct_0 @ sk_B))
% 0.20/0.50        | (v2_struct_0 @ sk_B)
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (~ (r1_tarski @ (u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1)) @ 
% 0.20/0.50          (u1_struct_0 @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('27', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('28', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t12_waybel_9, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.20/0.50           ( ![C:$i]:
% 0.20/0.50             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) =>
% 0.20/0.50               ( ( u1_struct_0 @ ( k4_waybel_9 @ A @ B @ C ) ) =
% 0.20/0.50                 ( a_3_0_waybel_9 @ A @ B @ C ) ) ) ) ) ) ))).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X15)
% 0.20/0.50          | ~ (l1_waybel_0 @ X15 @ X16)
% 0.20/0.50          | ((u1_struct_0 @ (k4_waybel_9 @ X16 @ X15 @ X17))
% 0.20/0.50              = (a_3_0_waybel_9 @ X16 @ X15 @ X17))
% 0.20/0.50          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.20/0.50          | ~ (l1_struct_0 @ X16)
% 0.20/0.50          | (v2_struct_0 @ X16))),
% 0.20/0.50      inference('cnf', [status(esa)], [t12_waybel_9])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((v2_struct_0 @ X0)
% 0.20/0.50          | ~ (l1_struct_0 @ X0)
% 0.20/0.50          | ((u1_struct_0 @ (k4_waybel_9 @ X0 @ sk_B @ sk_C_1))
% 0.20/0.50              = (a_3_0_waybel_9 @ X0 @ sk_B @ sk_C_1))
% 0.20/0.50          | ~ (l1_waybel_0 @ sk_B @ X0)
% 0.20/0.50          | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_B)
% 0.20/0.50        | ((u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.20/0.50            = (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.20/0.50        | ~ (l1_struct_0 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['27', '30'])).
% 0.20/0.50  thf('32', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_B)
% 0.20/0.50        | ((u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.20/0.50            = (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.20/0.50        | (v2_struct_0 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('34', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_A)
% 0.20/0.50        | ((u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.20/0.50            = (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1)))),
% 0.20/0.50      inference('clc', [status(thm)], ['33', '34'])).
% 0.20/0.50  thf('36', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (((u1_struct_0 @ (k4_waybel_9 @ sk_A @ sk_B @ sk_C_1))
% 0.20/0.50         = (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1))),
% 0.20/0.50      inference('clc', [status(thm)], ['35', '36'])).
% 0.20/0.50  thf('38', plain,
% 0.20/0.50      (~ (r1_tarski @ (a_3_0_waybel_9 @ sk_A @ sk_B @ sk_C_1) @ 
% 0.20/0.50          (u1_struct_0 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['26', '37'])).
% 0.20/0.50  thf('39', plain,
% 0.20/0.50      (((v1_xboole_0 @ (u1_struct_0 @ sk_B))
% 0.20/0.50        | (v2_struct_0 @ sk_A)
% 0.20/0.50        | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['25', '38'])).
% 0.20/0.50  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (((v2_struct_0 @ sk_B) | (v1_xboole_0 @ (u1_struct_0 @ sk_B)))),
% 0.20/0.50      inference('clc', [status(thm)], ['39', '40'])).
% 0.20/0.50  thf('42', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('43', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_B))),
% 0.20/0.50      inference('clc', [status(thm)], ['41', '42'])).
% 0.20/0.50  thf(d1_struct_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_struct_0 @ A ) =>
% 0.20/0.50       ( ( v2_struct_0 @ A ) <=> ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.20/0.50  thf('44', plain,
% 0.20/0.50      (![X9 : $i]:
% 0.20/0.50         (~ (v1_xboole_0 @ (u1_struct_0 @ X9))
% 0.20/0.50          | (v2_struct_0 @ X9)
% 0.20/0.50          | ~ (l1_struct_0 @ X9))),
% 0.20/0.50      inference('cnf', [status(esa)], [d1_struct_0])).
% 0.20/0.50  thf('45', plain, ((~ (l1_struct_0 @ sk_B) | (v2_struct_0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.50  thf('46', plain, (~ (v2_struct_0 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('47', plain, (~ (l1_struct_0 @ sk_B)),
% 0.20/0.50      inference('clc', [status(thm)], ['45', '46'])).
% 0.20/0.50  thf('48', plain, (~ (l1_orders_2 @ sk_B)),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '47'])).
% 0.20/0.50  thf('49', plain, ((l1_waybel_0 @ sk_B @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_l1_waybel_0, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( l1_struct_0 @ A ) =>
% 0.20/0.50       ( ![B:$i]: ( ( l1_waybel_0 @ B @ A ) => ( l1_orders_2 @ B ) ) ) ))).
% 0.20/0.50  thf('50', plain,
% 0.20/0.50      (![X7 : $i, X8 : $i]:
% 0.20/0.50         (~ (l1_waybel_0 @ X7 @ X8) | (l1_orders_2 @ X7) | ~ (l1_struct_0 @ X8))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_l1_waybel_0])).
% 0.20/0.50  thf('51', plain, ((~ (l1_struct_0 @ sk_A) | (l1_orders_2 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.50  thf('52', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('53', plain, ((l1_orders_2 @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['51', '52'])).
% 0.20/0.50  thf('54', plain, ($false), inference('demod', [status(thm)], ['48', '53'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
