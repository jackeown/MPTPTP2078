%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ilyaS7q4fV

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:14:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 167 expanded)
%              Number of leaves         :   32 (  64 expanded)
%              Depth                    :   23
%              Number of atoms          :  638 (1828 expanded)
%              Number of equality atoms :    5 (  10 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_waybel_0_type,type,(
    r2_waybel_0: $i > $i > $i > $o )).

thf(r1_waybel_0_type,type,(
    r1_waybel_0: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(l1_waybel_0_type,type,(
    l1_waybel_0: $i > $i > $o )).

thf(k2_waybel_0_type,type,(
    k2_waybel_0: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v7_waybel_0_type,type,(
    v7_waybel_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X6 @ X7 ) @ X7 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t29_yellow_6,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( v4_orders_2 @ B )
            & ( v7_waybel_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( ~ ( v2_struct_0 @ B )
              & ( v4_orders_2 @ B )
              & ( v7_waybel_0 @ B )
              & ( l1_waybel_0 @ B @ A ) )
           => ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_yellow_6])).

thf('4',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
            <=> ~ ( r1_waybel_0 @ A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X18 )
      | ( r1_waybel_0 @ X18 @ X17 @ ( k6_subset_1 @ ( u1_struct_0 @ X18 ) @ X19 ) )
      | ( r2_waybel_0 @ X18 @ X17 @ X19 )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t10_waybel_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k6_subset_1 @ X9 @ X10 )
      = ( k4_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( l1_waybel_0 @ X17 @ X18 )
      | ( r1_waybel_0 @ X18 @ X17 @ ( k4_xboole_0 @ ( u1_struct_0 @ X18 ) @ X19 ) )
      | ( r2_waybel_0 @ X18 @ X17 @ X19 )
      | ~ ( l1_struct_0 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    ~ ( r1_waybel_0 @ sk_A @ sk_B_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 )
    | ( v2_struct_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v2_struct_0 @ sk_B_1 )
    | ( r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0 ),
    inference(clc,[status(thm)],['15','16'])).

thf(t8_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i,D: $i] :
              ( ( r1_tarski @ C @ D )
             => ( ( ( r1_waybel_0 @ A @ B @ C )
                 => ( r1_waybel_0 @ A @ B @ D ) )
                & ( ( r2_waybel_0 @ A @ B @ C )
                 => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) ) )).

thf('18',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( v2_struct_0 @ X21 )
      | ~ ( l1_waybel_0 @ X21 @ X22 )
      | ~ ( r2_waybel_0 @ X22 @ X21 @ X23 )
      | ( r2_waybel_0 @ X22 @ X21 @ X24 )
      | ~ ( r1_tarski @ X23 @ X24 )
      | ~ ( l1_struct_0 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t8_waybel_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('21',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('22',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('24',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r2_waybel_0 @ sk_A @ sk_B_1 @ X0 ) ),
    inference(clc,[status(thm)],['25','26'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('29',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( sk_B @ X8 ) @ X8 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(d12_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( ~ ( v2_struct_0 @ B )
            & ( l1_waybel_0 @ B @ A ) )
         => ! [C: $i] :
              ( ( r2_waybel_0 @ A @ B @ C )
            <=> ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
                 => ? [E: $i] :
                      ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C )
                      & ( r1_orders_2 @ B @ D @ E )
                      & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X11: $i,X12: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( l1_waybel_0 @ X11 @ X12 )
      | ~ ( r2_waybel_0 @ X12 @ X11 @ X15 )
      | ( m1_subset_1 @ ( sk_E @ X16 @ X15 @ X11 @ X12 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ X0 ) ) @ X2 @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_waybel_0 @ X1 @ X0 @ X2 )
      | ~ ( l1_waybel_0 @ X0 @ X1 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ ( u1_struct_0 @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X11: $i,X12: $i,X15: $i,X16: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( l1_waybel_0 @ X11 @ X12 )
      | ~ ( r2_waybel_0 @ X12 @ X11 @ X15 )
      | ( r2_hidden @ ( k2_waybel_0 @ X12 @ X11 @ ( sk_E @ X16 @ X15 @ X11 @ X12 ) ) @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d12_waybel_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 )
      | ( r2_hidden @ ( k2_waybel_0 @ X1 @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X0 @ sk_B_1 @ sk_A ) @ X2 @ sk_B_1 @ X1 ) ) @ X2 )
      | ~ ( r2_waybel_0 @ X1 @ sk_B_1 @ X2 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ X1 )
      | ( v2_struct_0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ~ ( l1_waybel_0 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ~ ( l1_struct_0 @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','41'])).

thf('43',plain,(
    l1_waybel_0 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_B_1 )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['45','46'])).

thf('48',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k2_waybel_0 @ sk_A @ sk_B_1 @ ( sk_E @ ( sk_E @ ( sk_B @ ( u1_struct_0 @ sk_B_1 ) ) @ X1 @ sk_B_1 @ sk_A ) @ X0 @ sk_B_1 @ sk_A ) ) @ X0 ) ),
    inference(clc,[status(thm)],['47','48'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('50',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r1_xboole_0 @ X1 @ X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    $false ),
    inference('sup-',[status(thm)],['2','51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ilyaS7q4fV
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:15:26 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 41 iterations in 0.031s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(r2_waybel_0_type, type, r2_waybel_0: $i > $i > $i > $o).
% 0.22/0.50  thf(r1_waybel_0_type, type, r1_waybel_0: $i > $i > $i > $o).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.50  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.22/0.50  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.22/0.50  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.22/0.50  thf(l1_waybel_0_type, type, l1_waybel_0: $i > $i > $o).
% 0.22/0.50  thf(k2_waybel_0_type, type, k2_waybel_0: $i > $i > $i > $i).
% 0.22/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.50  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.22/0.50  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(v7_waybel_0_type, type, v7_waybel_0: $i > $o).
% 0.22/0.50  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.22/0.50  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.22/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.50  thf(t3_boole, axiom,
% 0.22/0.50    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.50  thf('0', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.50  thf(t79_xboole_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X6 @ X7) @ X7)),
% 0.22/0.50      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.22/0.50  thf('2', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.22/0.50      inference('sup+', [status(thm)], ['0', '1'])).
% 0.22/0.50  thf('3', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.22/0.50      inference('cnf', [status(esa)], [t3_boole])).
% 0.22/0.50  thf(t29_yellow_6, conjecture,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.22/0.50             ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.50           ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i]:
% 0.22/0.50        ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.50          ( ![B:$i]:
% 0.22/0.50            ( ( ( ~( v2_struct_0 @ B ) ) & ( v4_orders_2 @ B ) & 
% 0.22/0.50                ( v7_waybel_0 @ B ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.50              ( r1_waybel_0 @ A @ B @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t29_yellow_6])).
% 0.22/0.50  thf('4', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t10_waybel_0, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.22/0.50               ( ~( r1_waybel_0 @
% 0.22/0.50                    A @ B @ ( k6_subset_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X17)
% 0.22/0.50          | ~ (l1_waybel_0 @ X17 @ X18)
% 0.22/0.50          | (r1_waybel_0 @ X18 @ X17 @ 
% 0.22/0.50             (k6_subset_1 @ (u1_struct_0 @ X18) @ X19))
% 0.22/0.50          | (r2_waybel_0 @ X18 @ X17 @ X19)
% 0.22/0.50          | ~ (l1_struct_0 @ X18)
% 0.22/0.50          | (v2_struct_0 @ X18))),
% 0.22/0.50      inference('cnf', [status(esa)], [t10_waybel_0])).
% 0.22/0.50  thf(redefinition_k6_subset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X9 : $i, X10 : $i]:
% 0.22/0.50         ((k6_subset_1 @ X9 @ X10) = (k4_xboole_0 @ X9 @ X10))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X17)
% 0.22/0.50          | ~ (l1_waybel_0 @ X17 @ X18)
% 0.22/0.50          | (r1_waybel_0 @ X18 @ X17 @ 
% 0.22/0.50             (k4_xboole_0 @ (u1_struct_0 @ X18) @ X19))
% 0.22/0.50          | (r2_waybel_0 @ X18 @ X17 @ X19)
% 0.22/0.50          | ~ (l1_struct_0 @ X18)
% 0.22/0.50          | (v2_struct_0 @ X18))),
% 0.22/0.50      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.50  thf('8', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_A)
% 0.22/0.50          | ~ (l1_struct_0 @ sk_A)
% 0.22/0.50          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.50          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.50             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.22/0.50          | (v2_struct_0 @ sk_B_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '7'])).
% 0.22/0.50  thf('9', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_A)
% 0.22/0.50          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.50          | (r1_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.50             (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ X0))
% 0.22/0.50          | (v2_struct_0 @ sk_B_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      (((r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))
% 0.22/0.50        | (v2_struct_0 @ sk_B_1)
% 0.22/0.50        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.22/0.50        | (v2_struct_0 @ sk_A))),
% 0.22/0.50      inference('sup+', [status(thm)], ['3', '10'])).
% 0.22/0.50  thf('12', plain, (~ (r1_waybel_0 @ sk_A @ sk_B_1 @ (u1_struct_0 @ sk_A))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('13', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_A)
% 0.22/0.50        | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)
% 0.22/0.50        | (v2_struct_0 @ sk_B_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (((v2_struct_0 @ sk_B_1) | (r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0))),
% 0.22/0.50      inference('clc', [status(thm)], ['13', '14'])).
% 0.22/0.50  thf('16', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('17', plain, ((r2_waybel_0 @ sk_A @ sk_B_1 @ k1_xboole_0)),
% 0.22/0.50      inference('clc', [status(thm)], ['15', '16'])).
% 0.22/0.50  thf(t8_waybel_0, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.50           ( ![C:$i,D:$i]:
% 0.22/0.50             ( ( r1_tarski @ C @ D ) =>
% 0.22/0.50               ( ( ( r1_waybel_0 @ A @ B @ C ) => ( r1_waybel_0 @ A @ B @ D ) ) & 
% 0.22/0.50                 ( ( r2_waybel_0 @ A @ B @ C ) => ( r2_waybel_0 @ A @ B @ D ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X21)
% 0.22/0.50          | ~ (l1_waybel_0 @ X21 @ X22)
% 0.22/0.50          | ~ (r2_waybel_0 @ X22 @ X21 @ X23)
% 0.22/0.50          | (r2_waybel_0 @ X22 @ X21 @ X24)
% 0.22/0.50          | ~ (r1_tarski @ X23 @ X24)
% 0.22/0.50          | ~ (l1_struct_0 @ X22)
% 0.22/0.50          | (v2_struct_0 @ X22))),
% 0.22/0.50      inference('cnf', [status(esa)], [t8_waybel_0])).
% 0.22/0.50  thf('19', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_A)
% 0.22/0.50          | ~ (l1_struct_0 @ sk_A)
% 0.22/0.50          | ~ (r1_tarski @ k1_xboole_0 @ X0)
% 0.22/0.50          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.50          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.22/0.50          | (v2_struct_0 @ sk_B_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.50  thf('20', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.50  thf('21', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.22/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.50  thf('22', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('23', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_A)
% 0.22/0.50          | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)
% 0.22/0.50          | (v2_struct_0 @ sk_B_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.22/0.50  thf('24', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_B_1) | (r2_waybel_0 @ sk_A @ sk_B_1 @ X0))),
% 0.22/0.50      inference('clc', [status(thm)], ['23', '24'])).
% 0.22/0.50  thf('26', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('27', plain, (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)),
% 0.22/0.50      inference('clc', [status(thm)], ['25', '26'])).
% 0.22/0.50  thf('28', plain, (![X0 : $i]: (r2_waybel_0 @ sk_A @ sk_B_1 @ X0)),
% 0.22/0.50      inference('clc', [status(thm)], ['25', '26'])).
% 0.22/0.50  thf(existence_m1_subset_1, axiom,
% 0.22/0.50    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.22/0.50  thf('29', plain, (![X8 : $i]: (m1_subset_1 @ (sk_B @ X8) @ X8)),
% 0.22/0.50      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.22/0.50  thf(d12_waybel_0, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( ( ~( v2_struct_0 @ B ) ) & ( l1_waybel_0 @ B @ A ) ) =>
% 0.22/0.50           ( ![C:$i]:
% 0.22/0.50             ( ( r2_waybel_0 @ A @ B @ C ) <=>
% 0.22/0.50               ( ![D:$i]:
% 0.22/0.50                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) =>
% 0.22/0.50                   ( ?[E:$i]:
% 0.22/0.50                     ( ( r2_hidden @ ( k2_waybel_0 @ A @ B @ E ) @ C ) & 
% 0.22/0.50                       ( r1_orders_2 @ B @ D @ E ) & 
% 0.22/0.50                       ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i, X15 : $i, X16 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X11)
% 0.22/0.50          | ~ (l1_waybel_0 @ X11 @ X12)
% 0.22/0.50          | ~ (r2_waybel_0 @ X12 @ X11 @ X15)
% 0.22/0.50          | (m1_subset_1 @ (sk_E @ X16 @ X15 @ X11 @ X12) @ (u1_struct_0 @ X11))
% 0.22/0.50          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X11))
% 0.22/0.50          | ~ (l1_struct_0 @ X12)
% 0.22/0.50          | (v2_struct_0 @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X1)
% 0.22/0.50          | ~ (l1_struct_0 @ X1)
% 0.22/0.50          | (m1_subset_1 @ 
% 0.22/0.50             (sk_E @ (sk_B @ (u1_struct_0 @ X0)) @ X2 @ X0 @ X1) @ 
% 0.22/0.50             (u1_struct_0 @ X0))
% 0.22/0.50          | ~ (r2_waybel_0 @ X1 @ X0 @ X2)
% 0.22/0.50          | ~ (l1_waybel_0 @ X0 @ X1)
% 0.22/0.50          | (v2_struct_0 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_B_1)
% 0.22/0.50          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.22/0.50          | (m1_subset_1 @ 
% 0.22/0.50             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.22/0.50             (u1_struct_0 @ sk_B_1))
% 0.22/0.50          | ~ (l1_struct_0 @ sk_A)
% 0.22/0.50          | (v2_struct_0 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['28', '31'])).
% 0.22/0.50  thf('33', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('34', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('35', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_B_1)
% 0.22/0.50          | (m1_subset_1 @ 
% 0.22/0.50             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.22/0.50             (u1_struct_0 @ sk_B_1))
% 0.22/0.50          | (v2_struct_0 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.22/0.50  thf('36', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('37', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_A)
% 0.22/0.50          | (m1_subset_1 @ 
% 0.22/0.50             (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.22/0.50             (u1_struct_0 @ sk_B_1)))),
% 0.22/0.50      inference('clc', [status(thm)], ['35', '36'])).
% 0.22/0.50  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('39', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         (m1_subset_1 @ 
% 0.22/0.50          (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.22/0.50          (u1_struct_0 @ sk_B_1))),
% 0.22/0.50      inference('clc', [status(thm)], ['37', '38'])).
% 0.22/0.50  thf('40', plain,
% 0.22/0.50      (![X11 : $i, X12 : $i, X15 : $i, X16 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X11)
% 0.22/0.50          | ~ (l1_waybel_0 @ X11 @ X12)
% 0.22/0.50          | ~ (r2_waybel_0 @ X12 @ X11 @ X15)
% 0.22/0.50          | (r2_hidden @ 
% 0.22/0.50             (k2_waybel_0 @ X12 @ X11 @ (sk_E @ X16 @ X15 @ X11 @ X12)) @ X15)
% 0.22/0.50          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X11))
% 0.22/0.50          | ~ (l1_struct_0 @ X12)
% 0.22/0.50          | (v2_struct_0 @ X12))),
% 0.22/0.50      inference('cnf', [status(esa)], [d12_waybel_0])).
% 0.22/0.50  thf('41', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         ((v2_struct_0 @ X1)
% 0.22/0.50          | ~ (l1_struct_0 @ X1)
% 0.22/0.50          | (r2_hidden @ 
% 0.22/0.50             (k2_waybel_0 @ X1 @ sk_B_1 @ 
% 0.22/0.50              (sk_E @ 
% 0.22/0.50               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X0 @ sk_B_1 @ sk_A) @ 
% 0.22/0.50               X2 @ sk_B_1 @ X1)) @ 
% 0.22/0.50             X2)
% 0.22/0.50          | ~ (r2_waybel_0 @ X1 @ sk_B_1 @ X2)
% 0.22/0.50          | ~ (l1_waybel_0 @ sk_B_1 @ X1)
% 0.22/0.50          | (v2_struct_0 @ sk_B_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.22/0.50  thf('42', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_B_1)
% 0.22/0.50          | ~ (l1_waybel_0 @ sk_B_1 @ sk_A)
% 0.22/0.50          | (r2_hidden @ 
% 0.22/0.50             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.50              (sk_E @ 
% 0.22/0.50               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 0.22/0.50               X0 @ sk_B_1 @ sk_A)) @ 
% 0.22/0.50             X0)
% 0.22/0.50          | ~ (l1_struct_0 @ sk_A)
% 0.22/0.50          | (v2_struct_0 @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['27', '41'])).
% 0.22/0.50  thf('43', plain, ((l1_waybel_0 @ sk_B_1 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('44', plain, ((l1_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('45', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_B_1)
% 0.22/0.50          | (r2_hidden @ 
% 0.22/0.50             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.50              (sk_E @ 
% 0.22/0.50               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 0.22/0.50               X0 @ sk_B_1 @ sk_A)) @ 
% 0.22/0.50             X0)
% 0.22/0.50          | (v2_struct_0 @ sk_A))),
% 0.22/0.50      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.22/0.50  thf('46', plain, (~ (v2_struct_0 @ sk_B_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('47', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         ((v2_struct_0 @ sk_A)
% 0.22/0.50          | (r2_hidden @ 
% 0.22/0.50             (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.50              (sk_E @ 
% 0.22/0.50               (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 0.22/0.50               X0 @ sk_B_1 @ sk_A)) @ 
% 0.22/0.50             X0))),
% 0.22/0.50      inference('clc', [status(thm)], ['45', '46'])).
% 0.22/0.50  thf('48', plain, (~ (v2_struct_0 @ sk_A)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('49', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i]:
% 0.22/0.50         (r2_hidden @ 
% 0.22/0.50          (k2_waybel_0 @ sk_A @ sk_B_1 @ 
% 0.22/0.50           (sk_E @ 
% 0.22/0.50            (sk_E @ (sk_B @ (u1_struct_0 @ sk_B_1)) @ X1 @ sk_B_1 @ sk_A) @ 
% 0.22/0.50            X0 @ sk_B_1 @ sk_A)) @ 
% 0.22/0.50          X0)),
% 0.22/0.50      inference('clc', [status(thm)], ['47', '48'])).
% 0.22/0.50  thf(t4_xboole_0, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.50            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.50       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.50            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.50  thf('50', plain,
% 0.22/0.50      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.22/0.50          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.22/0.50      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.50  thf('51', plain, (![X0 : $i, X1 : $i]: ~ (r1_xboole_0 @ X1 @ X0)),
% 0.22/0.50      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.50  thf('52', plain, ($false), inference('sup-', [status(thm)], ['2', '51'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
