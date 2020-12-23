%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AFu8899oOI

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:03 EST 2020

% Result     : Theorem 0.25s
% Output     : Refutation 0.25s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 270 expanded)
%              Number of leaves         :   36 ( 102 expanded)
%              Depth                    :   15
%              Number of atoms          : 1065 (2615 expanded)
%              Number of equality atoms :   25 (  90 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(t3_yellow_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
               => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
                <=> ( r1_tarski @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_yellow_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 )
   <= ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('4',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( r1_orders_2 @ X13 @ X12 @ X14 )
      | ~ ( r3_orders_2 @ X13 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X18: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X16: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,
    ( ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ sk_A )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_B @ sk_A ) )
   <= ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('17',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) )
   <= ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['11','14','17'])).

thf('19',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(d9_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r1_orders_2 @ X9 @ X8 @ X10 )
      | ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( u1_orders_2 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ ( u1_orders_2 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X16: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('23',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('24',plain,(
    ! [X23: $i] :
      ( ( u1_orders_2 @ ( k2_yellow_1 @ X23 ) )
      = ( k1_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ ( k1_yellow_1 @ X0 ) )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['21','22','23','24'])).

thf('26',plain,
    ( ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k1_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ sk_A ) )
   <= ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['12','13'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf('29',plain,
    ( ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k1_yellow_1 @ sk_A ) ) )
   <= ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A ) )
             => ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r1_tarski @ C @ D ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X3
       != ( k1_wellord2 @ X2 ) )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X5 @ X2 )
      | ( r1_tarski @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('31',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ ( k1_wellord2 @ X2 ) )
      | ( r1_tarski @ X4 @ X5 )
      | ~ ( r2_hidden @ X5 @ X2 )
      | ~ ( r2_hidden @ X4 @ X2 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf(redefinition_k1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k1_yellow_1 @ A )
      = ( k1_wellord2 @ A ) ) )).

thf('32',plain,(
    ! [X21: $i] :
      ( ( k1_yellow_1 @ X21 )
      = ( k1_wellord2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_yellow_1])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('33',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('34',plain,(
    ! [X21: $i] :
      ( ( k1_yellow_1 @ X21 )
      = ( k1_wellord2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_yellow_1])).

thf('35',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k1_yellow_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X21: $i] :
      ( ( k1_yellow_1 @ X21 )
      = ( k1_wellord2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_yellow_1])).

thf('37',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ ( k1_yellow_1 @ X2 ) )
      | ( r1_tarski @ X4 @ X5 )
      | ~ ( r2_hidden @ X5 @ X2 )
      | ~ ( r2_hidden @ X4 @ X2 ) ) ),
    inference(demod,[status(thm)],['31','32','35','36'])).

thf('38',plain,
    ( ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( r2_hidden @ sk_B @ sk_A )
      | ~ ( r2_hidden @ sk_C_1 @ sk_A )
      | ( r1_tarski @ sk_B @ sk_C_1 ) )
   <= ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['12','13'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r1_tarski @ sk_B @ sk_C_1 ) )
   <= ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['38','43','48'])).

thf('50',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc1_struct_0,axiom,(
    ! [A: $i] :
      ( ( ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('51',plain,(
    ! [X7: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ~ ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc1_struct_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X16: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('54',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('55',plain,(
    ! [X0: $i] :
      ( l1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,
    ( ( ( r1_tarski @ sk_B @ sk_C_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['49','56'])).

thf('58',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('61',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('63',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['41','42'])).

thf('64',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['2'])).

thf('65',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X3
       != ( k1_wellord2 @ X2 ) )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X5 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X3 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('66',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X2 ) )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ ( k1_wellord2 @ X2 ) )
      | ~ ( r2_hidden @ X5 @ X2 )
      | ~ ( r2_hidden @ X4 @ X2 ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X21: $i] :
      ( ( k1_yellow_1 @ X21 )
      = ( k1_wellord2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_yellow_1])).

thf('68',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k1_yellow_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('69',plain,(
    ! [X21: $i] :
      ( ( k1_yellow_1 @ X21 )
      = ( k1_wellord2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_yellow_1])).

thf('70',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ ( k1_yellow_1 @ X2 ) )
      | ~ ( r2_hidden @ X5 @ X2 )
      | ~ ( r2_hidden @ X4 @ X2 ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_B @ X0 )
        | ~ ( r2_hidden @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k1_yellow_1 @ X0 ) ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k1_yellow_1 @ sk_A ) )
      | ~ ( r2_hidden @ sk_C_1 @ sk_A ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['63','71'])).

thf('73',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(clc,[status(thm)],['46','47'])).

thf('74',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k1_yellow_1 @ sk_A ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X23: $i] :
      ( ( u1_orders_2 @ ( k2_yellow_1 @ X23 ) )
      = ( k1_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('76',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ ( u1_orders_2 @ X9 ) )
      | ( r1_orders_2 @ X9 @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k1_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X16: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('79',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('80',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k1_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ sk_A )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ sk_A ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['74','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf('84',plain,(
    m1_subset_1 @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['12','13'])).

thf('85',plain,
    ( ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('87',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( r3_orders_2 @ X13 @ X12 @ X14 )
      | ~ ( r1_orders_2 @ X13 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('90',plain,(
    ! [X18: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('91',plain,(
    ! [X16: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['88','89','90','91'])).

thf('93',plain,
    ( ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['85','92'])).

thf('94',plain,(
    m1_subset_1 @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['12','13'])).

thf('95',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['15','16'])).

thf('96',plain,
    ( ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 )
   <= ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('98',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
   <= ( ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 )
      & ( r1_tarski @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('100',plain,
    ( ( v1_xboole_0 @ sk_A )
   <= ( ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 )
      & ( r1_tarski @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','61','62','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AFu8899oOI
% 0.17/0.38  % Computer   : n003.cluster.edu
% 0.17/0.38  % Model      : x86_64 x86_64
% 0.17/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.38  % Memory     : 8042.1875MB
% 0.17/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.38  % CPULimit   : 60
% 0.17/0.38  % DateTime   : Tue Dec  1 13:30:57 EST 2020
% 0.17/0.38  % CPUTime    : 
% 0.17/0.38  % Running portfolio for 600 s
% 0.17/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.38  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.25/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.25/0.53  % Solved by: fo/fo7.sh
% 0.25/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.25/0.53  % done 55 iterations in 0.033s
% 0.25/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.25/0.53  % SZS output start Refutation
% 0.25/0.53  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.25/0.53  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.25/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.25/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.25/0.53  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.25/0.53  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.25/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.25/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.25/0.53  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.25/0.53  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.25/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.25/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.25/0.53  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.25/0.53  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.25/0.53  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.25/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.25/0.53  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.25/0.53  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.25/0.53  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.25/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.25/0.53  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.25/0.53  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.25/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.25/0.53  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.25/0.53  thf(t3_yellow_1, conjecture,
% 0.25/0.53    (![A:$i]:
% 0.25/0.53     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.25/0.53       ( ![B:$i]:
% 0.25/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.25/0.53           ( ![C:$i]:
% 0.25/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.25/0.53               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.25/0.53                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.25/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.25/0.53    (~( ![A:$i]:
% 0.25/0.53        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.25/0.53          ( ![B:$i]:
% 0.25/0.53            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.25/0.53              ( ![C:$i]:
% 0.25/0.53                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.25/0.53                  ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.25/0.53                    ( r1_tarski @ B @ C ) ) ) ) ) ) ) )),
% 0.25/0.53    inference('cnf.neg', [status(esa)], [t3_yellow_1])).
% 0.25/0.53  thf('0', plain,
% 0.25/0.53      ((~ (r1_tarski @ sk_B @ sk_C_1)
% 0.25/0.53        | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('1', plain,
% 0.25/0.53      (~ ((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.25/0.53       ~ ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1))),
% 0.25/0.53      inference('split', [status(esa)], ['0'])).
% 0.25/0.53  thf('2', plain,
% 0.25/0.53      (((r1_tarski @ sk_B @ sk_C_1)
% 0.25/0.53        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('3', plain,
% 0.25/0.53      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1))
% 0.25/0.53         <= (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('split', [status(esa)], ['2'])).
% 0.25/0.53  thf(t1_yellow_1, axiom,
% 0.25/0.53    (![A:$i]:
% 0.25/0.53     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.25/0.53       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.25/0.53  thf('4', plain, (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.25/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.25/0.53  thf(redefinition_r3_orders_2, axiom,
% 0.25/0.53    (![A:$i,B:$i,C:$i]:
% 0.25/0.53     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.25/0.53         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.25/0.53         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.25/0.53       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.25/0.53  thf('5', plain,
% 0.25/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.25/0.53         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.25/0.53          | ~ (l1_orders_2 @ X13)
% 0.25/0.53          | ~ (v3_orders_2 @ X13)
% 0.25/0.53          | (v2_struct_0 @ X13)
% 0.25/0.53          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.25/0.53          | (r1_orders_2 @ X13 @ X12 @ X14)
% 0.25/0.53          | ~ (r3_orders_2 @ X13 @ X12 @ X14))),
% 0.25/0.53      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.25/0.53  thf('6', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.53         (~ (m1_subset_1 @ X1 @ X0)
% 0.25/0.53          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.25/0.53          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.25/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.25/0.53          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.25/0.53          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.25/0.53          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.25/0.53  thf('7', plain, (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.25/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.25/0.53  thf(fc5_yellow_1, axiom,
% 0.25/0.53    (![A:$i]:
% 0.25/0.53     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.25/0.53       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.25/0.53       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.25/0.53       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.25/0.53  thf('8', plain, (![X18 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X18))),
% 0.25/0.53      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.25/0.53  thf(dt_k2_yellow_1, axiom,
% 0.25/0.53    (![A:$i]:
% 0.25/0.53     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.25/0.53       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.25/0.53  thf('9', plain, (![X16 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X16))),
% 0.25/0.53      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.25/0.53  thf('10', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.53         (~ (m1_subset_1 @ X1 @ X0)
% 0.25/0.53          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.25/0.53          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.25/0.53          | ~ (m1_subset_1 @ X2 @ X0)
% 0.25/0.53          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.25/0.53      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 0.25/0.53  thf('11', plain,
% 0.25/0.53      ((((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.25/0.53         | ~ (m1_subset_1 @ sk_C_1 @ sk_A)
% 0.25/0.53         | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)
% 0.25/0.53         | ~ (m1_subset_1 @ sk_B @ sk_A)))
% 0.25/0.53         <= (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['3', '10'])).
% 0.25/0.53  thf('12', plain,
% 0.25/0.53      ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('13', plain,
% 0.25/0.53      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.25/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.25/0.53  thf('14', plain, ((m1_subset_1 @ sk_C_1 @ sk_A)),
% 0.25/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.25/0.53  thf('15', plain,
% 0.25/0.53      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('16', plain,
% 0.25/0.53      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.25/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.25/0.53  thf('17', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.25/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.25/0.53  thf('18', plain,
% 0.25/0.53      ((((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.25/0.53         | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)))
% 0.25/0.53         <= (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('demod', [status(thm)], ['11', '14', '17'])).
% 0.25/0.53  thf('19', plain,
% 0.25/0.53      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.25/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.25/0.53  thf(d9_orders_2, axiom,
% 0.25/0.53    (![A:$i]:
% 0.25/0.53     ( ( l1_orders_2 @ A ) =>
% 0.25/0.53       ( ![B:$i]:
% 0.25/0.53         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.25/0.53           ( ![C:$i]:
% 0.25/0.53             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.25/0.53               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.25/0.53                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.25/0.53  thf('20', plain,
% 0.25/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.25/0.53         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.25/0.53          | ~ (r1_orders_2 @ X9 @ X8 @ X10)
% 0.25/0.53          | (r2_hidden @ (k4_tarski @ X8 @ X10) @ (u1_orders_2 @ X9))
% 0.25/0.53          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.25/0.53          | ~ (l1_orders_2 @ X9))),
% 0.25/0.53      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.25/0.53  thf('21', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.53         (~ (m1_subset_1 @ X1 @ X0)
% 0.25/0.53          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.25/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.25/0.53          | (r2_hidden @ (k4_tarski @ X1 @ X2) @ 
% 0.25/0.53             (u1_orders_2 @ (k2_yellow_1 @ X0)))
% 0.25/0.53          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2))),
% 0.25/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.25/0.53  thf('22', plain, (![X16 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X16))),
% 0.25/0.53      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.25/0.53  thf('23', plain,
% 0.25/0.53      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.25/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.25/0.53  thf('24', plain,
% 0.25/0.53      (![X23 : $i]: ((u1_orders_2 @ (k2_yellow_1 @ X23)) = (k1_yellow_1 @ X23))),
% 0.25/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.25/0.53  thf('25', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.53         (~ (m1_subset_1 @ X1 @ X0)
% 0.25/0.53          | ~ (m1_subset_1 @ X2 @ X0)
% 0.25/0.53          | (r2_hidden @ (k4_tarski @ X1 @ X2) @ (k1_yellow_1 @ X0))
% 0.25/0.53          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2))),
% 0.25/0.53      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.25/0.53  thf('26', plain,
% 0.25/0.53      ((((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.25/0.53         | (r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (k1_yellow_1 @ sk_A))
% 0.25/0.53         | ~ (m1_subset_1 @ sk_C_1 @ sk_A)
% 0.25/0.53         | ~ (m1_subset_1 @ sk_B @ sk_A)))
% 0.25/0.53         <= (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['18', '25'])).
% 0.25/0.53  thf('27', plain, ((m1_subset_1 @ sk_C_1 @ sk_A)),
% 0.25/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.25/0.53  thf('28', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.25/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.25/0.53  thf('29', plain,
% 0.25/0.53      ((((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.25/0.53         | (r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (k1_yellow_1 @ sk_A))))
% 0.25/0.53         <= (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.25/0.53  thf(d1_wellord2, axiom,
% 0.25/0.53    (![A:$i,B:$i]:
% 0.25/0.53     ( ( v1_relat_1 @ B ) =>
% 0.25/0.53       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.25/0.53         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.25/0.53           ( ![C:$i,D:$i]:
% 0.25/0.53             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.25/0.53               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.25/0.53                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.25/0.53  thf('30', plain,
% 0.25/0.53      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.25/0.53         (((X3) != (k1_wellord2 @ X2))
% 0.25/0.53          | ~ (r2_hidden @ X4 @ X2)
% 0.25/0.53          | ~ (r2_hidden @ X5 @ X2)
% 0.25/0.53          | (r1_tarski @ X4 @ X5)
% 0.25/0.53          | ~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X3)
% 0.25/0.53          | ~ (v1_relat_1 @ X3))),
% 0.25/0.53      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.25/0.53  thf('31', plain,
% 0.25/0.53      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.25/0.53         (~ (v1_relat_1 @ (k1_wellord2 @ X2))
% 0.25/0.53          | ~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ (k1_wellord2 @ X2))
% 0.25/0.53          | (r1_tarski @ X4 @ X5)
% 0.25/0.53          | ~ (r2_hidden @ X5 @ X2)
% 0.25/0.53          | ~ (r2_hidden @ X4 @ X2))),
% 0.25/0.53      inference('simplify', [status(thm)], ['30'])).
% 0.25/0.53  thf(redefinition_k1_yellow_1, axiom,
% 0.25/0.53    (![A:$i]: ( ( k1_yellow_1 @ A ) = ( k1_wellord2 @ A ) ))).
% 0.25/0.53  thf('32', plain, (![X21 : $i]: ((k1_yellow_1 @ X21) = (k1_wellord2 @ X21))),
% 0.25/0.53      inference('cnf', [status(esa)], [redefinition_k1_yellow_1])).
% 0.25/0.53  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.25/0.53  thf('33', plain, (![X6 : $i]: (v1_relat_1 @ (k1_wellord2 @ X6))),
% 0.25/0.53      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.25/0.53  thf('34', plain, (![X21 : $i]: ((k1_yellow_1 @ X21) = (k1_wellord2 @ X21))),
% 0.25/0.53      inference('cnf', [status(esa)], [redefinition_k1_yellow_1])).
% 0.25/0.53  thf('35', plain, (![X6 : $i]: (v1_relat_1 @ (k1_yellow_1 @ X6))),
% 0.25/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.25/0.53  thf('36', plain, (![X21 : $i]: ((k1_yellow_1 @ X21) = (k1_wellord2 @ X21))),
% 0.25/0.53      inference('cnf', [status(esa)], [redefinition_k1_yellow_1])).
% 0.25/0.53  thf('37', plain,
% 0.25/0.53      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.25/0.53         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ (k1_yellow_1 @ X2))
% 0.25/0.53          | (r1_tarski @ X4 @ X5)
% 0.25/0.53          | ~ (r2_hidden @ X5 @ X2)
% 0.25/0.53          | ~ (r2_hidden @ X4 @ X2))),
% 0.25/0.53      inference('demod', [status(thm)], ['31', '32', '35', '36'])).
% 0.25/0.53  thf('38', plain,
% 0.25/0.53      ((((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.25/0.53         | ~ (r2_hidden @ sk_B @ sk_A)
% 0.25/0.53         | ~ (r2_hidden @ sk_C_1 @ sk_A)
% 0.25/0.53         | (r1_tarski @ sk_B @ sk_C_1)))
% 0.25/0.53         <= (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['29', '37'])).
% 0.25/0.53  thf('39', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.25/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.25/0.53  thf(t2_subset, axiom,
% 0.25/0.53    (![A:$i,B:$i]:
% 0.25/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.25/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.25/0.53  thf('40', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i]:
% 0.25/0.53         ((r2_hidden @ X0 @ X1)
% 0.25/0.53          | (v1_xboole_0 @ X1)
% 0.25/0.53          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.25/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.25/0.53  thf('41', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_B @ sk_A))),
% 0.25/0.53      inference('sup-', [status(thm)], ['39', '40'])).
% 0.25/0.53  thf('42', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('43', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.25/0.53      inference('clc', [status(thm)], ['41', '42'])).
% 0.25/0.53  thf('44', plain, ((m1_subset_1 @ sk_C_1 @ sk_A)),
% 0.25/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.25/0.53  thf('45', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i]:
% 0.25/0.53         ((r2_hidden @ X0 @ X1)
% 0.25/0.53          | (v1_xboole_0 @ X1)
% 0.25/0.53          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.25/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.25/0.53  thf('46', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C_1 @ sk_A))),
% 0.25/0.53      inference('sup-', [status(thm)], ['44', '45'])).
% 0.25/0.53  thf('47', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('48', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.25/0.53      inference('clc', [status(thm)], ['46', '47'])).
% 0.25/0.53  thf('49', plain,
% 0.25/0.53      ((((v2_struct_0 @ (k2_yellow_1 @ sk_A)) | (r1_tarski @ sk_B @ sk_C_1)))
% 0.25/0.53         <= (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('demod', [status(thm)], ['38', '43', '48'])).
% 0.25/0.53  thf('50', plain,
% 0.25/0.53      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.25/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.25/0.53  thf(fc1_struct_0, axiom,
% 0.25/0.53    (![A:$i]:
% 0.25/0.53     ( ( ( v2_struct_0 @ A ) & ( l1_struct_0 @ A ) ) =>
% 0.25/0.53       ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ))).
% 0.25/0.53  thf('51', plain,
% 0.25/0.53      (![X7 : $i]:
% 0.25/0.53         ((v1_xboole_0 @ (u1_struct_0 @ X7))
% 0.25/0.53          | ~ (l1_struct_0 @ X7)
% 0.25/0.53          | ~ (v2_struct_0 @ X7))),
% 0.25/0.53      inference('cnf', [status(esa)], [fc1_struct_0])).
% 0.25/0.53  thf('52', plain,
% 0.25/0.53      (![X0 : $i]:
% 0.25/0.53         ((v1_xboole_0 @ X0)
% 0.25/0.53          | ~ (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.25/0.53          | ~ (l1_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.25/0.53      inference('sup+', [status(thm)], ['50', '51'])).
% 0.25/0.53  thf('53', plain, (![X16 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X16))),
% 0.25/0.53      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.25/0.53  thf(dt_l1_orders_2, axiom,
% 0.25/0.53    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.25/0.53  thf('54', plain,
% 0.25/0.53      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_orders_2 @ X11))),
% 0.25/0.53      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.25/0.53  thf('55', plain, (![X0 : $i]: (l1_struct_0 @ (k2_yellow_1 @ X0))),
% 0.25/0.53      inference('sup-', [status(thm)], ['53', '54'])).
% 0.25/0.53  thf('56', plain,
% 0.25/0.53      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.25/0.53      inference('demod', [status(thm)], ['52', '55'])).
% 0.25/0.53  thf('57', plain,
% 0.25/0.53      ((((r1_tarski @ sk_B @ sk_C_1) | (v1_xboole_0 @ sk_A)))
% 0.25/0.53         <= (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['49', '56'])).
% 0.25/0.53  thf('58', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('59', plain,
% 0.25/0.53      (((r1_tarski @ sk_B @ sk_C_1))
% 0.25/0.53         <= (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('clc', [status(thm)], ['57', '58'])).
% 0.25/0.53  thf('60', plain,
% 0.25/0.53      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('split', [status(esa)], ['0'])).
% 0.25/0.53  thf('61', plain,
% 0.25/0.53      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.25/0.53       ~ ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1))),
% 0.25/0.53      inference('sup-', [status(thm)], ['59', '60'])).
% 0.25/0.53  thf('62', plain,
% 0.25/0.53      (((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.25/0.53       ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1))),
% 0.25/0.53      inference('split', [status(esa)], ['2'])).
% 0.25/0.53  thf('63', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.25/0.53      inference('clc', [status(thm)], ['41', '42'])).
% 0.25/0.53  thf('64', plain,
% 0.25/0.53      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('split', [status(esa)], ['2'])).
% 0.25/0.53  thf('65', plain,
% 0.25/0.53      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.25/0.53         (((X3) != (k1_wellord2 @ X2))
% 0.25/0.53          | ~ (r2_hidden @ X4 @ X2)
% 0.25/0.53          | ~ (r2_hidden @ X5 @ X2)
% 0.25/0.53          | (r2_hidden @ (k4_tarski @ X4 @ X5) @ X3)
% 0.25/0.53          | ~ (r1_tarski @ X4 @ X5)
% 0.25/0.53          | ~ (v1_relat_1 @ X3))),
% 0.25/0.53      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.25/0.53  thf('66', plain,
% 0.25/0.53      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.25/0.53         (~ (v1_relat_1 @ (k1_wellord2 @ X2))
% 0.25/0.53          | ~ (r1_tarski @ X4 @ X5)
% 0.25/0.53          | (r2_hidden @ (k4_tarski @ X4 @ X5) @ (k1_wellord2 @ X2))
% 0.25/0.53          | ~ (r2_hidden @ X5 @ X2)
% 0.25/0.53          | ~ (r2_hidden @ X4 @ X2))),
% 0.25/0.53      inference('simplify', [status(thm)], ['65'])).
% 0.25/0.53  thf('67', plain, (![X21 : $i]: ((k1_yellow_1 @ X21) = (k1_wellord2 @ X21))),
% 0.25/0.53      inference('cnf', [status(esa)], [redefinition_k1_yellow_1])).
% 0.25/0.53  thf('68', plain, (![X6 : $i]: (v1_relat_1 @ (k1_yellow_1 @ X6))),
% 0.25/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.25/0.53  thf('69', plain, (![X21 : $i]: ((k1_yellow_1 @ X21) = (k1_wellord2 @ X21))),
% 0.25/0.53      inference('cnf', [status(esa)], [redefinition_k1_yellow_1])).
% 0.25/0.53  thf('70', plain,
% 0.25/0.53      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.25/0.53         (~ (r1_tarski @ X4 @ X5)
% 0.25/0.53          | (r2_hidden @ (k4_tarski @ X4 @ X5) @ (k1_yellow_1 @ X2))
% 0.25/0.53          | ~ (r2_hidden @ X5 @ X2)
% 0.25/0.53          | ~ (r2_hidden @ X4 @ X2))),
% 0.25/0.53      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.25/0.53  thf('71', plain,
% 0.25/0.53      ((![X0 : $i]:
% 0.25/0.53          (~ (r2_hidden @ sk_B @ X0)
% 0.25/0.53           | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.25/0.53           | (r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (k1_yellow_1 @ X0))))
% 0.25/0.53         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['64', '70'])).
% 0.25/0.53  thf('72', plain,
% 0.25/0.53      ((((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (k1_yellow_1 @ sk_A))
% 0.25/0.53         | ~ (r2_hidden @ sk_C_1 @ sk_A))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['63', '71'])).
% 0.25/0.53  thf('73', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.25/0.53      inference('clc', [status(thm)], ['46', '47'])).
% 0.25/0.53  thf('74', plain,
% 0.25/0.53      (((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (k1_yellow_1 @ sk_A)))
% 0.25/0.53         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('demod', [status(thm)], ['72', '73'])).
% 0.25/0.53  thf('75', plain,
% 0.25/0.53      (![X23 : $i]: ((u1_orders_2 @ (k2_yellow_1 @ X23)) = (k1_yellow_1 @ X23))),
% 0.25/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.25/0.53  thf('76', plain,
% 0.25/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.25/0.53         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 0.25/0.53          | ~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ (u1_orders_2 @ X9))
% 0.25/0.53          | (r1_orders_2 @ X9 @ X8 @ X10)
% 0.25/0.53          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.25/0.53          | ~ (l1_orders_2 @ X9))),
% 0.25/0.53      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.25/0.53  thf('77', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.53         (~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k1_yellow_1 @ X0))
% 0.25/0.53          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.25/0.53          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.25/0.53          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.25/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0))))),
% 0.25/0.53      inference('sup-', [status(thm)], ['75', '76'])).
% 0.25/0.53  thf('78', plain, (![X16 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X16))),
% 0.25/0.53      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.25/0.53  thf('79', plain,
% 0.25/0.53      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.25/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.25/0.53  thf('80', plain,
% 0.25/0.53      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.25/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.25/0.53  thf('81', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.53         (~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k1_yellow_1 @ X0))
% 0.25/0.53          | ~ (m1_subset_1 @ X1 @ X0)
% 0.25/0.53          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.25/0.53          | ~ (m1_subset_1 @ X2 @ X0))),
% 0.25/0.53      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 0.25/0.53  thf('82', plain,
% 0.25/0.53      (((~ (m1_subset_1 @ sk_B @ sk_A)
% 0.25/0.53         | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)
% 0.25/0.53         | ~ (m1_subset_1 @ sk_C_1 @ sk_A))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['74', '81'])).
% 0.25/0.53  thf('83', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.25/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.25/0.53  thf('84', plain, ((m1_subset_1 @ sk_C_1 @ sk_A)),
% 0.25/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.25/0.53  thf('85', plain,
% 0.25/0.53      (((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1))
% 0.25/0.53         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.25/0.53  thf('86', plain,
% 0.25/0.53      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.25/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.25/0.53  thf('87', plain,
% 0.25/0.53      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.25/0.53         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.25/0.53          | ~ (l1_orders_2 @ X13)
% 0.25/0.53          | ~ (v3_orders_2 @ X13)
% 0.25/0.53          | (v2_struct_0 @ X13)
% 0.25/0.53          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.25/0.53          | (r3_orders_2 @ X13 @ X12 @ X14)
% 0.25/0.53          | ~ (r1_orders_2 @ X13 @ X12 @ X14))),
% 0.25/0.53      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.25/0.53  thf('88', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.53         (~ (m1_subset_1 @ X1 @ X0)
% 0.25/0.53          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.25/0.53          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.25/0.53          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.25/0.53          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.25/0.53          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.25/0.53          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['86', '87'])).
% 0.25/0.53  thf('89', plain,
% 0.25/0.53      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.25/0.53      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.25/0.53  thf('90', plain, (![X18 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X18))),
% 0.25/0.53      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.25/0.53  thf('91', plain, (![X16 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X16))),
% 0.25/0.53      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.25/0.53  thf('92', plain,
% 0.25/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.25/0.53         (~ (m1_subset_1 @ X1 @ X0)
% 0.25/0.53          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.25/0.53          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.25/0.53          | ~ (m1_subset_1 @ X2 @ X0)
% 0.25/0.53          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.25/0.53      inference('demod', [status(thm)], ['88', '89', '90', '91'])).
% 0.25/0.53  thf('93', plain,
% 0.25/0.53      ((((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.25/0.53         | ~ (m1_subset_1 @ sk_C_1 @ sk_A)
% 0.25/0.53         | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)
% 0.25/0.53         | ~ (m1_subset_1 @ sk_B @ sk_A))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['85', '92'])).
% 0.25/0.53  thf('94', plain, ((m1_subset_1 @ sk_C_1 @ sk_A)),
% 0.25/0.53      inference('demod', [status(thm)], ['12', '13'])).
% 0.25/0.53  thf('95', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.25/0.53      inference('demod', [status(thm)], ['15', '16'])).
% 0.25/0.53  thf('96', plain,
% 0.25/0.53      ((((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.25/0.53         | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)))
% 0.25/0.53         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.25/0.53  thf('97', plain,
% 0.25/0.53      ((~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1))
% 0.25/0.53         <= (~ ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('split', [status(esa)], ['0'])).
% 0.25/0.53  thf('98', plain,
% 0.25/0.53      (((v2_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.25/0.53         <= (~ ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)) & 
% 0.25/0.53             ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['96', '97'])).
% 0.25/0.53  thf('99', plain,
% 0.25/0.53      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.25/0.53      inference('demod', [status(thm)], ['52', '55'])).
% 0.25/0.53  thf('100', plain,
% 0.25/0.53      (((v1_xboole_0 @ sk_A))
% 0.25/0.53         <= (~ ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)) & 
% 0.25/0.53             ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.25/0.53      inference('sup-', [status(thm)], ['98', '99'])).
% 0.25/0.53  thf('101', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.25/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.25/0.53  thf('102', plain,
% 0.25/0.53      (~ ((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.25/0.53       ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1))),
% 0.25/0.53      inference('sup-', [status(thm)], ['100', '101'])).
% 0.25/0.53  thf('103', plain, ($false),
% 0.25/0.53      inference('sat_resolution*', [status(thm)], ['1', '61', '62', '102'])).
% 0.25/0.53  
% 0.25/0.53  % SZS output end Refutation
% 0.25/0.53  
% 0.25/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
