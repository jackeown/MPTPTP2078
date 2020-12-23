%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3FmKezmDxS

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 368 expanded)
%              Number of leaves         :   34 ( 131 expanded)
%              Depth                    :   23
%              Number of atoms          : 1010 (3748 expanded)
%              Number of equality atoms :   24 ( 126 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 )
   <= ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['1'])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('3',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
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

thf('4',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( r1_orders_2 @ X11 @ X10 @ X12 )
      | ~ ( r3_orders_2 @ X11 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X16: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X14: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['5','6','7','8'])).

thf('10',plain,
    ( ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ sk_A )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_B @ sk_A ) )
   <= ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) )
   <= ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['10','13','16'])).

thf('18',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
    | ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['14','15'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( r1_tarski @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['1'])).

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

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X3
       != ( k1_wellord2 @ X2 ) )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X5 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X3 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('27',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X2 ) )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ ( k1_wellord2 @ X2 ) )
      | ~ ( r2_hidden @ X5 @ X2 )
      | ~ ( r2_hidden @ X4 @ X2 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(redefinition_k1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k1_yellow_1 @ A )
      = ( k1_wellord2 @ A ) ) )).

thf('28',plain,(
    ! [X20: $i] :
      ( ( k1_yellow_1 @ X20 )
      = ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_yellow_1])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('29',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('30',plain,(
    ! [X20: $i] :
      ( ( k1_yellow_1 @ X20 )
      = ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_yellow_1])).

thf('31',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k1_yellow_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X20: $i] :
      ( ( k1_yellow_1 @ X20 )
      = ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_yellow_1])).

thf('33',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ ( k1_yellow_1 @ X2 ) )
      | ~ ( r2_hidden @ X5 @ X2 )
      | ~ ( r2_hidden @ X4 @ X2 ) ) ),
    inference(demod,[status(thm)],['27','28','31','32'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ sk_B @ X0 )
        | ~ ( r2_hidden @ sk_C_1 @ X0 )
        | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k1_yellow_1 @ X0 ) ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,
    ( ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k1_yellow_1 @ sk_A ) )
      | ~ ( r2_hidden @ sk_C_1 @ sk_A ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k1_yellow_1 @ sk_A ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X22: $i] :
      ( ( u1_orders_2 @ ( k2_yellow_1 @ X22 ) )
      = ( k1_yellow_1 @ X22 ) ) ),
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

thf('43',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( u1_orders_2 @ X8 ) )
      | ( r1_orders_2 @ X8 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k1_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X14: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('46',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('47',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k1_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['44','45','46','47'])).

thf('49',plain,
    ( ( ~ ( m1_subset_1 @ sk_B @ sk_A )
      | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ sk_A ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['41','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['14','15'])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf('52',plain,
    ( ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('54',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( r3_orders_2 @ X11 @ X10 @ X12 )
      | ~ ( r1_orders_2 @ X11 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('57',plain,(
    ! [X16: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('58',plain,(
    ! [X14: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,
    ( ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_B @ sk_A ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['14','15'])).

thf('63',plain,
    ( ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) )
   <= ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 )
   <= ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['18'])).

thf('65',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
   <= ( ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 )
      & ( r1_tarski @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('66',plain,(
    ! [X19: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X19 ) )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_A )
   <= ( ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 )
      & ( r1_tarski @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 )
    | ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['1'])).

thf('71',plain,(
    r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['19','69','70'])).

thf('72',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['17','71'])).

thf('73',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('74',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_orders_2 @ X8 @ X7 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ X9 ) @ ( u1_orders_2 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d9_orders_2])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ ( u1_orders_2 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X14: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('77',plain,(
    ! [X21: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('78',plain,(
    ! [X22: $i] :
      ( ( u1_orders_2 @ ( k2_yellow_1 @ X22 ) )
      = ( k1_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ ( k1_yellow_1 @ X0 ) )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['75','76','77','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k1_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['72','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_C_1 @ sk_A ),
    inference(demod,[status(thm)],['11','12'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['14','15'])).

thf('83',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k1_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X3
       != ( k1_wellord2 @ X2 ) )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X5 @ X2 )
      | ( r1_tarski @ X4 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('85',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ ( k1_wellord2 @ X2 ) )
      | ( r1_tarski @ X4 @ X5 )
      | ~ ( r2_hidden @ X5 @ X2 )
      | ~ ( r2_hidden @ X4 @ X2 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X20: $i] :
      ( ( k1_yellow_1 @ X20 )
      = ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_yellow_1])).

thf('87',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( k1_yellow_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('88',plain,(
    ! [X20: $i] :
      ( ( k1_yellow_1 @ X20 )
      = ( k1_wellord2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_yellow_1])).

thf('89',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X5 ) @ ( k1_yellow_1 @ X2 ) )
      | ( r1_tarski @ X4 @ X5 )
      | ~ ( r2_hidden @ X5 @ X2 )
      | ~ ( r2_hidden @ X4 @ X2 ) ) ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( r2_hidden @ sk_B @ sk_A )
    | ~ ( r2_hidden @ sk_C_1 @ sk_A )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['83','89'])).

thf('91',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['22','23'])).

thf('92',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(clc,[status(thm)],['38','39'])).

thf('93',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_C_1 )
   <= ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['18'])).

thf('95',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['19','69'])).

thf('96',plain,(
    ~ ( r1_tarski @ sk_B @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['94','95'])).

thf('97',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference(clc,[status(thm)],['93','96'])).

thf('98',plain,(
    ! [X19: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X19 ) )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('99',plain,(
    v1_xboole_0 @ sk_A ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['0','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3FmKezmDxS
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:03:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.49  % Solved by: fo/fo7.sh
% 0.21/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.49  % done 56 iterations in 0.034s
% 0.21/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.49  % SZS output start Refutation
% 0.21/0.49  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.21/0.49  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.49  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.21/0.49  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.21/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.21/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.21/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.49  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.21/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.21/0.49  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.49  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.21/0.49  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.21/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.21/0.49  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.21/0.49  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.21/0.49  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.21/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.49  thf(t3_yellow_1, conjecture,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.21/0.49               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.21/0.49                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.21/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.49    (~( ![A:$i]:
% 0.21/0.49        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49          ( ![B:$i]:
% 0.21/0.49            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.21/0.49              ( ![C:$i]:
% 0.21/0.49                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.21/0.49                  ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.21/0.49                    ( r1_tarski @ B @ C ) ) ) ) ) ) ) )),
% 0.21/0.49    inference('cnf.neg', [status(esa)], [t3_yellow_1])).
% 0.21/0.49  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('1', plain,
% 0.21/0.49      (((r1_tarski @ sk_B @ sk_C_1)
% 0.21/0.49        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('2', plain,
% 0.21/0.49      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1))
% 0.21/0.49         <= (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['1'])).
% 0.21/0.49  thf(t1_yellow_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.21/0.49       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.49  thf('3', plain, (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.49  thf(redefinition_r3_orders_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i]:
% 0.21/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.21/0.49         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.21/0.49       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.21/0.49  thf('4', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.21/0.49          | ~ (l1_orders_2 @ X11)
% 0.21/0.49          | ~ (v3_orders_2 @ X11)
% 0.21/0.49          | (v2_struct_0 @ X11)
% 0.21/0.49          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.21/0.49          | (r1_orders_2 @ X11 @ X10 @ X12)
% 0.21/0.49          | ~ (r3_orders_2 @ X11 @ X10 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.21/0.49  thf('5', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.49          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.49          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.21/0.49          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.21/0.49          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.49          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.49  thf('6', plain, (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.49  thf(fc5_yellow_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.49       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.49       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.49       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.21/0.49  thf('7', plain, (![X16 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.21/0.49  thf(dt_k2_yellow_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.21/0.49       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.21/0.49  thf('8', plain, (![X14 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.49  thf('9', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.49          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.49          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ X0)
% 0.21/0.49          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['5', '6', '7', '8'])).
% 0.21/0.49  thf('10', plain,
% 0.21/0.49      ((((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.49         | ~ (m1_subset_1 @ sk_C_1 @ sk_A)
% 0.21/0.49         | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)
% 0.21/0.49         | ~ (m1_subset_1 @ sk_B @ sk_A)))
% 0.21/0.49         <= (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['2', '9'])).
% 0.21/0.49  thf('11', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('12', plain,
% 0.21/0.49      (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.49  thf('13', plain, ((m1_subset_1 @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('14', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('15', plain,
% 0.21/0.49      (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.49  thf('16', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('17', plain,
% 0.21/0.49      ((((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.49         | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)))
% 0.21/0.49         <= (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '13', '16'])).
% 0.21/0.49  thf('18', plain,
% 0.21/0.49      ((~ (r1_tarski @ sk_B @ sk_C_1)
% 0.21/0.49        | ~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('19', plain,
% 0.21/0.49      (~ ((r1_tarski @ sk_B @ sk_C_1)) | 
% 0.21/0.49       ~ ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1))),
% 0.21/0.49      inference('split', [status(esa)], ['18'])).
% 0.21/0.49  thf('20', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf(t2_subset, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.49       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.49  thf('21', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r2_hidden @ X0 @ X1)
% 0.21/0.49          | (v1_xboole_0 @ X1)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.49  thf('22', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.49  thf('23', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('24', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.21/0.49      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.49  thf('25', plain,
% 0.21/0.49      (((r1_tarski @ sk_B @ sk_C_1)) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['1'])).
% 0.21/0.49  thf(d1_wellord2, axiom,
% 0.21/0.49    (![A:$i,B:$i]:
% 0.21/0.49     ( ( v1_relat_1 @ B ) =>
% 0.21/0.49       ( ( ( B ) = ( k1_wellord2 @ A ) ) <=>
% 0.21/0.49         ( ( ( k3_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.49           ( ![C:$i,D:$i]:
% 0.21/0.49             ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) ) =>
% 0.21/0.49               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.21/0.49                 ( r1_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.21/0.49  thf('26', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.49         (((X3) != (k1_wellord2 @ X2))
% 0.21/0.49          | ~ (r2_hidden @ X4 @ X2)
% 0.21/0.49          | ~ (r2_hidden @ X5 @ X2)
% 0.21/0.49          | (r2_hidden @ (k4_tarski @ X4 @ X5) @ X3)
% 0.21/0.49          | ~ (r1_tarski @ X4 @ X5)
% 0.21/0.49          | ~ (v1_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.21/0.49  thf('27', plain,
% 0.21/0.49      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ (k1_wellord2 @ X2))
% 0.21/0.49          | ~ (r1_tarski @ X4 @ X5)
% 0.21/0.49          | (r2_hidden @ (k4_tarski @ X4 @ X5) @ (k1_wellord2 @ X2))
% 0.21/0.49          | ~ (r2_hidden @ X5 @ X2)
% 0.21/0.49          | ~ (r2_hidden @ X4 @ X2))),
% 0.21/0.49      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.49  thf(redefinition_k1_yellow_1, axiom,
% 0.21/0.49    (![A:$i]: ( ( k1_yellow_1 @ A ) = ( k1_wellord2 @ A ) ))).
% 0.21/0.49  thf('28', plain, (![X20 : $i]: ((k1_yellow_1 @ X20) = (k1_wellord2 @ X20))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k1_yellow_1])).
% 0.21/0.49  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.21/0.49  thf('29', plain, (![X6 : $i]: (v1_relat_1 @ (k1_wellord2 @ X6))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.21/0.49  thf('30', plain, (![X20 : $i]: ((k1_yellow_1 @ X20) = (k1_wellord2 @ X20))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k1_yellow_1])).
% 0.21/0.49  thf('31', plain, (![X6 : $i]: (v1_relat_1 @ (k1_yellow_1 @ X6))),
% 0.21/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('32', plain, (![X20 : $i]: ((k1_yellow_1 @ X20) = (k1_wellord2 @ X20))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k1_yellow_1])).
% 0.21/0.49  thf('33', plain,
% 0.21/0.49      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.21/0.49         (~ (r1_tarski @ X4 @ X5)
% 0.21/0.49          | (r2_hidden @ (k4_tarski @ X4 @ X5) @ (k1_yellow_1 @ X2))
% 0.21/0.49          | ~ (r2_hidden @ X5 @ X2)
% 0.21/0.49          | ~ (r2_hidden @ X4 @ X2))),
% 0.21/0.49      inference('demod', [status(thm)], ['27', '28', '31', '32'])).
% 0.21/0.49  thf('34', plain,
% 0.21/0.49      ((![X0 : $i]:
% 0.21/0.49          (~ (r2_hidden @ sk_B @ X0)
% 0.21/0.49           | ~ (r2_hidden @ sk_C_1 @ X0)
% 0.21/0.49           | (r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (k1_yellow_1 @ X0))))
% 0.21/0.49         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['25', '33'])).
% 0.21/0.49  thf('35', plain,
% 0.21/0.49      ((((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (k1_yellow_1 @ sk_A))
% 0.21/0.49         | ~ (r2_hidden @ sk_C_1 @ sk_A))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['24', '34'])).
% 0.21/0.49  thf('36', plain, ((m1_subset_1 @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('37', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i]:
% 0.21/0.49         ((r2_hidden @ X0 @ X1)
% 0.21/0.49          | (v1_xboole_0 @ X1)
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.21/0.49      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.49  thf('38', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_C_1 @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.49  thf('39', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('40', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.49  thf('41', plain,
% 0.21/0.49      (((r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (k1_yellow_1 @ sk_A)))
% 0.21/0.49         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['35', '40'])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (![X22 : $i]: ((u1_orders_2 @ (k2_yellow_1 @ X22)) = (k1_yellow_1 @ X22))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.49  thf(d9_orders_2, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( l1_orders_2 @ A ) =>
% 0.21/0.49       ( ![B:$i]:
% 0.21/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49           ( ![C:$i]:
% 0.21/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.21/0.49               ( ( r1_orders_2 @ A @ B @ C ) <=>
% 0.21/0.49                 ( r2_hidden @ ( k4_tarski @ B @ C ) @ ( u1_orders_2 @ A ) ) ) ) ) ) ) ))).
% 0.21/0.49  thf('43', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.21/0.49          | ~ (r2_hidden @ (k4_tarski @ X7 @ X9) @ (u1_orders_2 @ X8))
% 0.21/0.49          | (r1_orders_2 @ X8 @ X7 @ X9)
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.49          | ~ (l1_orders_2 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k1_yellow_1 @ X0))
% 0.21/0.49          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.21/0.49          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['42', '43'])).
% 0.21/0.49  thf('45', plain, (![X14 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.49  thf('48', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k1_yellow_1 @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.49          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ X2 @ X1)
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ X0))),
% 0.21/0.49      inference('demod', [status(thm)], ['44', '45', '46', '47'])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (((~ (m1_subset_1 @ sk_B @ sk_A)
% 0.21/0.49         | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)
% 0.21/0.49         | ~ (m1_subset_1 @ sk_C_1 @ sk_A))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['41', '48'])).
% 0.21/0.49  thf('50', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('51', plain, ((m1_subset_1 @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      (((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1))
% 0.21/0.49         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.49  thf('54', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.21/0.49          | ~ (l1_orders_2 @ X11)
% 0.21/0.49          | ~ (v3_orders_2 @ X11)
% 0.21/0.49          | (v2_struct_0 @ X11)
% 0.21/0.49          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.21/0.49          | (r3_orders_2 @ X11 @ X10 @ X12)
% 0.21/0.49          | ~ (r1_orders_2 @ X11 @ X10 @ X12))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.21/0.49  thf('55', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.49          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.49          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.21/0.49          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.21/0.49          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.49          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['53', '54'])).
% 0.21/0.49  thf('56', plain,
% 0.21/0.49      (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.49  thf('57', plain, (![X16 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X16))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.21/0.49  thf('58', plain, (![X14 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.49  thf('59', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.49          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.49          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ X0)
% 0.21/0.49          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.21/0.49      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      ((((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.49         | ~ (m1_subset_1 @ sk_C_1 @ sk_A)
% 0.21/0.49         | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)
% 0.21/0.49         | ~ (m1_subset_1 @ sk_B @ sk_A))) <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['52', '59'])).
% 0.21/0.49  thf('61', plain, ((m1_subset_1 @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('62', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('63', plain,
% 0.21/0.49      ((((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.49         | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)))
% 0.21/0.49         <= (((r1_tarski @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.21/0.49  thf('64', plain,
% 0.21/0.49      ((~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1))
% 0.21/0.49         <= (~ ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['18'])).
% 0.21/0.49  thf('65', plain,
% 0.21/0.49      (((v2_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.21/0.49         <= (~ ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)) & 
% 0.21/0.49             ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['63', '64'])).
% 0.21/0.49  thf(fc6_yellow_1, axiom,
% 0.21/0.49    (![A:$i]:
% 0.21/0.49     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.49       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.21/0.49         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.21/0.49  thf('66', plain,
% 0.21/0.49      (![X19 : $i]:
% 0.21/0.49         (~ (v2_struct_0 @ (k2_yellow_1 @ X19)) | (v1_xboole_0 @ X19))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.21/0.49  thf('67', plain,
% 0.21/0.49      (((v1_xboole_0 @ sk_A))
% 0.21/0.49         <= (~ ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)) & 
% 0.21/0.49             ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.49  thf('68', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('69', plain,
% 0.21/0.49      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)) | 
% 0.21/0.49       ~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.49  thf('70', plain,
% 0.21/0.49      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1)) | 
% 0.21/0.49       ((r1_tarski @ sk_B @ sk_C_1))),
% 0.21/0.49      inference('split', [status(esa)], ['1'])).
% 0.21/0.49  thf('71', plain, (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['19', '69', '70'])).
% 0.21/0.49  thf('72', plain,
% 0.21/0.49      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.49        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C_1))),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['17', '71'])).
% 0.21/0.49  thf('73', plain,
% 0.21/0.49      (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.49  thf('74', plain,
% 0.21/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.21/0.49          | ~ (r1_orders_2 @ X8 @ X7 @ X9)
% 0.21/0.49          | (r2_hidden @ (k4_tarski @ X7 @ X9) @ (u1_orders_2 @ X8))
% 0.21/0.49          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.21/0.49          | ~ (l1_orders_2 @ X8))),
% 0.21/0.49      inference('cnf', [status(esa)], [d9_orders_2])).
% 0.21/0.49  thf('75', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.49          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.21/0.49          | (r2_hidden @ (k4_tarski @ X1 @ X2) @ 
% 0.21/0.49             (u1_orders_2 @ (k2_yellow_1 @ X0)))
% 0.21/0.49          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2))),
% 0.21/0.49      inference('sup-', [status(thm)], ['73', '74'])).
% 0.21/0.49  thf('76', plain, (![X14 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X14))),
% 0.21/0.49      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.21/0.49  thf('77', plain,
% 0.21/0.49      (![X21 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X21)) = (X21))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.49  thf('78', plain,
% 0.21/0.49      (![X22 : $i]: ((u1_orders_2 @ (k2_yellow_1 @ X22)) = (k1_yellow_1 @ X22))),
% 0.21/0.49      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.21/0.49  thf('79', plain,
% 0.21/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X1 @ X0)
% 0.21/0.49          | ~ (m1_subset_1 @ X2 @ X0)
% 0.21/0.49          | (r2_hidden @ (k4_tarski @ X1 @ X2) @ (k1_yellow_1 @ X0))
% 0.21/0.49          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2))),
% 0.21/0.49      inference('demod', [status(thm)], ['75', '76', '77', '78'])).
% 0.21/0.49  thf('80', plain,
% 0.21/0.49      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.49        | (r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (k1_yellow_1 @ sk_A))
% 0.21/0.49        | ~ (m1_subset_1 @ sk_C_1 @ sk_A)
% 0.21/0.49        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['72', '79'])).
% 0.21/0.49  thf('81', plain, ((m1_subset_1 @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.49  thf('82', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.21/0.49      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.49  thf('83', plain,
% 0.21/0.49      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.49        | (r2_hidden @ (k4_tarski @ sk_B @ sk_C_1) @ (k1_yellow_1 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.21/0.49  thf('84', plain,
% 0.21/0.49      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.49         (((X3) != (k1_wellord2 @ X2))
% 0.21/0.49          | ~ (r2_hidden @ X4 @ X2)
% 0.21/0.49          | ~ (r2_hidden @ X5 @ X2)
% 0.21/0.49          | (r1_tarski @ X4 @ X5)
% 0.21/0.49          | ~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ X3)
% 0.21/0.49          | ~ (v1_relat_1 @ X3))),
% 0.21/0.49      inference('cnf', [status(esa)], [d1_wellord2])).
% 0.21/0.49  thf('85', plain,
% 0.21/0.49      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ (k1_wellord2 @ X2))
% 0.21/0.49          | ~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ (k1_wellord2 @ X2))
% 0.21/0.49          | (r1_tarski @ X4 @ X5)
% 0.21/0.49          | ~ (r2_hidden @ X5 @ X2)
% 0.21/0.49          | ~ (r2_hidden @ X4 @ X2))),
% 0.21/0.49      inference('simplify', [status(thm)], ['84'])).
% 0.21/0.49  thf('86', plain, (![X20 : $i]: ((k1_yellow_1 @ X20) = (k1_wellord2 @ X20))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k1_yellow_1])).
% 0.21/0.49  thf('87', plain, (![X6 : $i]: (v1_relat_1 @ (k1_yellow_1 @ X6))),
% 0.21/0.49      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.49  thf('88', plain, (![X20 : $i]: ((k1_yellow_1 @ X20) = (k1_wellord2 @ X20))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k1_yellow_1])).
% 0.21/0.49  thf('89', plain,
% 0.21/0.49      (![X2 : $i, X4 : $i, X5 : $i]:
% 0.21/0.49         (~ (r2_hidden @ (k4_tarski @ X4 @ X5) @ (k1_yellow_1 @ X2))
% 0.21/0.49          | (r1_tarski @ X4 @ X5)
% 0.21/0.49          | ~ (r2_hidden @ X5 @ X2)
% 0.21/0.49          | ~ (r2_hidden @ X4 @ X2))),
% 0.21/0.49      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.21/0.49  thf('90', plain,
% 0.21/0.49      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.21/0.49        | ~ (r2_hidden @ sk_B @ sk_A)
% 0.21/0.49        | ~ (r2_hidden @ sk_C_1 @ sk_A)
% 0.21/0.49        | (r1_tarski @ sk_B @ sk_C_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['83', '89'])).
% 0.21/0.49  thf('91', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.21/0.49      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.49  thf('92', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.21/0.49      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.49  thf('93', plain,
% 0.21/0.49      (((v2_struct_0 @ (k2_yellow_1 @ sk_A)) | (r1_tarski @ sk_B @ sk_C_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.21/0.49  thf('94', plain,
% 0.21/0.49      ((~ (r1_tarski @ sk_B @ sk_C_1)) <= (~ ((r1_tarski @ sk_B @ sk_C_1)))),
% 0.21/0.49      inference('split', [status(esa)], ['18'])).
% 0.21/0.49  thf('95', plain, (~ ((r1_tarski @ sk_B @ sk_C_1))),
% 0.21/0.49      inference('sat_resolution*', [status(thm)], ['19', '69'])).
% 0.21/0.49  thf('96', plain, (~ (r1_tarski @ sk_B @ sk_C_1)),
% 0.21/0.49      inference('simpl_trail', [status(thm)], ['94', '95'])).
% 0.21/0.49  thf('97', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['93', '96'])).
% 0.21/0.49  thf('98', plain,
% 0.21/0.49      (![X19 : $i]:
% 0.21/0.49         (~ (v2_struct_0 @ (k2_yellow_1 @ X19)) | (v1_xboole_0 @ X19))),
% 0.21/0.49      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.21/0.49  thf('99', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('sup-', [status(thm)], ['97', '98'])).
% 0.21/0.49  thf('100', plain, ($false), inference('demod', [status(thm)], ['0', '99'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
