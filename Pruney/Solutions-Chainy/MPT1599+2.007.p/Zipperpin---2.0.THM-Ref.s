%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1upB40gvcc

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:06 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 335 expanded)
%              Number of leaves         :   31 ( 127 expanded)
%              Depth                    :   17
%              Number of atoms          : 1170 (3853 expanded)
%              Number of equality atoms :   20 ( 160 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(t7_yellow_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
               => ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ ( k3_xboole_0 @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) )
         => ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
                 => ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_yellow_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('2',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k11_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k11_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('8',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( m1_subset_1 @ ( k11_lattice3 @ X8 @ X7 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_lattice3])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('11',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X16: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(l28_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( D
                      = ( k11_lattice3 @ A @ B @ C ) )
                  <=> ( ( r1_orders_2 @ A @ D @ B )
                      & ( r1_orders_2 @ A @ D @ C )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( ( r1_orders_2 @ A @ E @ B )
                              & ( r1_orders_2 @ A @ E @ C ) )
                           => ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( X12
       != ( k11_lattice3 @ X11 @ X10 @ X13 ) )
      | ( r1_orders_2 @ X11 @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v2_lattice3 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('18',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v2_lattice3 @ X11 )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( r1_orders_2 @ X11 @ ( k11_lattice3 @ X11 @ X10 @ X13 ) @ X13 )
      | ~ ( m1_subset_1 @ ( k11_lattice3 @ X11 @ X10 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('21',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('22',plain,(
    ! [X16: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X20: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20','21','22','23'])).

thf('25',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('28',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('29',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
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

thf('31',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r3_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('34',plain,(
    ! [X18: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('35',plain,(
    ! [X16: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('37',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('39',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['3','14'])).

thf('40',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('42',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X25 ) @ X24 @ X26 )
      | ( r1_tarski @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ ( k2_yellow_1 @ X25 ) ) )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('43',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('44',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('45',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ X25 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X25 ) @ X24 @ X26 )
      | ( r1_tarski @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('48',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['3','14'])).

thf('49',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf(fc6_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ A ) )
        & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ) )).

thf('50',plain,(
    ! [X21: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X21 ) )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('51',plain,
    ( ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['3','14'])).

thf('55',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( X12
       != ( k11_lattice3 @ X11 @ X10 @ X13 ) )
      | ( r1_orders_2 @ X11 @ X12 @ X10 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v2_lattice3 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('57',plain,(
    ! [X10: $i,X11: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v2_lattice3 @ X11 )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( r1_orders_2 @ X11 @ ( k11_lattice3 @ X11 @ X10 @ X13 ) @ X10 )
      | ~ ( m1_subset_1 @ ( k11_lattice3 @ X11 @ X10 @ X13 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('60',plain,(
    ! [X22: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X22 ) )
      = X22 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('61',plain,(
    ! [X16: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('62',plain,(
    ! [X20: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62'])).

thf('64',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['54','63'])).

thf('65',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('68',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['32','33','34','35'])).

thf('70',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('72',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['3','14'])).

thf('73',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ X25 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X25 ) @ X24 @ X26 )
      | ( r1_tarski @ X24 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ X25 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('76',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('78',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['3','14'])).

thf('79',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X21: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X21 ) )
      | ( v1_xboole_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[fc6_yellow_1])).

thf('81',plain,
    ( ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ),
    inference(clc,[status(thm)],['81','82'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['53','85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['0','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1upB40gvcc
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:41:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.55/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.73  % Solved by: fo/fo7.sh
% 0.55/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.73  % done 228 iterations in 0.288s
% 0.55/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.73  % SZS output start Refutation
% 0.55/0.73  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.55/0.73  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.55/0.73  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.55/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.73  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.55/0.73  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.55/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.73  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.55/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.55/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.73  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.55/0.73  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.55/0.73  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.55/0.73  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.55/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.55/0.73  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.55/0.73  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.55/0.73  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.55/0.73  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.55/0.73  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.55/0.73  thf(t7_yellow_1, conjecture,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.55/0.73       ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.55/0.73         ( ![B:$i]:
% 0.55/0.73           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.55/0.73             ( ![C:$i]:
% 0.55/0.73               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.55/0.73                 ( r1_tarski @
% 0.55/0.73                   ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 0.55/0.73                   ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ))).
% 0.55/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.73    (~( ![A:$i]:
% 0.55/0.73        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.55/0.73          ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.55/0.73            ( ![B:$i]:
% 0.55/0.73              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.55/0.73                ( ![C:$i]:
% 0.55/0.73                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.55/0.73                    ( r1_tarski @
% 0.55/0.73                      ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 0.55/0.73                      ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ) )),
% 0.55/0.73    inference('cnf.neg', [status(esa)], [t7_yellow_1])).
% 0.55/0.73  thf('0', plain,
% 0.55/0.73      (~ (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.55/0.73          (k3_xboole_0 @ sk_B @ sk_C))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('1', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf(t1_yellow_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.55/0.73       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.55/0.73  thf('2', plain, (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.55/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.55/0.73  thf('3', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.55/0.73      inference('demod', [status(thm)], ['1', '2'])).
% 0.55/0.73  thf('4', plain,
% 0.55/0.73      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('5', plain, (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.55/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.55/0.73  thf('6', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.55/0.73      inference('demod', [status(thm)], ['4', '5'])).
% 0.55/0.73  thf('7', plain, (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.55/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.55/0.73  thf(dt_k11_lattice3, axiom,
% 0.55/0.73    (![A:$i,B:$i,C:$i]:
% 0.55/0.73     ( ( ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.55/0.73         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.73       ( m1_subset_1 @ ( k11_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.55/0.73  thf('8', plain,
% 0.55/0.73      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.55/0.73          | ~ (l1_orders_2 @ X8)
% 0.55/0.73          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.55/0.73          | (m1_subset_1 @ (k11_lattice3 @ X8 @ X7 @ X9) @ (u1_struct_0 @ X8)))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k11_lattice3])).
% 0.55/0.73  thf('9', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X1 @ X0)
% 0.55/0.73          | (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ 
% 0.55/0.73             (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.55/0.73          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.55/0.73          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['7', '8'])).
% 0.55/0.73  thf('10', plain,
% 0.55/0.73      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.55/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.55/0.73  thf('11', plain,
% 0.55/0.73      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.55/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.55/0.73  thf(dt_k2_yellow_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.55/0.73       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.55/0.73  thf('12', plain, (![X16 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X16))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.55/0.73  thf('13', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X1 @ X0)
% 0.55/0.73          | (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ X0)
% 0.55/0.73          | ~ (m1_subset_1 @ X2 @ X0))),
% 0.55/0.73      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.55/0.73  thf('14', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.55/0.73          | (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 0.55/0.73             sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['6', '13'])).
% 0.55/0.73  thf('15', plain,
% 0.55/0.73      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.55/0.73        sk_A)),
% 0.55/0.73      inference('sup-', [status(thm)], ['3', '14'])).
% 0.55/0.73  thf('16', plain,
% 0.55/0.73      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.55/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.55/0.73  thf(l28_lattice3, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.55/0.73         ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.55/0.73           ( ![C:$i]:
% 0.55/0.73             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.55/0.73               ( ![D:$i]:
% 0.55/0.73                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.55/0.73                   ( ( ( D ) = ( k11_lattice3 @ A @ B @ C ) ) <=>
% 0.55/0.73                     ( ( r1_orders_2 @ A @ D @ B ) & 
% 0.55/0.73                       ( r1_orders_2 @ A @ D @ C ) & 
% 0.55/0.73                       ( ![E:$i]:
% 0.55/0.73                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.55/0.73                           ( ( ( r1_orders_2 @ A @ E @ B ) & 
% 0.55/0.73                               ( r1_orders_2 @ A @ E @ C ) ) =>
% 0.55/0.73                             ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.55/0.73  thf('17', plain,
% 0.55/0.73      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.55/0.73          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.55/0.73          | ((X12) != (k11_lattice3 @ X11 @ X10 @ X13))
% 0.55/0.73          | (r1_orders_2 @ X11 @ X12 @ X13)
% 0.55/0.73          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.55/0.73          | ~ (l1_orders_2 @ X11)
% 0.55/0.73          | ~ (v2_lattice3 @ X11)
% 0.55/0.73          | ~ (v5_orders_2 @ X11)
% 0.55/0.73          | (v2_struct_0 @ X11))),
% 0.55/0.73      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.55/0.73  thf('18', plain,
% 0.55/0.73      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.55/0.73         ((v2_struct_0 @ X11)
% 0.55/0.73          | ~ (v5_orders_2 @ X11)
% 0.55/0.73          | ~ (v2_lattice3 @ X11)
% 0.55/0.73          | ~ (l1_orders_2 @ X11)
% 0.55/0.73          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.55/0.73          | (r1_orders_2 @ X11 @ (k11_lattice3 @ X11 @ X10 @ X13) @ X13)
% 0.55/0.73          | ~ (m1_subset_1 @ (k11_lattice3 @ X11 @ X10 @ X13) @ 
% 0.55/0.73               (u1_struct_0 @ X11))
% 0.55/0.73          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11)))),
% 0.55/0.73      inference('simplify', [status(thm)], ['17'])).
% 0.55/0.73  thf('19', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X0)
% 0.55/0.73          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.55/0.73          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.55/0.73             (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X1)
% 0.55/0.73          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.55/0.73          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.55/0.73          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 0.55/0.73          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.55/0.73          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['16', '18'])).
% 0.55/0.73  thf('20', plain,
% 0.55/0.73      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.55/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.55/0.73  thf('21', plain,
% 0.55/0.73      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.55/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.55/0.73  thf('22', plain, (![X16 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X16))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.55/0.73  thf(fc5_yellow_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.55/0.73       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.55/0.73       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.55/0.73       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.55/0.73  thf('23', plain, (![X20 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X20))),
% 0.55/0.73      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.55/0.73  thf('24', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X0)
% 0.55/0.73          | ~ (m1_subset_1 @ X2 @ X0)
% 0.55/0.73          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.55/0.73             (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X1)
% 0.55/0.73          | ~ (m1_subset_1 @ X1 @ X0)
% 0.55/0.73          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 0.55/0.73          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.55/0.73      inference('demod', [status(thm)], ['19', '20', '21', '22', '23'])).
% 0.55/0.73  thf('25', plain,
% 0.55/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.55/0.73        | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.55/0.73        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.55/0.73        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.55/0.73           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.55/0.73        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['15', '24'])).
% 0.55/0.73  thf('26', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('27', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.55/0.73      inference('demod', [status(thm)], ['1', '2'])).
% 0.55/0.73  thf('28', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.55/0.73      inference('demod', [status(thm)], ['4', '5'])).
% 0.55/0.73  thf('29', plain,
% 0.55/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.55/0.73        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.55/0.73           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 0.55/0.73  thf('30', plain,
% 0.55/0.73      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.55/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.55/0.73  thf(redefinition_r3_orders_2, axiom,
% 0.55/0.73    (![A:$i,B:$i,C:$i]:
% 0.55/0.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.55/0.73         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.55/0.73         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.73       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.55/0.73  thf('31', plain,
% 0.55/0.73      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.55/0.73          | ~ (l1_orders_2 @ X4)
% 0.55/0.73          | ~ (v3_orders_2 @ X4)
% 0.55/0.73          | (v2_struct_0 @ X4)
% 0.55/0.73          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.55/0.73          | (r3_orders_2 @ X4 @ X3 @ X5)
% 0.55/0.73          | ~ (r1_orders_2 @ X4 @ X3 @ X5))),
% 0.55/0.73      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.55/0.73  thf('32', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X1 @ X0)
% 0.55/0.73          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.55/0.73          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.55/0.73          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.55/0.73          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.55/0.73          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.55/0.73          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['30', '31'])).
% 0.55/0.73  thf('33', plain,
% 0.55/0.73      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.55/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.55/0.73  thf('34', plain, (![X18 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X18))),
% 0.55/0.73      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.55/0.73  thf('35', plain, (![X16 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X16))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.55/0.73  thf('36', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X1 @ X0)
% 0.55/0.73          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.55/0.73          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.55/0.73          | ~ (m1_subset_1 @ X2 @ X0)
% 0.55/0.73          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.55/0.73      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.55/0.73  thf('37', plain,
% 0.55/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.55/0.73        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.55/0.73        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.55/0.73        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.55/0.73           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.55/0.73        | ~ (m1_subset_1 @ 
% 0.55/0.73             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['29', '36'])).
% 0.55/0.73  thf('38', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.55/0.73      inference('demod', [status(thm)], ['1', '2'])).
% 0.55/0.73  thf('39', plain,
% 0.55/0.73      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.55/0.73        sk_A)),
% 0.55/0.73      inference('sup-', [status(thm)], ['3', '14'])).
% 0.55/0.73  thf('40', plain,
% 0.55/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.55/0.73        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.55/0.73        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.55/0.73           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.55/0.73  thf('41', plain,
% 0.55/0.73      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.55/0.73         (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.55/0.73        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.55/0.73      inference('simplify', [status(thm)], ['40'])).
% 0.55/0.73  thf(t3_yellow_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.55/0.73       ( ![B:$i]:
% 0.55/0.73         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.55/0.73           ( ![C:$i]:
% 0.55/0.73             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.55/0.73               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.55/0.73                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.55/0.73  thf('42', plain,
% 0.55/0.73      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X24 @ (u1_struct_0 @ (k2_yellow_1 @ X25)))
% 0.55/0.73          | ~ (r3_orders_2 @ (k2_yellow_1 @ X25) @ X24 @ X26)
% 0.55/0.73          | (r1_tarski @ X24 @ X26)
% 0.55/0.73          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ (k2_yellow_1 @ X25)))
% 0.55/0.73          | (v1_xboole_0 @ X25))),
% 0.55/0.73      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.55/0.73  thf('43', plain,
% 0.55/0.73      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.55/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.55/0.73  thf('44', plain,
% 0.55/0.73      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.55/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.55/0.73  thf('45', plain,
% 0.55/0.73      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X24 @ X25)
% 0.55/0.73          | ~ (r3_orders_2 @ (k2_yellow_1 @ X25) @ X24 @ X26)
% 0.55/0.73          | (r1_tarski @ X24 @ X26)
% 0.55/0.73          | ~ (m1_subset_1 @ X26 @ X25)
% 0.55/0.73          | (v1_xboole_0 @ X25))),
% 0.55/0.73      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.55/0.73  thf('46', plain,
% 0.55/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.55/0.73        | (v1_xboole_0 @ sk_A)
% 0.55/0.73        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.55/0.73        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.55/0.73           sk_C)
% 0.55/0.73        | ~ (m1_subset_1 @ 
% 0.55/0.73             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['41', '45'])).
% 0.55/0.73  thf('47', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.55/0.73      inference('demod', [status(thm)], ['1', '2'])).
% 0.55/0.73  thf('48', plain,
% 0.55/0.73      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.55/0.73        sk_A)),
% 0.55/0.73      inference('sup-', [status(thm)], ['3', '14'])).
% 0.55/0.73  thf('49', plain,
% 0.55/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.55/0.73        | (v1_xboole_0 @ sk_A)
% 0.55/0.73        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.55/0.73           sk_C))),
% 0.55/0.73      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.55/0.73  thf(fc6_yellow_1, axiom,
% 0.55/0.73    (![A:$i]:
% 0.55/0.73     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.55/0.73       ( ( ~( v2_struct_0 @ ( k2_yellow_1 @ A ) ) ) & 
% 0.55/0.73         ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) ))).
% 0.55/0.73  thf('50', plain,
% 0.55/0.73      (![X21 : $i]:
% 0.55/0.73         (~ (v2_struct_0 @ (k2_yellow_1 @ X21)) | (v1_xboole_0 @ X21))),
% 0.55/0.73      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.55/0.73  thf('51', plain,
% 0.55/0.73      (((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.55/0.73        | (v1_xboole_0 @ sk_A))),
% 0.55/0.73      inference('clc', [status(thm)], ['49', '50'])).
% 0.55/0.73  thf('52', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('53', plain,
% 0.55/0.73      ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)),
% 0.55/0.73      inference('clc', [status(thm)], ['51', '52'])).
% 0.55/0.73  thf('54', plain,
% 0.55/0.73      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.55/0.73        sk_A)),
% 0.55/0.73      inference('sup-', [status(thm)], ['3', '14'])).
% 0.55/0.73  thf('55', plain,
% 0.55/0.73      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.55/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.55/0.73  thf('56', plain,
% 0.55/0.73      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.55/0.73          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.55/0.73          | ((X12) != (k11_lattice3 @ X11 @ X10 @ X13))
% 0.55/0.73          | (r1_orders_2 @ X11 @ X12 @ X10)
% 0.55/0.73          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.55/0.73          | ~ (l1_orders_2 @ X11)
% 0.55/0.73          | ~ (v2_lattice3 @ X11)
% 0.55/0.73          | ~ (v5_orders_2 @ X11)
% 0.55/0.73          | (v2_struct_0 @ X11))),
% 0.55/0.73      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.55/0.73  thf('57', plain,
% 0.55/0.73      (![X10 : $i, X11 : $i, X13 : $i]:
% 0.55/0.73         ((v2_struct_0 @ X11)
% 0.55/0.73          | ~ (v5_orders_2 @ X11)
% 0.55/0.73          | ~ (v2_lattice3 @ X11)
% 0.55/0.73          | ~ (l1_orders_2 @ X11)
% 0.55/0.73          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.55/0.73          | (r1_orders_2 @ X11 @ (k11_lattice3 @ X11 @ X10 @ X13) @ X10)
% 0.55/0.73          | ~ (m1_subset_1 @ (k11_lattice3 @ X11 @ X10 @ X13) @ 
% 0.55/0.73               (u1_struct_0 @ X11))
% 0.55/0.73          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11)))),
% 0.55/0.73      inference('simplify', [status(thm)], ['56'])).
% 0.55/0.73  thf('58', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X0)
% 0.55/0.73          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.55/0.73          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.55/0.73             (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X2)
% 0.55/0.73          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.55/0.73          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.55/0.73          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 0.55/0.73          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.55/0.73          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.55/0.73      inference('sup-', [status(thm)], ['55', '57'])).
% 0.55/0.73  thf('59', plain,
% 0.55/0.73      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.55/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.55/0.73  thf('60', plain,
% 0.55/0.73      (![X22 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X22)) = (X22))),
% 0.55/0.73      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.55/0.73  thf('61', plain, (![X16 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X16))),
% 0.55/0.73      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.55/0.73  thf('62', plain, (![X20 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X20))),
% 0.55/0.73      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.55/0.73  thf('63', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X0)
% 0.55/0.73          | ~ (m1_subset_1 @ X2 @ X0)
% 0.55/0.73          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.55/0.73             (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X2)
% 0.55/0.73          | ~ (m1_subset_1 @ X1 @ X0)
% 0.55/0.73          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 0.55/0.73          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.55/0.73      inference('demod', [status(thm)], ['58', '59', '60', '61', '62'])).
% 0.55/0.73  thf('64', plain,
% 0.55/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.55/0.73        | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.55/0.73        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.55/0.73        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.55/0.73           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.55/0.73        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['54', '63'])).
% 0.55/0.73  thf('65', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('66', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.55/0.73      inference('demod', [status(thm)], ['1', '2'])).
% 0.55/0.73  thf('67', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.55/0.73      inference('demod', [status(thm)], ['4', '5'])).
% 0.55/0.73  thf('68', plain,
% 0.55/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.55/0.73        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.55/0.73           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 0.55/0.73      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 0.55/0.73  thf('69', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X1 @ X0)
% 0.55/0.73          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.55/0.73          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.55/0.73          | ~ (m1_subset_1 @ X2 @ X0)
% 0.55/0.73          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.55/0.73      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.55/0.73  thf('70', plain,
% 0.55/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.55/0.73        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.55/0.73        | ~ (m1_subset_1 @ sk_B @ sk_A)
% 0.55/0.73        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.55/0.73           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.55/0.73        | ~ (m1_subset_1 @ 
% 0.55/0.73             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['68', '69'])).
% 0.55/0.73  thf('71', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.55/0.73      inference('demod', [status(thm)], ['4', '5'])).
% 0.55/0.73  thf('72', plain,
% 0.55/0.73      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.55/0.73        sk_A)),
% 0.55/0.73      inference('sup-', [status(thm)], ['3', '14'])).
% 0.55/0.73  thf('73', plain,
% 0.55/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.55/0.73        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.55/0.73        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.55/0.73           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 0.55/0.73      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.55/0.73  thf('74', plain,
% 0.55/0.73      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.55/0.73         (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.55/0.73        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.55/0.73      inference('simplify', [status(thm)], ['73'])).
% 0.55/0.73  thf('75', plain,
% 0.55/0.73      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.55/0.73         (~ (m1_subset_1 @ X24 @ X25)
% 0.55/0.73          | ~ (r3_orders_2 @ (k2_yellow_1 @ X25) @ X24 @ X26)
% 0.55/0.73          | (r1_tarski @ X24 @ X26)
% 0.55/0.73          | ~ (m1_subset_1 @ X26 @ X25)
% 0.55/0.73          | (v1_xboole_0 @ X25))),
% 0.55/0.73      inference('demod', [status(thm)], ['42', '43', '44'])).
% 0.55/0.73  thf('76', plain,
% 0.55/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.55/0.73        | (v1_xboole_0 @ sk_A)
% 0.55/0.73        | ~ (m1_subset_1 @ sk_B @ sk_A)
% 0.55/0.73        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.55/0.73           sk_B)
% 0.55/0.73        | ~ (m1_subset_1 @ 
% 0.55/0.73             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 0.55/0.73      inference('sup-', [status(thm)], ['74', '75'])).
% 0.55/0.73  thf('77', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.55/0.73      inference('demod', [status(thm)], ['4', '5'])).
% 0.55/0.73  thf('78', plain,
% 0.55/0.73      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.55/0.73        sk_A)),
% 0.55/0.73      inference('sup-', [status(thm)], ['3', '14'])).
% 0.55/0.73  thf('79', plain,
% 0.55/0.73      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.55/0.73        | (v1_xboole_0 @ sk_A)
% 0.55/0.73        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.55/0.73           sk_B))),
% 0.55/0.73      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.55/0.73  thf('80', plain,
% 0.55/0.73      (![X21 : $i]:
% 0.55/0.73         (~ (v2_struct_0 @ (k2_yellow_1 @ X21)) | (v1_xboole_0 @ X21))),
% 0.55/0.73      inference('cnf', [status(esa)], [fc6_yellow_1])).
% 0.55/0.73  thf('81', plain,
% 0.55/0.73      (((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.55/0.73        | (v1_xboole_0 @ sk_A))),
% 0.55/0.73      inference('clc', [status(thm)], ['79', '80'])).
% 0.55/0.73  thf('82', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.55/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.73  thf('83', plain,
% 0.55/0.73      ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)),
% 0.55/0.73      inference('clc', [status(thm)], ['81', '82'])).
% 0.55/0.73  thf(t19_xboole_1, axiom,
% 0.55/0.73    (![A:$i,B:$i,C:$i]:
% 0.55/0.73     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.55/0.73       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.55/0.73  thf('84', plain,
% 0.55/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.73         (~ (r1_tarski @ X0 @ X1)
% 0.55/0.73          | ~ (r1_tarski @ X0 @ X2)
% 0.55/0.73          | (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.55/0.73      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.55/0.73  thf('85', plain,
% 0.55/0.73      (![X0 : $i]:
% 0.55/0.73         ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.55/0.73           (k3_xboole_0 @ sk_B @ X0))
% 0.55/0.73          | ~ (r1_tarski @ 
% 0.55/0.73               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))),
% 0.55/0.73      inference('sup-', [status(thm)], ['83', '84'])).
% 0.55/0.73  thf('86', plain,
% 0.55/0.73      ((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.55/0.73        (k3_xboole_0 @ sk_B @ sk_C))),
% 0.55/0.73      inference('sup-', [status(thm)], ['53', '85'])).
% 0.55/0.73  thf('87', plain, ($false), inference('demod', [status(thm)], ['0', '86'])).
% 0.55/0.73  
% 0.55/0.73  % SZS output end Refutation
% 0.55/0.73  
% 0.55/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
