%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hiy502ZbVe

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:07 EST 2020

% Result     : Theorem 12.50s
% Output     : Refutation 12.50s
% Verified   : 
% Statistics : Number of formulae       :  254 (1890 expanded)
%              Number of leaves         :   34 ( 638 expanded)
%              Depth                    :   23
%              Number of atoms          : 2845 (23530 expanded)
%              Number of equality atoms :  118 (1133 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) )
        = ( k1_yellow_1 @ A ) )
      & ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('4',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k11_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k11_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( m1_subset_1 @ ( k11_lattice3 @ X10 @ X9 @ X11 ) @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_lattice3])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('8',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X26: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7','8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('12',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['2','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(reflexivity_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( r3_orders_2 @ A @ B @ B ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r3_orders_2 @ X5 @ X6 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_orders_2 @ X5 )
      | ~ ( v3_orders_2 @ X5 )
      | ( v2_struct_0 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r3_orders_2])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X28: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('21',plain,(
    ! [X26: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('25',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(t25_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v3_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( B
                  = ( k12_lattice3 @ A @ B @ C ) )
              <=> ( r3_orders_2 @ A @ B @ C ) ) ) ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r3_orders_2 @ X23 @ X22 @ X24 )
      | ( X22
        = ( k12_lattice3 @ X23 @ X22 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( X1
        = ( k12_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X28: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('30',plain,(
    ! [X30: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('31',plain,(
    ! [X26: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('32',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( X1
        = ( k12_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
      | ( X1
        = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( sk_C
      = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('38',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( sk_C
      = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('42',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(t16_lattice3,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( v4_orders_2 @ A )
                   => ( ( k11_lattice3 @ A @ ( k11_lattice3 @ A @ B @ C ) @ D )
                      = ( k11_lattice3 @ A @ B @ ( k11_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) )).

thf('44',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ( ( k11_lattice3 @ X19 @ ( k11_lattice3 @ X19 @ X18 @ X21 ) @ X20 )
        = ( k11_lattice3 @ X19 @ X18 @ ( k11_lattice3 @ X19 @ X21 @ X20 ) ) )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v2_lattice3 @ X19 )
      | ~ ( v5_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t16_lattice3])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( v4_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ X3 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X3 ) ) )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X30: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('47',plain,(
    ! [X26: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('48',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('49',plain,(
    ! [X29: $i] :
      ( v4_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('50',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ X3 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X3 ) ) )
      | ~ ( m1_subset_1 @ X3 @ X0 ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X2 @ X1 ) @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X2 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ X1 ) @ sk_B )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['41','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) @ sk_B )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','53'])).

thf('55',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['39','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('58',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(redefinition_k12_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k12_lattice3 @ A @ B @ C )
        = ( k11_lattice3 @ A @ B @ C ) ) ) )).

thf('60',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v2_lattice3 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ( ( k12_lattice3 @ X13 @ X12 @ X14 )
        = ( k11_lattice3 @ X13 @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k12_lattice3])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('63',plain,(
    ! [X30: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('64',plain,(
    ! [X26: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['61','62','63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['57','66'])).

thf('68',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['56','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('70',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('71',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(t15_lattice3,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v2_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( k11_lattice3 @ A @ B @ C )
                = ( k11_lattice3 @ A @ C @ B ) ) ) ) ) )).

thf('73',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( ( k11_lattice3 @ X16 @ X15 @ X17 )
        = ( k11_lattice3 @ X16 @ X17 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v2_lattice3 @ X16 )
      | ~ ( v5_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t15_lattice3])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X30: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('76',plain,(
    ! [X26: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('77',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['74','75','76','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','79'])).

thf('81',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['69','80'])).

thf('82',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['57','66'])).

thf('84',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['81','84'])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','10'])).

thf('89',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('91',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['86','93'])).

thf('95',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) @ sk_B )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['55','68','85','94'])).

thf('96',plain,
    ( ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
      = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['38','95'])).

thf('97',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['81','84'])).

thf('98',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
      = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['86','93'])).

thf('100',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','78'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['57','66'])).

thf('107',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['104','107'])).

thf('109',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['99','108'])).

thf('110',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('112',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( X22
       != ( k12_lattice3 @ X23 @ X22 @ X24 ) )
      | ( r3_orders_2 @ X23 @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_orders_2 @ X23 )
      | ~ ( v2_lattice3 @ X23 )
      | ~ ( v5_orders_2 @ X23 )
      | ~ ( v3_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow_0])).

thf('113',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( X1
       != ( k12_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X28: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('115',plain,(
    ! [X30: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('116',plain,(
    ! [X26: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('117',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('118',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( X1
       != ( k12_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['113','114','115','116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ X1 ) )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','118'])).

thf('120',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) )
    | ~ ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['109','119'])).

thf('121',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('122',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('123',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['120','121','122'])).

thf('124',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['98','123'])).

thf('125',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('126',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ ( k2_yellow_1 @ X34 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X34 ) @ X33 @ X35 )
      | ( r1_tarski @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ ( k2_yellow_1 @ X34 ) ) )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('127',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('128',plain,(
    ! [X31: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X31 ) )
      = X31 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('129',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ X34 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X34 ) @ X33 @ X35 )
      | ( r1_tarski @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ X34 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('130',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['125','129'])).

thf('131',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('132',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('133',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) @ sk_B )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['40','53'])).

thf('138',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['81','84'])).

thf('140',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('141',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('142',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['140','143'])).

thf('145',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['13','14'])).

thf('146',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['2','11'])).

thf('147',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['140','143'])).

thf('148',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['145','150'])).

thf('152',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['138','139','144','151'])).

thf('153',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('154',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('155',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['71','78'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['153','156'])).

thf('158',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('160',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['157','160'])).

thf('162',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) ),
    inference('sup+',[status(thm)],['152','161'])).

thf('163',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['145','150'])).

thf('164',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['2','11'])).

thf('165',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('166',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X1 ) ) ),
    inference(demod,[status(thm)],['18','19','20','21'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B )
      | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['164','167'])).

thf('169',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
      | ( X1
        = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('170',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ sk_A )
    | ( sk_B
      = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('172',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('173',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( sk_B
      = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['146','147'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('176',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
      = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['173','176'])).

thf('178',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('179',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
      = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
      = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['163','179'])).

thf('181',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
      = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['162','180'])).

thf('182',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['158','159'])).

thf('183',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['70','79'])).

thf('185',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('188',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['185','188'])).

thf('190',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['182','189'])).

thf('191',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ X1 ) )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','118'])).

thf('192',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) )
    | ~ ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('194',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('195',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['192','193','194'])).

thf('196',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['181','195'])).

thf('197',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['196'])).

thf('198',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ X34 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X34 ) @ X33 @ X35 )
      | ( r1_tarski @ X33 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ X34 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(demod,[status(thm)],['126','127','128'])).

thf('199',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ sk_A )
    | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['197','198'])).

thf('200',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('201',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('202',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['199','200','201'])).

thf('203',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['202','203'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('205',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['204','205'])).

thf('207',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['135','206'])).

thf('208',plain,
    ( ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['207'])).

thf('209',plain,(
    ~ ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('210',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('211',plain,(
    ~ ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['209','210'])).

thf('212',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference(clc,[status(thm)],['208','211'])).

thf('213',plain,(
    ! [X26: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf(cc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('214',plain,(
    ! [X8: $i] :
      ( ~ ( v2_lattice3 @ X8 )
      | ~ ( v2_struct_0 @ X8 )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_lattice3])).

thf('215',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['213','214'])).

thf('216',plain,(
    ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['212','215'])).

thf('217',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    $false ),
    inference(demod,[status(thm)],['216','217'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Hiy502ZbVe
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:14:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 12.50/12.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 12.50/12.68  % Solved by: fo/fo7.sh
% 12.50/12.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 12.50/12.68  % done 3197 iterations in 12.219s
% 12.50/12.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 12.50/12.68  % SZS output start Refutation
% 12.50/12.68  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 12.50/12.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 12.50/12.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 12.50/12.68  thf(k12_lattice3_type, type, k12_lattice3: $i > $i > $i > $i).
% 12.50/12.68  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 12.50/12.68  thf(sk_B_type, type, sk_B: $i).
% 12.50/12.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 12.50/12.68  thf(sk_C_type, type, sk_C: $i).
% 12.50/12.68  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 12.50/12.68  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 12.50/12.68  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 12.50/12.68  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 12.50/12.68  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 12.50/12.68  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 12.50/12.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 12.50/12.68  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 12.50/12.68  thf(sk_A_type, type, sk_A: $i).
% 12.50/12.68  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 12.50/12.68  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 12.50/12.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 12.50/12.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 12.50/12.68  thf(t7_yellow_1, conjecture,
% 12.50/12.68    (![A:$i]:
% 12.50/12.68     ( ( ~( v1_xboole_0 @ A ) ) =>
% 12.50/12.68       ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 12.50/12.68         ( ![B:$i]:
% 12.50/12.68           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 12.50/12.68             ( ![C:$i]:
% 12.50/12.68               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 12.50/12.68                 ( r1_tarski @
% 12.50/12.68                   ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 12.50/12.68                   ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ))).
% 12.50/12.68  thf(zf_stmt_0, negated_conjecture,
% 12.50/12.68    (~( ![A:$i]:
% 12.50/12.68        ( ( ~( v1_xboole_0 @ A ) ) =>
% 12.50/12.68          ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 12.50/12.68            ( ![B:$i]:
% 12.50/12.68              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 12.50/12.68                ( ![C:$i]:
% 12.50/12.68                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 12.50/12.68                    ( r1_tarski @
% 12.50/12.68                      ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 12.50/12.68                      ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ) )),
% 12.50/12.68    inference('cnf.neg', [status(esa)], [t7_yellow_1])).
% 12.50/12.68  thf('0', plain,
% 12.50/12.68      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 12.50/12.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.50/12.68  thf(t1_yellow_1, axiom,
% 12.50/12.68    (![A:$i]:
% 12.50/12.68     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 12.50/12.68       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 12.50/12.68  thf('1', plain, (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 12.50/12.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 12.50/12.68  thf('2', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['0', '1'])).
% 12.50/12.68  thf('3', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['0', '1'])).
% 12.50/12.68  thf('4', plain, (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 12.50/12.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 12.50/12.68  thf(dt_k11_lattice3, axiom,
% 12.50/12.68    (![A:$i,B:$i,C:$i]:
% 12.50/12.68     ( ( ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 12.50/12.68         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 12.50/12.68       ( m1_subset_1 @ ( k11_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 12.50/12.68  thf('5', plain,
% 12.50/12.68      (![X9 : $i, X10 : $i, X11 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 12.50/12.68          | ~ (l1_orders_2 @ X10)
% 12.50/12.68          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 12.50/12.68          | (m1_subset_1 @ (k11_lattice3 @ X10 @ X9 @ X11) @ 
% 12.50/12.68             (u1_struct_0 @ X10)))),
% 12.50/12.68      inference('cnf', [status(esa)], [dt_k11_lattice3])).
% 12.50/12.68  thf('6', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X1 @ X0)
% 12.50/12.68          | (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ 
% 12.50/12.68             (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 12.50/12.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 12.50/12.68          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['4', '5'])).
% 12.50/12.68  thf('7', plain, (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 12.50/12.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 12.50/12.68  thf('8', plain, (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 12.50/12.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 12.50/12.68  thf(dt_k2_yellow_1, axiom,
% 12.50/12.68    (![A:$i]:
% 12.50/12.68     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 12.50/12.68       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 12.50/12.68  thf('9', plain, (![X26 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X26))),
% 12.50/12.68      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 12.50/12.68  thf('10', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X1 @ X0)
% 12.50/12.68          | (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ X0)
% 12.50/12.68          | ~ (m1_subset_1 @ X2 @ X0))),
% 12.50/12.68      inference('demod', [status(thm)], ['6', '7', '8', '9'])).
% 12.50/12.68  thf('11', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 12.50/12.68             sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['3', '10'])).
% 12.50/12.68  thf('12', plain,
% 12.50/12.68      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B) @ 
% 12.50/12.68        sk_A)),
% 12.50/12.68      inference('sup-', [status(thm)], ['2', '11'])).
% 12.50/12.68  thf('13', plain,
% 12.50/12.68      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 12.50/12.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.50/12.68  thf('14', plain,
% 12.50/12.68      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 12.50/12.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 12.50/12.68  thf('15', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['13', '14'])).
% 12.50/12.68  thf('16', plain,
% 12.50/12.68      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 12.50/12.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 12.50/12.68  thf(reflexivity_r3_orders_2, axiom,
% 12.50/12.68    (![A:$i,B:$i,C:$i]:
% 12.50/12.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 12.50/12.68         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 12.50/12.68         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 12.50/12.68       ( r3_orders_2 @ A @ B @ B ) ))).
% 12.50/12.68  thf('17', plain,
% 12.50/12.68      (![X5 : $i, X6 : $i, X7 : $i]:
% 12.50/12.68         ((r3_orders_2 @ X5 @ X6 @ X6)
% 12.50/12.68          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X5))
% 12.50/12.68          | ~ (l1_orders_2 @ X5)
% 12.50/12.68          | ~ (v3_orders_2 @ X5)
% 12.50/12.68          | (v2_struct_0 @ X5)
% 12.50/12.68          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X5)))),
% 12.50/12.68      inference('cnf', [status(esa)], [reflexivity_r3_orders_2])).
% 12.50/12.68  thf('18', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X1 @ X0)
% 12.50/12.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 12.50/12.68          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X1))),
% 12.50/12.68      inference('sup-', [status(thm)], ['16', '17'])).
% 12.50/12.68  thf('19', plain,
% 12.50/12.68      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 12.50/12.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 12.50/12.68  thf(fc5_yellow_1, axiom,
% 12.50/12.68    (![A:$i]:
% 12.50/12.68     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 12.50/12.68       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 12.50/12.68       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 12.50/12.68       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 12.50/12.68  thf('20', plain, (![X28 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X28))),
% 12.50/12.68      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 12.50/12.68  thf('21', plain, (![X26 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X26))),
% 12.50/12.68      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 12.50/12.68  thf('22', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X1 @ X0)
% 12.50/12.68          | ~ (m1_subset_1 @ X2 @ X0)
% 12.50/12.68          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X1))),
% 12.50/12.68      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 12.50/12.68  thf('23', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C)
% 12.50/12.68          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 12.50/12.68          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['15', '22'])).
% 12.50/12.68  thf('24', plain,
% 12.50/12.68      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 12.50/12.68        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C))),
% 12.50/12.68      inference('sup-', [status(thm)], ['12', '23'])).
% 12.50/12.68  thf('25', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 12.50/12.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.50/12.68  thf('26', plain,
% 12.50/12.68      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 12.50/12.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 12.50/12.68  thf(t25_yellow_0, axiom,
% 12.50/12.68    (![A:$i]:
% 12.50/12.68     ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & 
% 12.50/12.68         ( l1_orders_2 @ A ) ) =>
% 12.50/12.68       ( ![B:$i]:
% 12.50/12.68         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 12.50/12.68           ( ![C:$i]:
% 12.50/12.68             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 12.50/12.68               ( ( ( B ) = ( k12_lattice3 @ A @ B @ C ) ) <=>
% 12.50/12.68                 ( r3_orders_2 @ A @ B @ C ) ) ) ) ) ) ))).
% 12.50/12.68  thf('27', plain,
% 12.50/12.68      (![X22 : $i, X23 : $i, X24 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 12.50/12.68          | ~ (r3_orders_2 @ X23 @ X22 @ X24)
% 12.50/12.68          | ((X22) = (k12_lattice3 @ X23 @ X22 @ X24))
% 12.50/12.68          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 12.50/12.68          | ~ (l1_orders_2 @ X23)
% 12.50/12.68          | ~ (v2_lattice3 @ X23)
% 12.50/12.68          | ~ (v5_orders_2 @ X23)
% 12.50/12.68          | ~ (v3_orders_2 @ X23))),
% 12.50/12.68      inference('cnf', [status(esa)], [t25_yellow_0])).
% 12.50/12.68  thf('28', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X1 @ X0)
% 12.50/12.68          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 12.50/12.68          | ((X1) = (k12_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2))
% 12.50/12.68          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2))),
% 12.50/12.68      inference('sup-', [status(thm)], ['26', '27'])).
% 12.50/12.68  thf('29', plain, (![X28 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X28))),
% 12.50/12.68      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 12.50/12.68  thf('30', plain, (![X30 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X30))),
% 12.50/12.68      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 12.50/12.68  thf('31', plain, (![X26 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X26))),
% 12.50/12.68      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 12.50/12.68  thf('32', plain,
% 12.50/12.68      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 12.50/12.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 12.50/12.68  thf('33', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X1 @ X0)
% 12.50/12.68          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (m1_subset_1 @ X2 @ X0)
% 12.50/12.68          | ((X1) = (k12_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2))
% 12.50/12.68          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2))),
% 12.50/12.68      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 12.50/12.68  thf('34', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i]:
% 12.50/12.68         (~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 12.50/12.68          | ((X1) = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0))
% 12.50/12.68          | ~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['25', '33'])).
% 12.50/12.68  thf('35', plain,
% 12.50/12.68      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 12.50/12.68        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 12.50/12.68        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 12.50/12.68        | ((sk_C) = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['24', '34'])).
% 12.50/12.68  thf('36', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['13', '14'])).
% 12.50/12.68  thf('37', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['13', '14'])).
% 12.50/12.68  thf('38', plain,
% 12.50/12.68      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 12.50/12.68        | ((sk_C) = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C)))),
% 12.50/12.68      inference('demod', [status(thm)], ['35', '36', '37'])).
% 12.50/12.68  thf('39', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['13', '14'])).
% 12.50/12.68  thf('40', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['13', '14'])).
% 12.50/12.68  thf('41', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['0', '1'])).
% 12.50/12.68  thf('42', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 12.50/12.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.50/12.68  thf('43', plain,
% 12.50/12.68      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 12.50/12.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 12.50/12.68  thf(t16_lattice3, axiom,
% 12.50/12.68    (![A:$i]:
% 12.50/12.68     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 12.50/12.68       ( ![B:$i]:
% 12.50/12.68         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 12.50/12.68           ( ![C:$i]:
% 12.50/12.68             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 12.50/12.68               ( ![D:$i]:
% 12.50/12.68                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 12.50/12.68                   ( ( v4_orders_2 @ A ) =>
% 12.50/12.68                     ( ( k11_lattice3 @ A @ ( k11_lattice3 @ A @ B @ C ) @ D ) =
% 12.50/12.68                       ( k11_lattice3 @ A @ B @ ( k11_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 12.50/12.68  thf('44', plain,
% 12.50/12.68      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 12.50/12.68          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 12.50/12.68          | ((k11_lattice3 @ X19 @ (k11_lattice3 @ X19 @ X18 @ X21) @ X20)
% 12.50/12.68              = (k11_lattice3 @ X19 @ X18 @ (k11_lattice3 @ X19 @ X21 @ X20)))
% 12.50/12.68          | ~ (v4_orders_2 @ X19)
% 12.50/12.68          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X19))
% 12.50/12.68          | ~ (l1_orders_2 @ X19)
% 12.50/12.68          | ~ (v2_lattice3 @ X19)
% 12.50/12.68          | ~ (v5_orders_2 @ X19))),
% 12.50/12.68      inference('cnf', [status(esa)], [t16_lattice3])).
% 12.50/12.68  thf('45', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X1 @ X0)
% 12.50/12.68          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 12.50/12.68          | ~ (v4_orders_2 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ((k11_lattice3 @ (k2_yellow_1 @ X0) @ 
% 12.50/12.68              (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ X3)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ 
% 12.50/12.68                 (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X3)))
% 12.50/12.68          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ (k2_yellow_1 @ X0))))),
% 12.50/12.68      inference('sup-', [status(thm)], ['43', '44'])).
% 12.50/12.68  thf('46', plain, (![X30 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X30))),
% 12.50/12.68      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 12.50/12.68  thf('47', plain, (![X26 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X26))),
% 12.50/12.68      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 12.50/12.68  thf('48', plain,
% 12.50/12.68      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 12.50/12.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 12.50/12.68  thf('49', plain, (![X29 : $i]: (v4_orders_2 @ (k2_yellow_1 @ X29))),
% 12.50/12.68      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 12.50/12.68  thf('50', plain,
% 12.50/12.68      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 12.50/12.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 12.50/12.68  thf('51', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X1 @ X0)
% 12.50/12.68          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (m1_subset_1 @ X2 @ X0)
% 12.50/12.68          | ((k11_lattice3 @ (k2_yellow_1 @ X0) @ 
% 12.50/12.68              (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ X3)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ 
% 12.50/12.68                 (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X3)))
% 12.50/12.68          | ~ (m1_subset_1 @ X3 @ X0))),
% 12.50/12.68      inference('demod', [status(thm)], ['45', '46', '47', '48', '49', '50'])).
% 12.50/12.68  thf('52', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68              (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X2 @ X1) @ X0)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X2 @ 
% 12.50/12.68                 (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)))
% 12.50/12.68          | ~ (m1_subset_1 @ X1 @ sk_A)
% 12.50/12.68          | ~ (m1_subset_1 @ X2 @ sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['42', '51'])).
% 12.50/12.68  thf('53', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ~ (m1_subset_1 @ X1 @ sk_A)
% 12.50/12.68          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68              (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ X1) @ sk_B)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ 
% 12.50/12.68                 (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ sk_B))))),
% 12.50/12.68      inference('sup-', [status(thm)], ['41', '52'])).
% 12.50/12.68  thf('54', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68            (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0) @ sk_B)
% 12.50/12.68            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)))
% 12.50/12.68          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['40', '53'])).
% 12.50/12.68  thf('55', plain,
% 12.50/12.68      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68         (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C) @ sk_B)
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68            (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['39', '54'])).
% 12.50/12.68  thf('56', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['13', '14'])).
% 12.50/12.68  thf('57', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['13', '14'])).
% 12.50/12.68  thf('58', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 12.50/12.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.50/12.68  thf('59', plain,
% 12.50/12.68      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 12.50/12.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 12.50/12.68  thf(redefinition_k12_lattice3, axiom,
% 12.50/12.68    (![A:$i,B:$i,C:$i]:
% 12.50/12.68     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 12.50/12.68         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 12.50/12.68         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 12.50/12.68       ( ( k12_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ B @ C ) ) ))).
% 12.50/12.68  thf('60', plain,
% 12.50/12.68      (![X12 : $i, X13 : $i, X14 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 12.50/12.68          | ~ (l1_orders_2 @ X13)
% 12.50/12.68          | ~ (v2_lattice3 @ X13)
% 12.50/12.68          | ~ (v5_orders_2 @ X13)
% 12.50/12.68          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 12.50/12.68          | ((k12_lattice3 @ X13 @ X12 @ X14)
% 12.50/12.68              = (k11_lattice3 @ X13 @ X12 @ X14)))),
% 12.50/12.68      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 12.50/12.68  thf('61', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X1 @ X0)
% 12.50/12.68          | ((k12_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2))
% 12.50/12.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 12.50/12.68          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['59', '60'])).
% 12.50/12.68  thf('62', plain,
% 12.50/12.68      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 12.50/12.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 12.50/12.68  thf('63', plain, (![X30 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X30))),
% 12.50/12.68      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 12.50/12.68  thf('64', plain, (![X26 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X26))),
% 12.50/12.68      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 12.50/12.68  thf('65', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X1 @ X0)
% 12.50/12.68          | ((k12_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2))
% 12.50/12.68          | ~ (m1_subset_1 @ X2 @ X0)
% 12.50/12.68          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0)))),
% 12.50/12.68      inference('demod', [status(thm)], ['61', '62', '63', '64'])).
% 12.50/12.68  thf('66', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0))
% 12.50/12.68          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['58', '65'])).
% 12.50/12.68  thf('67', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['57', '66'])).
% 12.50/12.68  thf('68', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C)
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C))),
% 12.50/12.68      inference('sup-', [status(thm)], ['56', '67'])).
% 12.50/12.68  thf('69', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['13', '14'])).
% 12.50/12.68  thf('70', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['0', '1'])).
% 12.50/12.68  thf('71', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 12.50/12.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.50/12.68  thf('72', plain,
% 12.50/12.68      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 12.50/12.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 12.50/12.68  thf(t15_lattice3, axiom,
% 12.50/12.68    (![A:$i]:
% 12.50/12.68     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 12.50/12.68       ( ![B:$i]:
% 12.50/12.68         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 12.50/12.68           ( ![C:$i]:
% 12.50/12.68             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 12.50/12.68               ( ( k11_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ C @ B ) ) ) ) ) ) ))).
% 12.50/12.68  thf('73', plain,
% 12.50/12.68      (![X15 : $i, X16 : $i, X17 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 12.50/12.68          | ((k11_lattice3 @ X16 @ X15 @ X17)
% 12.50/12.68              = (k11_lattice3 @ X16 @ X17 @ X15))
% 12.50/12.68          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 12.50/12.68          | ~ (l1_orders_2 @ X16)
% 12.50/12.68          | ~ (v2_lattice3 @ X16)
% 12.50/12.68          | ~ (v5_orders_2 @ X16))),
% 12.50/12.68      inference('cnf', [status(esa)], [t15_lattice3])).
% 12.50/12.68  thf('74', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X1 @ X0)
% 12.50/12.68          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 12.50/12.68          | ((k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['72', '73'])).
% 12.50/12.68  thf('75', plain, (![X30 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X30))),
% 12.50/12.68      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 12.50/12.68  thf('76', plain, (![X26 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X26))),
% 12.50/12.68      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 12.50/12.68  thf('77', plain,
% 12.50/12.68      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 12.50/12.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 12.50/12.68  thf('78', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X1 @ X0)
% 12.50/12.68          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (m1_subset_1 @ X2 @ X0)
% 12.50/12.68          | ((k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)))),
% 12.50/12.68      inference('demod', [status(thm)], ['74', '75', '76', '77'])).
% 12.50/12.68  thf('79', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i]:
% 12.50/12.68         (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 12.50/12.68            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ X1))
% 12.50/12.68          | ~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['71', '78'])).
% 12.50/12.68  thf('80', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['70', '79'])).
% 12.50/12.68  thf('81', plain,
% 12.50/12.68      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 12.50/12.68      inference('sup-', [status(thm)], ['69', '80'])).
% 12.50/12.68  thf('82', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['0', '1'])).
% 12.50/12.68  thf('83', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['57', '66'])).
% 12.50/12.68  thf('84', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 12.50/12.68      inference('sup-', [status(thm)], ['82', '83'])).
% 12.50/12.68  thf('85', plain,
% 12.50/12.68      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 12.50/12.68         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 12.50/12.68      inference('demod', [status(thm)], ['81', '84'])).
% 12.50/12.68  thf('86', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['13', '14'])).
% 12.50/12.68  thf('87', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['13', '14'])).
% 12.50/12.68  thf('88', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 12.50/12.68             sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['3', '10'])).
% 12.50/12.68  thf('89', plain,
% 12.50/12.68      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 12.50/12.68        sk_A)),
% 12.50/12.68      inference('sup-', [status(thm)], ['87', '88'])).
% 12.50/12.68  thf('90', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 12.50/12.68      inference('sup-', [status(thm)], ['82', '83'])).
% 12.50/12.68  thf('91', plain,
% 12.50/12.68      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 12.50/12.68        sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['89', '90'])).
% 12.50/12.68  thf('92', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0))
% 12.50/12.68          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['58', '65'])).
% 12.50/12.68  thf('93', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ 
% 12.50/12.68              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ 
% 12.50/12.68                 (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))))),
% 12.50/12.68      inference('sup-', [status(thm)], ['91', '92'])).
% 12.50/12.68  thf('94', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['86', '93'])).
% 12.50/12.68  thf('95', plain,
% 12.50/12.68      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C) @ sk_B)
% 12.50/12.68         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 12.50/12.68      inference('demod', [status(thm)], ['55', '68', '85', '94'])).
% 12.50/12.68  thf('96', plain,
% 12.50/12.68      ((((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 12.50/12.68          = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))
% 12.50/12.68        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 12.50/12.68      inference('sup+', [status(thm)], ['38', '95'])).
% 12.50/12.68  thf('97', plain,
% 12.50/12.68      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 12.50/12.68         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 12.50/12.68      inference('demod', [status(thm)], ['81', '84'])).
% 12.50/12.68  thf('98', plain,
% 12.50/12.68      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 12.50/12.68          = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))
% 12.50/12.68        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 12.50/12.68      inference('demod', [status(thm)], ['96', '97'])).
% 12.50/12.68  thf('99', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['86', '93'])).
% 12.50/12.68  thf('100', plain,
% 12.50/12.68      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 12.50/12.68        sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['89', '90'])).
% 12.50/12.68  thf('101', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['13', '14'])).
% 12.50/12.68  thf('102', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i]:
% 12.50/12.68         (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 12.50/12.68            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ X1))
% 12.50/12.68          | ~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['71', '78'])).
% 12.50/12.68  thf('103', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['101', '102'])).
% 12.50/12.68  thf('104', plain,
% 12.50/12.68      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['100', '103'])).
% 12.50/12.68  thf('105', plain,
% 12.50/12.68      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 12.50/12.68        sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['89', '90'])).
% 12.50/12.68  thf('106', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['57', '66'])).
% 12.50/12.68  thf('107', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 12.50/12.68      inference('sup-', [status(thm)], ['105', '106'])).
% 12.50/12.68  thf('108', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 12.50/12.68      inference('sup+', [status(thm)], ['104', '107'])).
% 12.50/12.68  thf('109', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 12.50/12.68         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 12.50/12.68      inference('sup+', [status(thm)], ['99', '108'])).
% 12.50/12.68  thf('110', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 12.50/12.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.50/12.68  thf('111', plain,
% 12.50/12.68      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 12.50/12.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 12.50/12.68  thf('112', plain,
% 12.50/12.68      (![X22 : $i, X23 : $i, X24 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 12.50/12.68          | ((X22) != (k12_lattice3 @ X23 @ X22 @ X24))
% 12.50/12.68          | (r3_orders_2 @ X23 @ X22 @ X24)
% 12.50/12.68          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 12.50/12.68          | ~ (l1_orders_2 @ X23)
% 12.50/12.68          | ~ (v2_lattice3 @ X23)
% 12.50/12.68          | ~ (v5_orders_2 @ X23)
% 12.50/12.68          | ~ (v3_orders_2 @ X23))),
% 12.50/12.68      inference('cnf', [status(esa)], [t25_yellow_0])).
% 12.50/12.68  thf('113', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X1 @ X0)
% 12.50/12.68          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 12.50/12.68          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 12.50/12.68          | ((X1) != (k12_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['111', '112'])).
% 12.50/12.68  thf('114', plain, (![X28 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X28))),
% 12.50/12.68      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 12.50/12.68  thf('115', plain, (![X30 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X30))),
% 12.50/12.68      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 12.50/12.68  thf('116', plain, (![X26 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X26))),
% 12.50/12.68      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 12.50/12.68  thf('117', plain,
% 12.50/12.68      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 12.50/12.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 12.50/12.68  thf('118', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X1 @ X0)
% 12.50/12.68          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (m1_subset_1 @ X2 @ X0)
% 12.50/12.68          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 12.50/12.68          | ((X1) != (k12_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)))),
% 12.50/12.68      inference('demod', [status(thm)], ['113', '114', '115', '116', '117'])).
% 12.50/12.68  thf('119', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i]:
% 12.50/12.68         (((X0) != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ X1))
% 12.50/12.68          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ X0 @ X1)
% 12.50/12.68          | ~ (m1_subset_1 @ X1 @ sk_A)
% 12.50/12.68          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['110', '118'])).
% 12.50/12.68  thf('120', plain,
% 12.50/12.68      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 12.50/12.68          != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))
% 12.50/12.68        | ~ (m1_subset_1 @ 
% 12.50/12.68             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 12.50/12.68        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 12.50/12.68        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 12.50/12.68      inference('sup-', [status(thm)], ['109', '119'])).
% 12.50/12.68  thf('121', plain,
% 12.50/12.68      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 12.50/12.68        sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['89', '90'])).
% 12.50/12.68  thf('122', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['13', '14'])).
% 12.50/12.68  thf('123', plain,
% 12.50/12.68      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 12.50/12.68          != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))
% 12.50/12.68        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 12.50/12.68      inference('demod', [status(thm)], ['120', '121', '122'])).
% 12.50/12.68  thf('124', plain,
% 12.50/12.68      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 12.50/12.68          != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 12.50/12.68        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 12.50/12.68        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 12.50/12.68      inference('sup-', [status(thm)], ['98', '123'])).
% 12.50/12.68  thf('125', plain,
% 12.50/12.68      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 12.50/12.68        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 12.50/12.68      inference('simplify', [status(thm)], ['124'])).
% 12.50/12.68  thf(t3_yellow_1, axiom,
% 12.50/12.68    (![A:$i]:
% 12.50/12.68     ( ( ~( v1_xboole_0 @ A ) ) =>
% 12.50/12.68       ( ![B:$i]:
% 12.50/12.68         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 12.50/12.68           ( ![C:$i]:
% 12.50/12.68             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 12.50/12.68               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 12.50/12.68                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 12.50/12.68  thf('126', plain,
% 12.50/12.68      (![X33 : $i, X34 : $i, X35 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X33 @ (u1_struct_0 @ (k2_yellow_1 @ X34)))
% 12.50/12.68          | ~ (r3_orders_2 @ (k2_yellow_1 @ X34) @ X33 @ X35)
% 12.50/12.68          | (r1_tarski @ X33 @ X35)
% 12.50/12.68          | ~ (m1_subset_1 @ X35 @ (u1_struct_0 @ (k2_yellow_1 @ X34)))
% 12.50/12.68          | (v1_xboole_0 @ X34))),
% 12.50/12.68      inference('cnf', [status(esa)], [t3_yellow_1])).
% 12.50/12.68  thf('127', plain,
% 12.50/12.68      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 12.50/12.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 12.50/12.68  thf('128', plain,
% 12.50/12.68      (![X31 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X31)) = (X31))),
% 12.50/12.68      inference('cnf', [status(esa)], [t1_yellow_1])).
% 12.50/12.68  thf('129', plain,
% 12.50/12.68      (![X33 : $i, X34 : $i, X35 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X33 @ X34)
% 12.50/12.68          | ~ (r3_orders_2 @ (k2_yellow_1 @ X34) @ X33 @ X35)
% 12.50/12.68          | (r1_tarski @ X33 @ X35)
% 12.50/12.68          | ~ (m1_subset_1 @ X35 @ X34)
% 12.50/12.68          | (v1_xboole_0 @ X34))),
% 12.50/12.68      inference('demod', [status(thm)], ['126', '127', '128'])).
% 12.50/12.68  thf('130', plain,
% 12.50/12.68      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 12.50/12.68        | (v1_xboole_0 @ sk_A)
% 12.50/12.68        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 12.50/12.68        | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 12.50/12.68           sk_C)
% 12.50/12.68        | ~ (m1_subset_1 @ 
% 12.50/12.68             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['125', '129'])).
% 12.50/12.68  thf('131', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['13', '14'])).
% 12.50/12.68  thf('132', plain,
% 12.50/12.68      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 12.50/12.68        sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['89', '90'])).
% 12.50/12.68  thf('133', plain,
% 12.50/12.68      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 12.50/12.68        | (v1_xboole_0 @ sk_A)
% 12.50/12.68        | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 12.50/12.68           sk_C))),
% 12.50/12.68      inference('demod', [status(thm)], ['130', '131', '132'])).
% 12.50/12.68  thf('134', plain, (~ (v1_xboole_0 @ sk_A)),
% 12.50/12.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.50/12.68  thf('135', plain,
% 12.50/12.68      (((r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 12.50/12.68        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 12.50/12.68      inference('clc', [status(thm)], ['133', '134'])).
% 12.50/12.68  thf('136', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['0', '1'])).
% 12.50/12.68  thf('137', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68            (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0) @ sk_B)
% 12.50/12.68            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)))
% 12.50/12.68          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['40', '53'])).
% 12.50/12.68  thf('138', plain,
% 12.50/12.68      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68         (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ sk_B)
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68            (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['136', '137'])).
% 12.50/12.68  thf('139', plain,
% 12.50/12.68      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 12.50/12.68         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 12.50/12.68      inference('demod', [status(thm)], ['81', '84'])).
% 12.50/12.68  thf('140', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['0', '1'])).
% 12.50/12.68  thf('141', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['0', '1'])).
% 12.50/12.68  thf('142', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0))
% 12.50/12.68          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['58', '65'])).
% 12.50/12.68  thf('143', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['141', '142'])).
% 12.50/12.68  thf('144', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))),
% 12.50/12.68      inference('sup-', [status(thm)], ['140', '143'])).
% 12.50/12.68  thf('145', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['13', '14'])).
% 12.50/12.68  thf('146', plain,
% 12.50/12.68      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B) @ 
% 12.50/12.68        sk_A)),
% 12.50/12.68      inference('sup-', [status(thm)], ['2', '11'])).
% 12.50/12.68  thf('147', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))),
% 12.50/12.68      inference('sup-', [status(thm)], ['140', '143'])).
% 12.50/12.68  thf('148', plain,
% 12.50/12.68      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B) @ 
% 12.50/12.68        sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['146', '147'])).
% 12.50/12.68  thf('149', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0))
% 12.50/12.68          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['58', '65'])).
% 12.50/12.68  thf('150', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ 
% 12.50/12.68              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ 
% 12.50/12.68                 (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))))),
% 12.50/12.68      inference('sup-', [status(thm)], ['148', '149'])).
% 12.50/12.68  thf('151', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['145', '150'])).
% 12.50/12.68  thf('152', plain,
% 12.50/12.68      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 12.50/12.68         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)))),
% 12.50/12.68      inference('demod', [status(thm)], ['138', '139', '144', '151'])).
% 12.50/12.68  thf('153', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['0', '1'])).
% 12.50/12.68  thf('154', plain,
% 12.50/12.68      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 12.50/12.68        sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['89', '90'])).
% 12.50/12.68  thf('155', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i]:
% 12.50/12.68         (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 12.50/12.68            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ X1))
% 12.50/12.68          | ~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['71', '78'])).
% 12.50/12.68  thf('156', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ 
% 12.50/12.68              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68                 (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['154', '155'])).
% 12.50/12.68  thf('157', plain,
% 12.50/12.68      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 12.50/12.68      inference('sup-', [status(thm)], ['153', '156'])).
% 12.50/12.68  thf('158', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['0', '1'])).
% 12.50/12.68  thf('159', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ 
% 12.50/12.68              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ 
% 12.50/12.68                 (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))))),
% 12.50/12.68      inference('sup-', [status(thm)], ['91', '92'])).
% 12.50/12.68  thf('160', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 12.50/12.68            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['158', '159'])).
% 12.50/12.68  thf('161', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 12.50/12.68      inference('demod', [status(thm)], ['157', '160'])).
% 12.50/12.68  thf('162', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 12.50/12.68         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)))),
% 12.50/12.68      inference('sup+', [status(thm)], ['152', '161'])).
% 12.50/12.68  thf('163', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['145', '150'])).
% 12.50/12.68  thf('164', plain,
% 12.50/12.68      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B) @ 
% 12.50/12.68        sk_A)),
% 12.50/12.68      inference('sup-', [status(thm)], ['2', '11'])).
% 12.50/12.68  thf('165', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['0', '1'])).
% 12.50/12.68  thf('166', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X1 @ X0)
% 12.50/12.68          | ~ (m1_subset_1 @ X2 @ X0)
% 12.50/12.68          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X1))),
% 12.50/12.68      inference('demod', [status(thm)], ['18', '19', '20', '21'])).
% 12.50/12.68  thf('167', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)
% 12.50/12.68          | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 12.50/12.68          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['165', '166'])).
% 12.50/12.68  thf('168', plain,
% 12.50/12.68      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 12.50/12.68        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))),
% 12.50/12.68      inference('sup-', [status(thm)], ['164', '167'])).
% 12.50/12.68  thf('169', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i]:
% 12.50/12.68         (~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 12.50/12.68          | ((X1) = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0))
% 12.50/12.68          | ~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['25', '33'])).
% 12.50/12.68  thf('170', plain,
% 12.50/12.68      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 12.50/12.68        | ~ (m1_subset_1 @ sk_B @ sk_A)
% 12.50/12.68        | ~ (m1_subset_1 @ sk_B @ sk_A)
% 12.50/12.68        | ((sk_B) = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['168', '169'])).
% 12.50/12.68  thf('171', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['0', '1'])).
% 12.50/12.68  thf('172', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['0', '1'])).
% 12.50/12.68  thf('173', plain,
% 12.50/12.68      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 12.50/12.68        | ((sk_B) = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)))),
% 12.50/12.68      inference('demod', [status(thm)], ['170', '171', '172'])).
% 12.50/12.68  thf('174', plain,
% 12.50/12.68      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B) @ 
% 12.50/12.68        sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['146', '147'])).
% 12.50/12.68  thf('175', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['101', '102'])).
% 12.50/12.68  thf('176', plain,
% 12.50/12.68      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B) @ sk_C)
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['174', '175'])).
% 12.50/12.68  thf('177', plain,
% 12.50/12.68      ((((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 12.50/12.68          = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)))
% 12.50/12.68        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 12.50/12.68      inference('sup+', [status(thm)], ['173', '176'])).
% 12.50/12.68  thf('178', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 12.50/12.68      inference('sup-', [status(thm)], ['82', '83'])).
% 12.50/12.68  thf('179', plain,
% 12.50/12.68      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 12.50/12.68          = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)))
% 12.50/12.68        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 12.50/12.68      inference('demod', [status(thm)], ['177', '178'])).
% 12.50/12.68  thf('180', plain,
% 12.50/12.68      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 12.50/12.68          = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 12.50/12.68             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)))
% 12.50/12.68        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 12.50/12.68      inference('sup+', [status(thm)], ['163', '179'])).
% 12.50/12.68  thf('181', plain,
% 12.50/12.68      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 12.50/12.68          = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 12.50/12.68             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))
% 12.50/12.68        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 12.50/12.68      inference('sup+', [status(thm)], ['162', '180'])).
% 12.50/12.68  thf('182', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 12.50/12.68            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['158', '159'])).
% 12.50/12.68  thf('183', plain,
% 12.50/12.68      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 12.50/12.68        sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['89', '90'])).
% 12.50/12.68  thf('184', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['70', '79'])).
% 12.50/12.68  thf('185', plain,
% 12.50/12.68      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 12.50/12.68            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['183', '184'])).
% 12.50/12.68  thf('186', plain,
% 12.50/12.68      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 12.50/12.68        sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['89', '90'])).
% 12.50/12.68  thf('187', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X0 @ sk_A)
% 12.50/12.68          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)
% 12.50/12.68              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['141', '142'])).
% 12.50/12.68  thf('188', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 12.50/12.68      inference('sup-', [status(thm)], ['186', '187'])).
% 12.50/12.68  thf('189', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 12.50/12.68            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 12.50/12.68      inference('sup+', [status(thm)], ['185', '188'])).
% 12.50/12.68  thf('190', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 12.50/12.68         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 12.50/12.68            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 12.50/12.68      inference('sup+', [status(thm)], ['182', '189'])).
% 12.50/12.68  thf('191', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i]:
% 12.50/12.68         (((X0) != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ X1))
% 12.50/12.68          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ X0 @ X1)
% 12.50/12.68          | ~ (m1_subset_1 @ X1 @ sk_A)
% 12.50/12.68          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['110', '118'])).
% 12.50/12.68  thf('192', plain,
% 12.50/12.68      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 12.50/12.68          != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 12.50/12.68              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))
% 12.50/12.68        | ~ (m1_subset_1 @ 
% 12.50/12.68             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 12.50/12.68        | ~ (m1_subset_1 @ sk_B @ sk_A)
% 12.50/12.68        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 12.50/12.68      inference('sup-', [status(thm)], ['190', '191'])).
% 12.50/12.68  thf('193', plain,
% 12.50/12.68      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 12.50/12.68        sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['89', '90'])).
% 12.50/12.68  thf('194', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['0', '1'])).
% 12.50/12.68  thf('195', plain,
% 12.50/12.68      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 12.50/12.68          != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 12.50/12.68              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))
% 12.50/12.68        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 12.50/12.68      inference('demod', [status(thm)], ['192', '193', '194'])).
% 12.50/12.68  thf('196', plain,
% 12.50/12.68      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 12.50/12.68          != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 12.50/12.68        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 12.50/12.68        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 12.50/12.68      inference('sup-', [status(thm)], ['181', '195'])).
% 12.50/12.68  thf('197', plain,
% 12.50/12.68      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 12.50/12.68         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 12.50/12.68        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 12.50/12.68      inference('simplify', [status(thm)], ['196'])).
% 12.50/12.68  thf('198', plain,
% 12.50/12.68      (![X33 : $i, X34 : $i, X35 : $i]:
% 12.50/12.68         (~ (m1_subset_1 @ X33 @ X34)
% 12.50/12.68          | ~ (r3_orders_2 @ (k2_yellow_1 @ X34) @ X33 @ X35)
% 12.50/12.68          | (r1_tarski @ X33 @ X35)
% 12.50/12.68          | ~ (m1_subset_1 @ X35 @ X34)
% 12.50/12.68          | (v1_xboole_0 @ X34))),
% 12.50/12.68      inference('demod', [status(thm)], ['126', '127', '128'])).
% 12.50/12.68  thf('199', plain,
% 12.50/12.68      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 12.50/12.68        | (v1_xboole_0 @ sk_A)
% 12.50/12.68        | ~ (m1_subset_1 @ sk_B @ sk_A)
% 12.50/12.68        | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 12.50/12.68           sk_B)
% 12.50/12.68        | ~ (m1_subset_1 @ 
% 12.50/12.68             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['197', '198'])).
% 12.50/12.68  thf('200', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['0', '1'])).
% 12.50/12.68  thf('201', plain,
% 12.50/12.68      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 12.50/12.68        sk_A)),
% 12.50/12.68      inference('demod', [status(thm)], ['89', '90'])).
% 12.50/12.68  thf('202', plain,
% 12.50/12.68      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 12.50/12.68        | (v1_xboole_0 @ sk_A)
% 12.50/12.68        | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 12.50/12.68           sk_B))),
% 12.50/12.68      inference('demod', [status(thm)], ['199', '200', '201'])).
% 12.50/12.68  thf('203', plain, (~ (v1_xboole_0 @ sk_A)),
% 12.50/12.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.50/12.68  thf('204', plain,
% 12.50/12.68      (((r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 12.50/12.68        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 12.50/12.68      inference('clc', [status(thm)], ['202', '203'])).
% 12.50/12.68  thf(t19_xboole_1, axiom,
% 12.50/12.68    (![A:$i,B:$i,C:$i]:
% 12.50/12.68     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 12.50/12.68       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 12.50/12.68  thf('205', plain,
% 12.50/12.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 12.50/12.68         (~ (r1_tarski @ X0 @ X1)
% 12.50/12.68          | ~ (r1_tarski @ X0 @ X2)
% 12.50/12.68          | (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 12.50/12.68      inference('cnf', [status(esa)], [t19_xboole_1])).
% 12.50/12.68  thf('206', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 12.50/12.68          | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 12.50/12.68             (k3_xboole_0 @ sk_B @ X0))
% 12.50/12.68          | ~ (r1_tarski @ 
% 12.50/12.68               (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))),
% 12.50/12.68      inference('sup-', [status(thm)], ['204', '205'])).
% 12.50/12.68  thf('207', plain,
% 12.50/12.68      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 12.50/12.68        | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 12.50/12.68           (k3_xboole_0 @ sk_B @ sk_C))
% 12.50/12.68        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['135', '206'])).
% 12.50/12.68  thf('208', plain,
% 12.50/12.68      (((r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 12.50/12.68         (k3_xboole_0 @ sk_B @ sk_C))
% 12.50/12.68        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 12.50/12.68      inference('simplify', [status(thm)], ['207'])).
% 12.50/12.68  thf('209', plain,
% 12.50/12.68      (~ (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 12.50/12.68          (k3_xboole_0 @ sk_B @ sk_C))),
% 12.50/12.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.50/12.68  thf('210', plain,
% 12.50/12.68      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 12.50/12.68         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 12.50/12.68      inference('sup-', [status(thm)], ['82', '83'])).
% 12.50/12.68  thf('211', plain,
% 12.50/12.68      (~ (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 12.50/12.68          (k3_xboole_0 @ sk_B @ sk_C))),
% 12.50/12.68      inference('demod', [status(thm)], ['209', '210'])).
% 12.50/12.68  thf('212', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 12.50/12.68      inference('clc', [status(thm)], ['208', '211'])).
% 12.50/12.68  thf('213', plain, (![X26 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X26))),
% 12.50/12.68      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 12.50/12.68  thf(cc2_lattice3, axiom,
% 12.50/12.68    (![A:$i]:
% 12.50/12.68     ( ( l1_orders_2 @ A ) =>
% 12.50/12.68       ( ( v2_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 12.50/12.68  thf('214', plain,
% 12.50/12.68      (![X8 : $i]:
% 12.50/12.68         (~ (v2_lattice3 @ X8) | ~ (v2_struct_0 @ X8) | ~ (l1_orders_2 @ X8))),
% 12.50/12.68      inference('cnf', [status(esa)], [cc2_lattice3])).
% 12.50/12.68  thf('215', plain,
% 12.50/12.68      (![X0 : $i]:
% 12.50/12.68         (~ (v2_struct_0 @ (k2_yellow_1 @ X0))
% 12.50/12.68          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0)))),
% 12.50/12.68      inference('sup-', [status(thm)], ['213', '214'])).
% 12.50/12.68  thf('216', plain, (~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 12.50/12.68      inference('sup-', [status(thm)], ['212', '215'])).
% 12.50/12.68  thf('217', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 12.50/12.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 12.50/12.68  thf('218', plain, ($false), inference('demod', [status(thm)], ['216', '217'])).
% 12.50/12.68  
% 12.50/12.68  % SZS output end Refutation
% 12.50/12.68  
% 12.50/12.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
