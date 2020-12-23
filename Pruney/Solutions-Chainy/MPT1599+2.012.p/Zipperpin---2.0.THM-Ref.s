%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fWOsLh7n3S

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:07 EST 2020

% Result     : Theorem 27.12s
% Output     : Refutation 27.12s
% Verified   : 
% Statistics : Number of formulae       :  260 (5828 expanded)
%              Number of leaves         :   32 (1917 expanded)
%              Depth                    :   25
%              Number of atoms          : 2783 (73194 expanded)
%              Number of equality atoms :  128 (3586 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k12_lattice3_type,type,(
    k12_lattice3: $i > $i > $i > $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ! [X30: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ! [X30: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X30: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) )
      = X30 ) ),
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

thf('9',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v2_lattice3 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( ( k12_lattice3 @ X12 @ X11 @ X13 )
        = ( k11_lattice3 @ X12 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k12_lattice3])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X30: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X29: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['10','11','12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('20',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X30: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) )
      = X30 ) ),
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

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( ( k11_lattice3 @ X15 @ X14 @ X16 )
        = ( k11_lattice3 @ X15 @ X16 @ X14 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v2_lattice3 @ X15 )
      | ~ ( v5_orders_2 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t15_lattice3])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X29: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('25',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('26',plain,(
    ! [X30: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['23','24','25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['17','30'])).

thf('32',plain,(
    ~ ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['0','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['17','30'])).

thf('39',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['32','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('44',plain,(
    ! [X30: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k11_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k11_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('45',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( m1_subset_1 @ ( k11_lattice3 @ X9 @ X8 @ X10 ) @ ( u1_struct_0 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_lattice3])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X30: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('48',plain,(
    ! [X30: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('49',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','50'])).

thf('52',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['42','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) ) @ sk_A ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('59',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('62',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) ) )
      | ~ ( r1_tarski @ X32 @ X34 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X33 ) @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) ) )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('63',plain,(
    ! [X30: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('64',plain,(
    ! [X30: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('65',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ X33 )
      | ~ ( r1_tarski @ X32 @ X34 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X33 ) @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','65'])).

thf('67',plain,
    ( ~ ( r1_tarski @ sk_C @ sk_C )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('69',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','69'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X30: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) )
      = X30 ) ),
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

thf('75',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ~ ( r3_orders_2 @ X22 @ X21 @ X23 )
      | ( X21
        = ( k12_lattice3 @ X22 @ X21 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v2_lattice3 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow_0])).

thf('76',plain,(
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
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X27: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('78',plain,(
    ! [X29: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('79',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('80',plain,(
    ! [X30: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( X1
        = ( k12_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) ) ),
    inference(demod,[status(thm)],['76','77','78','79','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
      | ( X1
        = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','81'])).

thf('83',plain,
    ( ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( sk_C
      = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) ) ),
    inference('sup-',[status(thm)],['72','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('85',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('86',plain,
    ( sk_C
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( sk_C
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['59','86'])).

thf('88',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['17','30'])).

thf('89',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['56','87','88'])).

thf('90',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('91',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','93'])).

thf('95',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('97',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('100',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['100','103'])).

thf('105',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['17','30'])).

thf('106',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['17','30'])).

thf('107',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['104','105','106'])).

thf('108',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('109',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('110',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['107','108','109'])).

thf('111',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['97','110'])).

thf('112',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['94','111'])).

thf('113',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X30: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('115',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( X21
       != ( k12_lattice3 @ X22 @ X21 @ X23 ) )
      | ( r3_orders_2 @ X22 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v2_lattice3 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t25_yellow_0])).

thf('116',plain,(
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
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X27: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('118',plain,(
    ! [X29: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('119',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('120',plain,(
    ! [X30: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('121',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( X1
       != ( k12_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['116','117','118','119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ X1 ) )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','121'])).

thf('123',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) )
    | ~ ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['112','122'])).

thf('124',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('125',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('126',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('128',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('129',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('130',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X30: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) )
      = X30 ) ),
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

thf('132',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( ( k11_lattice3 @ X18 @ ( k11_lattice3 @ X18 @ X17 @ X20 ) @ X19 )
        = ( k11_lattice3 @ X18 @ X17 @ ( k11_lattice3 @ X18 @ X20 @ X19 ) ) )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v2_lattice3 @ X18 )
      | ~ ( v5_orders_2 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t16_lattice3])).

thf('133',plain,(
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
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X29: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('135',plain,(
    ! [X25: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('136',plain,(
    ! [X30: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('137',plain,(
    ! [X28: $i] :
      ( v4_orders_2 @ ( k2_yellow_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('138',plain,(
    ! [X30: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('139',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ X3 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X3 ) ) )
      | ~ ( m1_subset_1 @ X3 @ X0 ) ) ),
    inference(demod,[status(thm)],['133','134','135','136','137','138'])).

thf('140',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X2 @ X1 ) @ X0 )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X2 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['130','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ X1 ) @ sk_B )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['129','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) @ sk_B )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['128','141'])).

thf('143',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','142'])).

thf('144',plain,
    ( sk_C
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_C ) ),
    inference(demod,[status(thm)],['59','86'])).

thf('145',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['3','16'])).

thf('146',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('147',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','93'])).

thf('149',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['143','144','147','148'])).

thf('150',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('151',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['149','150'])).

thf('152',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['126','151'])).

thf('153',plain,(
    r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ),
    inference(simplify,[status(thm)],['152'])).

thf('154',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X33 ) @ X32 @ X34 )
      | ( r1_tarski @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ ( k2_yellow_1 @ X33 ) ) )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('155',plain,(
    ! [X30: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('156',plain,(
    ! [X30: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) )
      = X30 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('157',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ X33 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X33 ) @ X32 @ X34 )
      | ( r1_tarski @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('158',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['153','157'])).

thf('159',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['1','2'])).

thf('160',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('161',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['158','159','160'])).

thf('162',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ),
    inference(clc,[status(thm)],['161','162'])).

thf('164',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('166',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('169',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['98','99'])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('172',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['17','30'])).

thf('174',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['17','30'])).

thf('175',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) ) ),
    inference(demod,[status(thm)],['172','173','174'])).

thf('176',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('177',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('178',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['169','178'])).

thf('180',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['166','179'])).

thf('181',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ X1 ) )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['113','121'])).

thf('182',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) )
    | ~ ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('184',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('185',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['182','183','184'])).

thf('186',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ X0 ) @ sk_B )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['128','141'])).

thf('188',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['186','187'])).

thf('189',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('190',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('191',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B )
        = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('192',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('194',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('195',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ X33 )
      | ~ ( r1_tarski @ X32 @ X34 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X33 ) @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['194','195'])).

thf('197',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_B )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['193','196'])).

thf('198',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['68'])).

thf('199',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ),
    inference(clc,[status(thm)],['199','200'])).

thf('202',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
      | ( X1
        = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','81'])).

thf('203',plain,
    ( ~ ( m1_subset_1 @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ sk_A )
    | ( sk_B
      = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('205',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('206',plain,
    ( sk_B
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['203','204','205'])).

thf('207',plain,
    ( sk_B
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_B ) ),
    inference(demod,[status(thm)],['192','206'])).

thf('208',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('209',plain,
    ( ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['188','189','207','208'])).

thf('210',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('211',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['166','179'])).

thf('212',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['210','211'])).

thf('213',plain,
    ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    = ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup+',[status(thm)],['209','212'])).

thf('214',plain,
    ( ( ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
     != ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['185','213'])).

thf('215',plain,(
    r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ X33 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X33 ) @ X32 @ X34 )
      | ( r1_tarski @ X32 @ X34 )
      | ~ ( m1_subset_1 @ X34 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(demod,[status(thm)],['154','155','156'])).

thf('217',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ sk_A )
    | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['215','216'])).

thf('218',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['4','5'])).

thf('219',plain,(
    m1_subset_1 @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['89','90'])).

thf('220',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['217','218','219'])).

thf('221',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('222',plain,(
    r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ),
    inference(clc,[status(thm)],['220','221'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('223',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ( r1_tarski @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    r1_tarski @ ( k12_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['163','224'])).

thf('226',plain,(
    $false ),
    inference(demod,[status(thm)],['40','225'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fWOsLh7n3S
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:56:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 27.12/27.34  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 27.12/27.34  % Solved by: fo/fo7.sh
% 27.12/27.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 27.12/27.34  % done 2889 iterations in 26.892s
% 27.12/27.34  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 27.12/27.34  % SZS output start Refutation
% 27.12/27.34  thf(sk_C_type, type, sk_C: $i).
% 27.12/27.34  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 27.12/27.34  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 27.12/27.34  thf(sk_B_type, type, sk_B: $i).
% 27.12/27.34  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 27.12/27.34  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 27.12/27.34  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 27.12/27.34  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 27.12/27.34  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 27.12/27.34  thf(k12_lattice3_type, type, k12_lattice3: $i > $i > $i > $i).
% 27.12/27.34  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 27.12/27.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 27.12/27.34  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 27.12/27.34  thf(sk_A_type, type, sk_A: $i).
% 27.12/27.34  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 27.12/27.34  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 27.12/27.34  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 27.12/27.34  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 27.12/27.34  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 27.12/27.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 27.12/27.34  thf(t7_yellow_1, conjecture,
% 27.12/27.34    (![A:$i]:
% 27.12/27.34     ( ( ~( v1_xboole_0 @ A ) ) =>
% 27.12/27.34       ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 27.12/27.34         ( ![B:$i]:
% 27.12/27.34           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 27.12/27.34             ( ![C:$i]:
% 27.12/27.34               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 27.12/27.34                 ( r1_tarski @
% 27.12/27.34                   ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 27.12/27.34                   ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ))).
% 27.12/27.34  thf(zf_stmt_0, negated_conjecture,
% 27.12/27.34    (~( ![A:$i]:
% 27.12/27.34        ( ( ~( v1_xboole_0 @ A ) ) =>
% 27.12/27.34          ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 27.12/27.34            ( ![B:$i]:
% 27.12/27.34              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 27.12/27.34                ( ![C:$i]:
% 27.12/27.34                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 27.12/27.34                    ( r1_tarski @
% 27.12/27.34                      ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 27.12/27.34                      ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ) )),
% 27.12/27.34    inference('cnf.neg', [status(esa)], [t7_yellow_1])).
% 27.12/27.34  thf('0', plain,
% 27.12/27.34      (~ (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 27.12/27.34          (k3_xboole_0 @ sk_B @ sk_C))),
% 27.12/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.12/27.34  thf('1', plain,
% 27.12/27.34      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 27.12/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.12/27.34  thf(t1_yellow_1, axiom,
% 27.12/27.34    (![A:$i]:
% 27.12/27.34     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 27.12/27.34       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 27.12/27.34  thf('2', plain, (![X30 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X30)) = (X30))),
% 27.12/27.34      inference('cnf', [status(esa)], [t1_yellow_1])).
% 27.12/27.34  thf('3', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['1', '2'])).
% 27.12/27.34  thf('4', plain,
% 27.12/27.34      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 27.12/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.12/27.34  thf('5', plain, (![X30 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X30)) = (X30))),
% 27.12/27.34      inference('cnf', [status(esa)], [t1_yellow_1])).
% 27.12/27.34  thf('6', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['4', '5'])).
% 27.12/27.34  thf('7', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 27.12/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.12/27.34  thf('8', plain, (![X30 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X30)) = (X30))),
% 27.12/27.34      inference('cnf', [status(esa)], [t1_yellow_1])).
% 27.12/27.34  thf(redefinition_k12_lattice3, axiom,
% 27.12/27.34    (![A:$i,B:$i,C:$i]:
% 27.12/27.34     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 27.12/27.34         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 27.12/27.34         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 27.12/27.34       ( ( k12_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ B @ C ) ) ))).
% 27.12/27.34  thf('9', plain,
% 27.12/27.34      (![X11 : $i, X12 : $i, X13 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 27.12/27.34          | ~ (l1_orders_2 @ X12)
% 27.12/27.34          | ~ (v2_lattice3 @ X12)
% 27.12/27.34          | ~ (v5_orders_2 @ X12)
% 27.12/27.34          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 27.12/27.34          | ((k12_lattice3 @ X12 @ X11 @ X13)
% 27.12/27.34              = (k11_lattice3 @ X12 @ X11 @ X13)))),
% 27.12/27.34      inference('cnf', [status(esa)], [redefinition_k12_lattice3])).
% 27.12/27.34  thf('10', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X1 @ X0)
% 27.12/27.34          | ((k12_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2))
% 27.12/27.34          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 27.12/27.34          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['8', '9'])).
% 27.12/27.34  thf('11', plain,
% 27.12/27.34      (![X30 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X30)) = (X30))),
% 27.12/27.34      inference('cnf', [status(esa)], [t1_yellow_1])).
% 27.12/27.34  thf(fc5_yellow_1, axiom,
% 27.12/27.34    (![A:$i]:
% 27.12/27.34     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 27.12/27.34       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 27.12/27.34       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 27.12/27.34       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 27.12/27.34  thf('12', plain, (![X29 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X29))),
% 27.12/27.34      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 27.12/27.34  thf(dt_k2_yellow_1, axiom,
% 27.12/27.34    (![A:$i]:
% 27.12/27.34     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 27.12/27.34       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 27.12/27.34  thf('13', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 27.12/27.34      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 27.12/27.34  thf('14', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X1 @ X0)
% 27.12/27.34          | ((k12_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2))
% 27.12/27.34          | ~ (m1_subset_1 @ X2 @ X0)
% 27.12/27.34          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0)))),
% 27.12/27.34      inference('demod', [status(thm)], ['10', '11', '12', '13'])).
% 27.12/27.34  thf('15', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0))
% 27.12/27.34          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 27.12/27.34      inference('sup-', [status(thm)], ['7', '14'])).
% 27.12/27.34  thf('16', plain,
% 27.12/27.34      (![X0 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['6', '15'])).
% 27.12/27.34  thf('17', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B))),
% 27.12/27.34      inference('sup-', [status(thm)], ['3', '16'])).
% 27.12/27.34  thf('18', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['1', '2'])).
% 27.12/27.34  thf('19', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['4', '5'])).
% 27.12/27.34  thf('20', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 27.12/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.12/27.34  thf('21', plain,
% 27.12/27.34      (![X30 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X30)) = (X30))),
% 27.12/27.34      inference('cnf', [status(esa)], [t1_yellow_1])).
% 27.12/27.34  thf(t15_lattice3, axiom,
% 27.12/27.34    (![A:$i]:
% 27.12/27.34     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 27.12/27.34       ( ![B:$i]:
% 27.12/27.34         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 27.12/27.34           ( ![C:$i]:
% 27.12/27.34             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 27.12/27.34               ( ( k11_lattice3 @ A @ B @ C ) = ( k11_lattice3 @ A @ C @ B ) ) ) ) ) ) ))).
% 27.12/27.34  thf('22', plain,
% 27.12/27.34      (![X14 : $i, X15 : $i, X16 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 27.12/27.34          | ((k11_lattice3 @ X15 @ X14 @ X16)
% 27.12/27.34              = (k11_lattice3 @ X15 @ X16 @ X14))
% 27.12/27.34          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 27.12/27.34          | ~ (l1_orders_2 @ X15)
% 27.12/27.34          | ~ (v2_lattice3 @ X15)
% 27.12/27.34          | ~ (v5_orders_2 @ X15))),
% 27.12/27.34      inference('cnf', [status(esa)], [t15_lattice3])).
% 27.12/27.34  thf('23', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X1 @ X0)
% 27.12/27.34          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 27.12/27.34          | ((k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['21', '22'])).
% 27.12/27.34  thf('24', plain, (![X29 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X29))),
% 27.12/27.34      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 27.12/27.34  thf('25', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 27.12/27.34      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 27.12/27.34  thf('26', plain,
% 27.12/27.34      (![X30 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X30)) = (X30))),
% 27.12/27.34      inference('cnf', [status(esa)], [t1_yellow_1])).
% 27.12/27.34  thf('27', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X1 @ X0)
% 27.12/27.34          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ~ (m1_subset_1 @ X2 @ X0)
% 27.12/27.34          | ((k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)))),
% 27.12/27.34      inference('demod', [status(thm)], ['23', '24', '25', '26'])).
% 27.12/27.34  thf('28', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i]:
% 27.12/27.34         (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 27.12/27.34            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ X1))
% 27.12/27.34          | ~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 27.12/27.34      inference('sup-', [status(thm)], ['20', '27'])).
% 27.12/27.34  thf('29', plain,
% 27.12/27.34      (![X0 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['19', '28'])).
% 27.12/27.34  thf('30', plain,
% 27.12/27.34      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 27.12/27.34      inference('sup-', [status(thm)], ['18', '29'])).
% 27.12/27.34  thf('31', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 27.12/27.34      inference('sup+', [status(thm)], ['17', '30'])).
% 27.12/27.34  thf('32', plain,
% 27.12/27.34      (~ (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ 
% 27.12/27.34          (k3_xboole_0 @ sk_B @ sk_C))),
% 27.12/27.34      inference('demod', [status(thm)], ['0', '31'])).
% 27.12/27.34  thf('33', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['4', '5'])).
% 27.12/27.34  thf('34', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['1', '2'])).
% 27.12/27.34  thf('35', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0))
% 27.12/27.34          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 27.12/27.34      inference('sup-', [status(thm)], ['7', '14'])).
% 27.12/27.34  thf('36', plain,
% 27.12/27.34      (![X0 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['34', '35'])).
% 27.12/27.34  thf('37', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 27.12/27.34      inference('sup-', [status(thm)], ['33', '36'])).
% 27.12/27.34  thf('38', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 27.12/27.34      inference('sup+', [status(thm)], ['17', '30'])).
% 27.12/27.34  thf('39', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 27.12/27.34         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 27.12/27.34      inference('sup+', [status(thm)], ['37', '38'])).
% 27.12/27.34  thf('40', plain,
% 27.12/27.34      (~ (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 27.12/27.34          (k3_xboole_0 @ sk_B @ sk_C))),
% 27.12/27.34      inference('demod', [status(thm)], ['32', '39'])).
% 27.12/27.34  thf('41', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['1', '2'])).
% 27.12/27.34  thf('42', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['1', '2'])).
% 27.12/27.34  thf('43', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['1', '2'])).
% 27.12/27.34  thf('44', plain,
% 27.12/27.34      (![X30 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X30)) = (X30))),
% 27.12/27.34      inference('cnf', [status(esa)], [t1_yellow_1])).
% 27.12/27.34  thf(dt_k11_lattice3, axiom,
% 27.12/27.34    (![A:$i,B:$i,C:$i]:
% 27.12/27.34     ( ( ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 27.12/27.34         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 27.12/27.34       ( m1_subset_1 @ ( k11_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 27.12/27.34  thf('45', plain,
% 27.12/27.34      (![X8 : $i, X9 : $i, X10 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 27.12/27.34          | ~ (l1_orders_2 @ X9)
% 27.12/27.34          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 27.12/27.34          | (m1_subset_1 @ (k11_lattice3 @ X9 @ X8 @ X10) @ (u1_struct_0 @ X9)))),
% 27.12/27.34      inference('cnf', [status(esa)], [dt_k11_lattice3])).
% 27.12/27.34  thf('46', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X1 @ X0)
% 27.12/27.34          | (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ 
% 27.12/27.34             (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 27.12/27.34          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 27.12/27.34          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['44', '45'])).
% 27.12/27.34  thf('47', plain,
% 27.12/27.34      (![X30 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X30)) = (X30))),
% 27.12/27.34      inference('cnf', [status(esa)], [t1_yellow_1])).
% 27.12/27.34  thf('48', plain,
% 27.12/27.34      (![X30 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X30)) = (X30))),
% 27.12/27.34      inference('cnf', [status(esa)], [t1_yellow_1])).
% 27.12/27.34  thf('49', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 27.12/27.34      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 27.12/27.34  thf('50', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X1 @ X0)
% 27.12/27.34          | (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ X0)
% 27.12/27.34          | ~ (m1_subset_1 @ X2 @ X0))),
% 27.12/27.34      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 27.12/27.34  thf('51', plain,
% 27.12/27.34      (![X0 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0) @ 
% 27.12/27.34             sk_A))),
% 27.12/27.34      inference('sup-', [status(thm)], ['43', '50'])).
% 27.12/27.34  thf('52', plain,
% 27.12/27.34      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C) @ 
% 27.12/27.34        sk_A)),
% 27.12/27.34      inference('sup-', [status(thm)], ['42', '51'])).
% 27.12/27.34  thf('53', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['4', '5'])).
% 27.12/27.34  thf('54', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X1 @ X0)
% 27.12/27.34          | (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ X0)
% 27.12/27.34          | ~ (m1_subset_1 @ X2 @ X0))),
% 27.12/27.34      inference('demod', [status(thm)], ['46', '47', '48', '49'])).
% 27.12/27.34  thf('55', plain,
% 27.12/27.34      (![X0 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 27.12/27.34             sk_A))),
% 27.12/27.34      inference('sup-', [status(thm)], ['53', '54'])).
% 27.12/27.34  thf('56', plain,
% 27.12/27.34      ((m1_subset_1 @ 
% 27.12/27.34        (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 27.12/27.34         (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C)) @ 
% 27.12/27.34        sk_A)),
% 27.12/27.34      inference('sup-', [status(thm)], ['52', '55'])).
% 27.12/27.34  thf('57', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['1', '2'])).
% 27.12/27.34  thf('58', plain,
% 27.12/27.34      (![X0 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['34', '35'])).
% 27.12/27.34  thf('59', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C))),
% 27.12/27.34      inference('sup-', [status(thm)], ['57', '58'])).
% 27.12/27.34  thf('60', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['1', '2'])).
% 27.12/27.34  thf('61', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['1', '2'])).
% 27.12/27.34  thf(t3_yellow_1, axiom,
% 27.12/27.34    (![A:$i]:
% 27.12/27.34     ( ( ~( v1_xboole_0 @ A ) ) =>
% 27.12/27.34       ( ![B:$i]:
% 27.12/27.34         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 27.12/27.34           ( ![C:$i]:
% 27.12/27.34             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 27.12/27.34               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 27.12/27.34                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 27.12/27.34  thf('62', plain,
% 27.12/27.34      (![X32 : $i, X33 : $i, X34 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ (k2_yellow_1 @ X33)))
% 27.12/27.34          | ~ (r1_tarski @ X32 @ X34)
% 27.12/27.34          | (r3_orders_2 @ (k2_yellow_1 @ X33) @ X32 @ X34)
% 27.12/27.34          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ (k2_yellow_1 @ X33)))
% 27.12/27.34          | (v1_xboole_0 @ X33))),
% 27.12/27.34      inference('cnf', [status(esa)], [t3_yellow_1])).
% 27.12/27.34  thf('63', plain,
% 27.12/27.34      (![X30 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X30)) = (X30))),
% 27.12/27.34      inference('cnf', [status(esa)], [t1_yellow_1])).
% 27.12/27.34  thf('64', plain,
% 27.12/27.34      (![X30 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X30)) = (X30))),
% 27.12/27.34      inference('cnf', [status(esa)], [t1_yellow_1])).
% 27.12/27.34  thf('65', plain,
% 27.12/27.34      (![X32 : $i, X33 : $i, X34 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X32 @ X33)
% 27.12/27.34          | ~ (r1_tarski @ X32 @ X34)
% 27.12/27.34          | (r3_orders_2 @ (k2_yellow_1 @ X33) @ X32 @ X34)
% 27.12/27.34          | ~ (m1_subset_1 @ X34 @ X33)
% 27.12/27.34          | (v1_xboole_0 @ X33))),
% 27.12/27.34      inference('demod', [status(thm)], ['62', '63', '64'])).
% 27.12/27.34  thf('66', plain,
% 27.12/27.34      (![X0 : $i]:
% 27.12/27.34         ((v1_xboole_0 @ sk_A)
% 27.12/27.34          | ~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0)
% 27.12/27.34          | ~ (r1_tarski @ sk_C @ X0))),
% 27.12/27.34      inference('sup-', [status(thm)], ['61', '65'])).
% 27.12/27.34  thf('67', plain,
% 27.12/27.34      ((~ (r1_tarski @ sk_C @ sk_C)
% 27.12/27.34        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C)
% 27.12/27.34        | (v1_xboole_0 @ sk_A))),
% 27.12/27.34      inference('sup-', [status(thm)], ['60', '66'])).
% 27.12/27.34  thf(d10_xboole_0, axiom,
% 27.12/27.34    (![A:$i,B:$i]:
% 27.12/27.34     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 27.12/27.34  thf('68', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 27.12/27.34      inference('cnf', [status(esa)], [d10_xboole_0])).
% 27.12/27.34  thf('69', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 27.12/27.34      inference('simplify', [status(thm)], ['68'])).
% 27.12/27.34  thf('70', plain,
% 27.12/27.34      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C)
% 27.12/27.34        | (v1_xboole_0 @ sk_A))),
% 27.12/27.34      inference('demod', [status(thm)], ['67', '69'])).
% 27.12/27.34  thf('71', plain, (~ (v1_xboole_0 @ sk_A)),
% 27.12/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.12/27.34  thf('72', plain, ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C)),
% 27.12/27.34      inference('clc', [status(thm)], ['70', '71'])).
% 27.12/27.34  thf('73', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 27.12/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.12/27.34  thf('74', plain,
% 27.12/27.34      (![X30 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X30)) = (X30))),
% 27.12/27.34      inference('cnf', [status(esa)], [t1_yellow_1])).
% 27.12/27.34  thf(t25_yellow_0, axiom,
% 27.12/27.34    (![A:$i]:
% 27.12/27.34     ( ( ( v3_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & 
% 27.12/27.34         ( l1_orders_2 @ A ) ) =>
% 27.12/27.34       ( ![B:$i]:
% 27.12/27.34         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 27.12/27.34           ( ![C:$i]:
% 27.12/27.34             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 27.12/27.34               ( ( ( B ) = ( k12_lattice3 @ A @ B @ C ) ) <=>
% 27.12/27.34                 ( r3_orders_2 @ A @ B @ C ) ) ) ) ) ) ))).
% 27.12/27.34  thf('75', plain,
% 27.12/27.34      (![X21 : $i, X22 : $i, X23 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 27.12/27.34          | ~ (r3_orders_2 @ X22 @ X21 @ X23)
% 27.12/27.34          | ((X21) = (k12_lattice3 @ X22 @ X21 @ X23))
% 27.12/27.34          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 27.12/27.34          | ~ (l1_orders_2 @ X22)
% 27.12/27.34          | ~ (v2_lattice3 @ X22)
% 27.12/27.34          | ~ (v5_orders_2 @ X22)
% 27.12/27.34          | ~ (v3_orders_2 @ X22))),
% 27.12/27.34      inference('cnf', [status(esa)], [t25_yellow_0])).
% 27.12/27.34  thf('76', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X1 @ X0)
% 27.12/27.34          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 27.12/27.34          | ((X1) = (k12_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2))
% 27.12/27.34          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2))),
% 27.12/27.34      inference('sup-', [status(thm)], ['74', '75'])).
% 27.12/27.34  thf('77', plain, (![X27 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X27))),
% 27.12/27.34      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 27.12/27.34  thf('78', plain, (![X29 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X29))),
% 27.12/27.34      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 27.12/27.34  thf('79', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 27.12/27.34      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 27.12/27.34  thf('80', plain,
% 27.12/27.34      (![X30 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X30)) = (X30))),
% 27.12/27.34      inference('cnf', [status(esa)], [t1_yellow_1])).
% 27.12/27.34  thf('81', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X1 @ X0)
% 27.12/27.34          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ~ (m1_subset_1 @ X2 @ X0)
% 27.12/27.34          | ((X1) = (k12_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2))
% 27.12/27.34          | ~ (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2))),
% 27.12/27.34      inference('demod', [status(thm)], ['76', '77', '78', '79', '80'])).
% 27.12/27.34  thf('82', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i]:
% 27.12/27.34         (~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 27.12/27.34          | ((X1) = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0))
% 27.12/27.34          | ~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 27.12/27.34      inference('sup-', [status(thm)], ['73', '81'])).
% 27.12/27.34  thf('83', plain,
% 27.12/27.34      ((~ (m1_subset_1 @ sk_C @ sk_A)
% 27.12/27.34        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 27.12/27.34        | ((sk_C) = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['72', '82'])).
% 27.12/27.34  thf('84', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['1', '2'])).
% 27.12/27.34  thf('85', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['1', '2'])).
% 27.12/27.34  thf('86', plain,
% 27.12/27.34      (((sk_C) = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C))),
% 27.12/27.34      inference('demod', [status(thm)], ['83', '84', '85'])).
% 27.12/27.34  thf('87', plain,
% 27.12/27.34      (((sk_C) = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C))),
% 27.12/27.34      inference('demod', [status(thm)], ['59', '86'])).
% 27.12/27.34  thf('88', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 27.12/27.34      inference('sup+', [status(thm)], ['17', '30'])).
% 27.12/27.34  thf('89', plain,
% 27.12/27.34      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ 
% 27.12/27.34        sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['56', '87', '88'])).
% 27.12/27.34  thf('90', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 27.12/27.34         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 27.12/27.34      inference('sup+', [status(thm)], ['37', '38'])).
% 27.12/27.34  thf('91', plain,
% 27.12/27.34      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 27.12/27.34        sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['89', '90'])).
% 27.12/27.34  thf('92', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0))
% 27.12/27.34          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 27.12/27.34      inference('sup-', [status(thm)], ['7', '14'])).
% 27.12/27.34  thf('93', plain,
% 27.12/27.34      (![X0 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ 
% 27.12/27.34              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ 
% 27.12/27.34                 (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))))),
% 27.12/27.34      inference('sup-', [status(thm)], ['91', '92'])).
% 27.12/27.34  thf('94', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 27.12/27.34         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 27.12/27.34            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['41', '93'])).
% 27.12/27.34  thf('95', plain,
% 27.12/27.34      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 27.12/27.34        sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['89', '90'])).
% 27.12/27.34  thf('96', plain,
% 27.12/27.34      (![X0 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['34', '35'])).
% 27.12/27.34  thf('97', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 27.12/27.34      inference('sup-', [status(thm)], ['95', '96'])).
% 27.12/27.34  thf('98', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['1', '2'])).
% 27.12/27.34  thf('99', plain,
% 27.12/27.34      (![X0 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 27.12/27.34             sk_A))),
% 27.12/27.34      inference('sup-', [status(thm)], ['53', '54'])).
% 27.12/27.34  thf('100', plain,
% 27.12/27.34      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 27.12/27.34        sk_A)),
% 27.12/27.34      inference('sup-', [status(thm)], ['98', '99'])).
% 27.12/27.34  thf('101', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['1', '2'])).
% 27.12/27.34  thf('102', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i]:
% 27.12/27.34         (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 27.12/27.34            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ X1))
% 27.12/27.34          | ~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 27.12/27.34      inference('sup-', [status(thm)], ['20', '27'])).
% 27.12/27.34  thf('103', plain,
% 27.12/27.34      (![X0 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['101', '102'])).
% 27.12/27.34  thf('104', plain,
% 27.12/27.34      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34         (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 27.12/27.34            (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['100', '103'])).
% 27.12/27.34  thf('105', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 27.12/27.34      inference('sup+', [status(thm)], ['17', '30'])).
% 27.12/27.34  thf('106', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 27.12/27.34      inference('sup+', [status(thm)], ['17', '30'])).
% 27.12/27.34  thf('107', plain,
% 27.12/27.34      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ sk_C)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 27.12/27.34            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)))),
% 27.12/27.34      inference('demod', [status(thm)], ['104', '105', '106'])).
% 27.12/27.34  thf('108', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 27.12/27.34         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 27.12/27.34      inference('sup+', [status(thm)], ['37', '38'])).
% 27.12/27.34  thf('109', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 27.12/27.34         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 27.12/27.34      inference('sup+', [status(thm)], ['37', '38'])).
% 27.12/27.34  thf('110', plain,
% 27.12/27.34      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 27.12/27.34            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 27.12/27.34      inference('demod', [status(thm)], ['107', '108', '109'])).
% 27.12/27.34  thf('111', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 27.12/27.34            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 27.12/27.34      inference('sup+', [status(thm)], ['97', '110'])).
% 27.12/27.34  thf('112', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 27.12/27.34         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 27.12/27.34            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 27.12/27.34      inference('sup+', [status(thm)], ['94', '111'])).
% 27.12/27.34  thf('113', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 27.12/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.12/27.34  thf('114', plain,
% 27.12/27.34      (![X30 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X30)) = (X30))),
% 27.12/27.34      inference('cnf', [status(esa)], [t1_yellow_1])).
% 27.12/27.34  thf('115', plain,
% 27.12/27.34      (![X21 : $i, X22 : $i, X23 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 27.12/27.34          | ((X21) != (k12_lattice3 @ X22 @ X21 @ X23))
% 27.12/27.34          | (r3_orders_2 @ X22 @ X21 @ X23)
% 27.12/27.34          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 27.12/27.34          | ~ (l1_orders_2 @ X22)
% 27.12/27.34          | ~ (v2_lattice3 @ X22)
% 27.12/27.34          | ~ (v5_orders_2 @ X22)
% 27.12/27.34          | ~ (v3_orders_2 @ X22))),
% 27.12/27.34      inference('cnf', [status(esa)], [t25_yellow_0])).
% 27.12/27.34  thf('116', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X1 @ X0)
% 27.12/27.34          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 27.12/27.34          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 27.12/27.34          | ((X1) != (k12_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['114', '115'])).
% 27.12/27.34  thf('117', plain, (![X27 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X27))),
% 27.12/27.34      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 27.12/27.34  thf('118', plain, (![X29 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X29))),
% 27.12/27.34      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 27.12/27.34  thf('119', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 27.12/27.34      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 27.12/27.34  thf('120', plain,
% 27.12/27.34      (![X30 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X30)) = (X30))),
% 27.12/27.34      inference('cnf', [status(esa)], [t1_yellow_1])).
% 27.12/27.34  thf('121', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X1 @ X0)
% 27.12/27.34          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ~ (m1_subset_1 @ X2 @ X0)
% 27.12/27.34          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 27.12/27.34          | ((X1) != (k12_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)))),
% 27.12/27.34      inference('demod', [status(thm)], ['116', '117', '118', '119', '120'])).
% 27.12/27.34  thf('122', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i]:
% 27.12/27.34         (((X0) != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ X1))
% 27.12/27.34          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ X0 @ X1)
% 27.12/27.34          | ~ (m1_subset_1 @ X1 @ sk_A)
% 27.12/27.34          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 27.12/27.34      inference('sup-', [status(thm)], ['113', '121'])).
% 27.12/27.34  thf('123', plain,
% 27.12/27.34      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 27.12/27.34          != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 27.12/27.34              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))
% 27.12/27.34        | ~ (m1_subset_1 @ 
% 27.12/27.34             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 27.12/27.34        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 27.12/27.34        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 27.12/27.34      inference('sup-', [status(thm)], ['112', '122'])).
% 27.12/27.34  thf('124', plain,
% 27.12/27.34      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 27.12/27.34        sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['89', '90'])).
% 27.12/27.34  thf('125', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['1', '2'])).
% 27.12/27.34  thf('126', plain,
% 27.12/27.34      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 27.12/27.34          != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 27.12/27.34              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))
% 27.12/27.34        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 27.12/27.34      inference('demod', [status(thm)], ['123', '124', '125'])).
% 27.12/27.34  thf('127', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['1', '2'])).
% 27.12/27.34  thf('128', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['1', '2'])).
% 27.12/27.34  thf('129', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['4', '5'])).
% 27.12/27.34  thf('130', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 27.12/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.12/27.34  thf('131', plain,
% 27.12/27.34      (![X30 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X30)) = (X30))),
% 27.12/27.34      inference('cnf', [status(esa)], [t1_yellow_1])).
% 27.12/27.34  thf(t16_lattice3, axiom,
% 27.12/27.34    (![A:$i]:
% 27.12/27.34     ( ( ( v5_orders_2 @ A ) & ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 27.12/27.34       ( ![B:$i]:
% 27.12/27.34         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 27.12/27.34           ( ![C:$i]:
% 27.12/27.34             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 27.12/27.34               ( ![D:$i]:
% 27.12/27.34                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 27.12/27.34                   ( ( v4_orders_2 @ A ) =>
% 27.12/27.34                     ( ( k11_lattice3 @ A @ ( k11_lattice3 @ A @ B @ C ) @ D ) =
% 27.12/27.34                       ( k11_lattice3 @ A @ B @ ( k11_lattice3 @ A @ C @ D ) ) ) ) ) ) ) ) ) ) ))).
% 27.12/27.34  thf('132', plain,
% 27.12/27.34      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 27.12/27.34          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 27.12/27.34          | ((k11_lattice3 @ X18 @ (k11_lattice3 @ X18 @ X17 @ X20) @ X19)
% 27.12/27.34              = (k11_lattice3 @ X18 @ X17 @ (k11_lattice3 @ X18 @ X20 @ X19)))
% 27.12/27.34          | ~ (v4_orders_2 @ X18)
% 27.12/27.34          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 27.12/27.34          | ~ (l1_orders_2 @ X18)
% 27.12/27.34          | ~ (v2_lattice3 @ X18)
% 27.12/27.34          | ~ (v5_orders_2 @ X18))),
% 27.12/27.34      inference('cnf', [status(esa)], [t16_lattice3])).
% 27.12/27.34  thf('133', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X1 @ X0)
% 27.12/27.34          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 27.12/27.34          | ~ (v4_orders_2 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ((k11_lattice3 @ (k2_yellow_1 @ X0) @ 
% 27.12/27.34              (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ X3)
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ 
% 27.12/27.34                 (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X3)))
% 27.12/27.34          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ (k2_yellow_1 @ X0))))),
% 27.12/27.34      inference('sup-', [status(thm)], ['131', '132'])).
% 27.12/27.34  thf('134', plain, (![X29 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X29))),
% 27.12/27.34      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 27.12/27.34  thf('135', plain, (![X25 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X25))),
% 27.12/27.34      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 27.12/27.34  thf('136', plain,
% 27.12/27.34      (![X30 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X30)) = (X30))),
% 27.12/27.34      inference('cnf', [status(esa)], [t1_yellow_1])).
% 27.12/27.34  thf('137', plain, (![X28 : $i]: (v4_orders_2 @ (k2_yellow_1 @ X28))),
% 27.12/27.34      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 27.12/27.34  thf('138', plain,
% 27.12/27.34      (![X30 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X30)) = (X30))),
% 27.12/27.34      inference('cnf', [status(esa)], [t1_yellow_1])).
% 27.12/27.34  thf('139', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X1 @ X0)
% 27.12/27.34          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 27.12/27.34          | ~ (m1_subset_1 @ X2 @ X0)
% 27.12/27.34          | ((k11_lattice3 @ (k2_yellow_1 @ X0) @ 
% 27.12/27.34              (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ X3)
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ 
% 27.12/27.34                 (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X3)))
% 27.12/27.34          | ~ (m1_subset_1 @ X3 @ X0))),
% 27.12/27.34      inference('demod', [status(thm)],
% 27.12/27.34                ['133', '134', '135', '136', '137', '138'])).
% 27.12/27.34  thf('140', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34              (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X2 @ X1) @ X0)
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X2 @ 
% 27.12/27.34                 (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)))
% 27.12/27.34          | ~ (m1_subset_1 @ X1 @ sk_A)
% 27.12/27.34          | ~ (m1_subset_1 @ X2 @ sk_A))),
% 27.12/27.34      inference('sup-', [status(thm)], ['130', '139'])).
% 27.12/27.34  thf('141', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | ~ (m1_subset_1 @ X1 @ sk_A)
% 27.12/27.34          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34              (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ X1) @ sk_B)
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ 
% 27.12/27.34                 (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ sk_B))))),
% 27.12/27.34      inference('sup-', [status(thm)], ['129', '140'])).
% 27.12/27.34  thf('142', plain,
% 27.12/27.34      (![X0 : $i]:
% 27.12/27.34         (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34            (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0) @ sk_B)
% 27.12/27.34            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 27.12/27.34               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)))
% 27.12/27.34          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 27.12/27.34      inference('sup-', [status(thm)], ['128', '141'])).
% 27.12/27.34  thf('143', plain,
% 27.12/27.34      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34         (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C) @ sk_B)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 27.12/27.34            (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['127', '142'])).
% 27.12/27.34  thf('144', plain,
% 27.12/27.34      (((sk_C) = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_C))),
% 27.12/27.34      inference('demod', [status(thm)], ['59', '86'])).
% 27.12/27.34  thf('145', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B))),
% 27.12/27.34      inference('sup-', [status(thm)], ['3', '16'])).
% 27.12/27.34  thf('146', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 27.12/27.34         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 27.12/27.34      inference('sup+', [status(thm)], ['37', '38'])).
% 27.12/27.34  thf('147', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B))),
% 27.12/27.34      inference('demod', [status(thm)], ['145', '146'])).
% 27.12/27.34  thf('148', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 27.12/27.34         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 27.12/27.34            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['41', '93'])).
% 27.12/27.34  thf('149', plain,
% 27.12/27.34      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 27.12/27.34         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 27.12/27.34            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 27.12/27.34      inference('demod', [status(thm)], ['143', '144', '147', '148'])).
% 27.12/27.34  thf('150', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B))),
% 27.12/27.34      inference('demod', [status(thm)], ['145', '146'])).
% 27.12/27.34  thf('151', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 27.12/27.34         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 27.12/27.34            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 27.12/27.34      inference('demod', [status(thm)], ['149', '150'])).
% 27.12/27.34  thf('152', plain,
% 27.12/27.34      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 27.12/27.34          != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 27.12/27.34        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 27.12/27.34      inference('demod', [status(thm)], ['126', '151'])).
% 27.12/27.34  thf('153', plain,
% 27.12/27.34      ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34        (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)),
% 27.12/27.34      inference('simplify', [status(thm)], ['152'])).
% 27.12/27.34  thf('154', plain,
% 27.12/27.34      (![X32 : $i, X33 : $i, X34 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X32 @ (u1_struct_0 @ (k2_yellow_1 @ X33)))
% 27.12/27.34          | ~ (r3_orders_2 @ (k2_yellow_1 @ X33) @ X32 @ X34)
% 27.12/27.34          | (r1_tarski @ X32 @ X34)
% 27.12/27.34          | ~ (m1_subset_1 @ X34 @ (u1_struct_0 @ (k2_yellow_1 @ X33)))
% 27.12/27.34          | (v1_xboole_0 @ X33))),
% 27.12/27.34      inference('cnf', [status(esa)], [t3_yellow_1])).
% 27.12/27.34  thf('155', plain,
% 27.12/27.34      (![X30 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X30)) = (X30))),
% 27.12/27.34      inference('cnf', [status(esa)], [t1_yellow_1])).
% 27.12/27.34  thf('156', plain,
% 27.12/27.34      (![X30 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X30)) = (X30))),
% 27.12/27.34      inference('cnf', [status(esa)], [t1_yellow_1])).
% 27.12/27.34  thf('157', plain,
% 27.12/27.34      (![X32 : $i, X33 : $i, X34 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X32 @ X33)
% 27.12/27.34          | ~ (r3_orders_2 @ (k2_yellow_1 @ X33) @ X32 @ X34)
% 27.12/27.34          | (r1_tarski @ X32 @ X34)
% 27.12/27.34          | ~ (m1_subset_1 @ X34 @ X33)
% 27.12/27.34          | (v1_xboole_0 @ X33))),
% 27.12/27.34      inference('demod', [status(thm)], ['154', '155', '156'])).
% 27.12/27.34  thf('158', plain,
% 27.12/27.34      (((v1_xboole_0 @ sk_A)
% 27.12/27.34        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 27.12/27.34        | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 27.12/27.34           sk_C)
% 27.12/27.34        | ~ (m1_subset_1 @ 
% 27.12/27.34             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 27.12/27.34      inference('sup-', [status(thm)], ['153', '157'])).
% 27.12/27.34  thf('159', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['1', '2'])).
% 27.12/27.34  thf('160', plain,
% 27.12/27.34      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 27.12/27.34        sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['89', '90'])).
% 27.12/27.34  thf('161', plain,
% 27.12/27.34      (((v1_xboole_0 @ sk_A)
% 27.12/27.34        | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 27.12/27.34           sk_C))),
% 27.12/27.34      inference('demod', [status(thm)], ['158', '159', '160'])).
% 27.12/27.34  thf('162', plain, (~ (v1_xboole_0 @ sk_A)),
% 27.12/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.12/27.34  thf('163', plain,
% 27.12/27.34      ((r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)),
% 27.12/27.34      inference('clc', [status(thm)], ['161', '162'])).
% 27.12/27.34  thf('164', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['4', '5'])).
% 27.12/27.34  thf('165', plain,
% 27.12/27.34      (![X0 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ 
% 27.12/27.34              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ 
% 27.12/27.34                 (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))))),
% 27.12/27.34      inference('sup-', [status(thm)], ['91', '92'])).
% 27.12/27.34  thf('166', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 27.12/27.34         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 27.12/27.34            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['164', '165'])).
% 27.12/27.34  thf('167', plain,
% 27.12/27.34      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 27.12/27.34        sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['89', '90'])).
% 27.12/27.34  thf('168', plain,
% 27.12/27.34      (![X0 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['6', '15'])).
% 27.12/27.34  thf('169', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 27.12/27.34      inference('sup-', [status(thm)], ['167', '168'])).
% 27.12/27.34  thf('170', plain,
% 27.12/27.34      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 27.12/27.34        sk_A)),
% 27.12/27.34      inference('sup-', [status(thm)], ['98', '99'])).
% 27.12/27.34  thf('171', plain,
% 27.12/27.34      (![X0 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | ((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['19', '28'])).
% 27.12/27.34  thf('172', plain,
% 27.12/27.34      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34         (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 27.12/27.34            (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['170', '171'])).
% 27.12/27.34  thf('173', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 27.12/27.34      inference('sup+', [status(thm)], ['17', '30'])).
% 27.12/27.34  thf('174', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 27.12/27.34      inference('sup+', [status(thm)], ['17', '30'])).
% 27.12/27.34  thf('175', plain,
% 27.12/27.34      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ sk_B)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 27.12/27.34            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)))),
% 27.12/27.34      inference('demod', [status(thm)], ['172', '173', '174'])).
% 27.12/27.34  thf('176', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 27.12/27.34         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 27.12/27.34      inference('sup+', [status(thm)], ['37', '38'])).
% 27.12/27.34  thf('177', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 27.12/27.34         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 27.12/27.34      inference('sup+', [status(thm)], ['37', '38'])).
% 27.12/27.34  thf('178', plain,
% 27.12/27.34      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 27.12/27.34            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 27.12/27.34      inference('demod', [status(thm)], ['175', '176', '177'])).
% 27.12/27.34  thf('179', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 27.12/27.34            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 27.12/27.34      inference('sup+', [status(thm)], ['169', '178'])).
% 27.12/27.34  thf('180', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 27.12/27.34         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 27.12/27.34            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 27.12/27.34      inference('sup+', [status(thm)], ['166', '179'])).
% 27.12/27.34  thf('181', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i]:
% 27.12/27.34         (((X0) != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ X1))
% 27.12/27.34          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ X0 @ X1)
% 27.12/27.34          | ~ (m1_subset_1 @ X1 @ sk_A)
% 27.12/27.34          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 27.12/27.34      inference('sup-', [status(thm)], ['113', '121'])).
% 27.12/27.34  thf('182', plain,
% 27.12/27.34      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 27.12/27.34          != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 27.12/27.34              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))
% 27.12/27.34        | ~ (m1_subset_1 @ 
% 27.12/27.34             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 27.12/27.34        | ~ (m1_subset_1 @ sk_B @ sk_A)
% 27.12/27.34        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 27.12/27.34      inference('sup-', [status(thm)], ['180', '181'])).
% 27.12/27.34  thf('183', plain,
% 27.12/27.34      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 27.12/27.34        sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['89', '90'])).
% 27.12/27.34  thf('184', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['4', '5'])).
% 27.12/27.34  thf('185', plain,
% 27.12/27.34      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 27.12/27.34          != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 27.12/27.34              (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))
% 27.12/27.34        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 27.12/27.34      inference('demod', [status(thm)], ['182', '183', '184'])).
% 27.12/27.34  thf('186', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['4', '5'])).
% 27.12/27.34  thf('187', plain,
% 27.12/27.34      (![X0 : $i]:
% 27.12/27.34         (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34            (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ X0) @ sk_B)
% 27.12/27.34            = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 27.12/27.34               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)))
% 27.12/27.34          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 27.12/27.34      inference('sup-', [status(thm)], ['128', '141'])).
% 27.12/27.34  thf('188', plain,
% 27.12/27.34      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34         (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ sk_B)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 27.12/27.34            (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['186', '187'])).
% 27.12/27.34  thf('189', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B))),
% 27.12/27.34      inference('demod', [status(thm)], ['145', '146'])).
% 27.12/27.34  thf('190', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['4', '5'])).
% 27.12/27.34  thf('191', plain,
% 27.12/27.34      (![X0 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | ((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)
% 27.12/27.34              = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['6', '15'])).
% 27.12/27.34  thf('192', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))),
% 27.12/27.34      inference('sup-', [status(thm)], ['190', '191'])).
% 27.12/27.34  thf('193', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['4', '5'])).
% 27.12/27.34  thf('194', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['4', '5'])).
% 27.12/27.34  thf('195', plain,
% 27.12/27.34      (![X32 : $i, X33 : $i, X34 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X32 @ X33)
% 27.12/27.34          | ~ (r1_tarski @ X32 @ X34)
% 27.12/27.34          | (r3_orders_2 @ (k2_yellow_1 @ X33) @ X32 @ X34)
% 27.12/27.34          | ~ (m1_subset_1 @ X34 @ X33)
% 27.12/27.34          | (v1_xboole_0 @ X33))),
% 27.12/27.34      inference('demod', [status(thm)], ['62', '63', '64'])).
% 27.12/27.34  thf('196', plain,
% 27.12/27.34      (![X0 : $i]:
% 27.12/27.34         ((v1_xboole_0 @ sk_A)
% 27.12/27.34          | ~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)
% 27.12/27.34          | ~ (r1_tarski @ sk_B @ X0))),
% 27.12/27.34      inference('sup-', [status(thm)], ['194', '195'])).
% 27.12/27.34  thf('197', plain,
% 27.12/27.34      ((~ (r1_tarski @ sk_B @ sk_B)
% 27.12/27.34        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)
% 27.12/27.34        | (v1_xboole_0 @ sk_A))),
% 27.12/27.34      inference('sup-', [status(thm)], ['193', '196'])).
% 27.12/27.34  thf('198', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 27.12/27.34      inference('simplify', [status(thm)], ['68'])).
% 27.12/27.34  thf('199', plain,
% 27.12/27.34      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)
% 27.12/27.34        | (v1_xboole_0 @ sk_A))),
% 27.12/27.34      inference('demod', [status(thm)], ['197', '198'])).
% 27.12/27.34  thf('200', plain, (~ (v1_xboole_0 @ sk_A)),
% 27.12/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.12/27.34  thf('201', plain, ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)),
% 27.12/27.34      inference('clc', [status(thm)], ['199', '200'])).
% 27.12/27.34  thf('202', plain,
% 27.12/27.34      (![X0 : $i, X1 : $i]:
% 27.12/27.34         (~ (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 27.12/27.34          | ((X1) = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0))
% 27.12/27.34          | ~ (m1_subset_1 @ X0 @ sk_A)
% 27.12/27.34          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 27.12/27.34      inference('sup-', [status(thm)], ['73', '81'])).
% 27.12/27.34  thf('203', plain,
% 27.12/27.34      ((~ (m1_subset_1 @ sk_B @ sk_A)
% 27.12/27.34        | ~ (m1_subset_1 @ sk_B @ sk_A)
% 27.12/27.34        | ((sk_B) = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B)))),
% 27.12/27.34      inference('sup-', [status(thm)], ['201', '202'])).
% 27.12/27.34  thf('204', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['4', '5'])).
% 27.12/27.34  thf('205', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['4', '5'])).
% 27.12/27.34  thf('206', plain,
% 27.12/27.34      (((sk_B) = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))),
% 27.12/27.34      inference('demod', [status(thm)], ['203', '204', '205'])).
% 27.12/27.34  thf('207', plain,
% 27.12/27.34      (((sk_B) = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_B))),
% 27.12/27.34      inference('demod', [status(thm)], ['192', '206'])).
% 27.12/27.34  thf('208', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B))),
% 27.12/27.34      inference('demod', [status(thm)], ['145', '146'])).
% 27.12/27.34  thf('209', plain,
% 27.12/27.34      (((k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 27.12/27.34         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 27.12/27.34      inference('demod', [status(thm)], ['188', '189', '207', '208'])).
% 27.12/27.34  thf('210', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 27.12/27.34      inference('sup-', [status(thm)], ['167', '168'])).
% 27.12/27.34  thf('211', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 27.12/27.34         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 27.12/27.34            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 27.12/27.34      inference('sup+', [status(thm)], ['166', '179'])).
% 27.12/27.34  thf('212', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 27.12/27.34         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 27.12/27.34         = (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34            (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 27.12/27.34      inference('demod', [status(thm)], ['210', '211'])).
% 27.12/27.34  thf('213', plain,
% 27.12/27.34      (((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 27.12/27.34         (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 27.12/27.34         = (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 27.12/27.34      inference('sup+', [status(thm)], ['209', '212'])).
% 27.12/27.34  thf('214', plain,
% 27.12/27.34      ((((k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 27.12/27.34          != (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 27.12/27.34        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34           (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 27.12/27.34      inference('demod', [status(thm)], ['185', '213'])).
% 27.12/27.34  thf('215', plain,
% 27.12/27.34      ((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 27.12/27.34        (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)),
% 27.12/27.34      inference('simplify', [status(thm)], ['214'])).
% 27.12/27.34  thf('216', plain,
% 27.12/27.34      (![X32 : $i, X33 : $i, X34 : $i]:
% 27.12/27.34         (~ (m1_subset_1 @ X32 @ X33)
% 27.12/27.34          | ~ (r3_orders_2 @ (k2_yellow_1 @ X33) @ X32 @ X34)
% 27.12/27.34          | (r1_tarski @ X32 @ X34)
% 27.12/27.34          | ~ (m1_subset_1 @ X34 @ X33)
% 27.12/27.34          | (v1_xboole_0 @ X33))),
% 27.12/27.34      inference('demod', [status(thm)], ['154', '155', '156'])).
% 27.12/27.34  thf('217', plain,
% 27.12/27.34      (((v1_xboole_0 @ sk_A)
% 27.12/27.34        | ~ (m1_subset_1 @ sk_B @ sk_A)
% 27.12/27.34        | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 27.12/27.34           sk_B)
% 27.12/27.34        | ~ (m1_subset_1 @ 
% 27.12/27.34             (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 27.12/27.34      inference('sup-', [status(thm)], ['215', '216'])).
% 27.12/27.34  thf('218', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['4', '5'])).
% 27.12/27.34  thf('219', plain,
% 27.12/27.34      ((m1_subset_1 @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 27.12/27.34        sk_A)),
% 27.12/27.34      inference('demod', [status(thm)], ['89', '90'])).
% 27.12/27.34  thf('220', plain,
% 27.12/27.34      (((v1_xboole_0 @ sk_A)
% 27.12/27.34        | (r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 27.12/27.34           sk_B))),
% 27.12/27.34      inference('demod', [status(thm)], ['217', '218', '219'])).
% 27.12/27.34  thf('221', plain, (~ (v1_xboole_0 @ sk_A)),
% 27.12/27.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 27.12/27.34  thf('222', plain,
% 27.12/27.34      ((r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)),
% 27.12/27.34      inference('clc', [status(thm)], ['220', '221'])).
% 27.12/27.34  thf(t19_xboole_1, axiom,
% 27.12/27.34    (![A:$i,B:$i,C:$i]:
% 27.12/27.34     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 27.12/27.34       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 27.12/27.34  thf('223', plain,
% 27.12/27.34      (![X3 : $i, X4 : $i, X5 : $i]:
% 27.12/27.34         (~ (r1_tarski @ X3 @ X4)
% 27.12/27.34          | ~ (r1_tarski @ X3 @ X5)
% 27.12/27.34          | (r1_tarski @ X3 @ (k3_xboole_0 @ X4 @ X5)))),
% 27.12/27.34      inference('cnf', [status(esa)], [t19_xboole_1])).
% 27.12/27.34  thf('224', plain,
% 27.12/27.34      (![X0 : $i]:
% 27.12/27.34         ((r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 27.12/27.34           (k3_xboole_0 @ sk_B @ X0))
% 27.12/27.34          | ~ (r1_tarski @ 
% 27.12/27.34               (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))),
% 27.12/27.34      inference('sup-', [status(thm)], ['222', '223'])).
% 27.12/27.34  thf('225', plain,
% 27.12/27.34      ((r1_tarski @ (k12_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 27.12/27.34        (k3_xboole_0 @ sk_B @ sk_C))),
% 27.12/27.34      inference('sup-', [status(thm)], ['163', '224'])).
% 27.12/27.34  thf('226', plain, ($false), inference('demod', [status(thm)], ['40', '225'])).
% 27.12/27.34  
% 27.12/27.34  % SZS output end Refutation
% 27.12/27.34  
% 27.12/27.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
