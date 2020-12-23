%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hQpgMMdvah

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:04 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 925 expanded)
%              Number of leaves         :   34 ( 321 expanded)
%              Depth                    :   20
%              Number of atoms          : 1468 (11438 expanded)
%              Number of equality atoms :   44 ( 510 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k13_lattice3_type,type,(
    k13_lattice3: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_lattice3_type,type,(
    v1_lattice3: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k10_lattice3_type,type,(
    k10_lattice3: $i > $i > $i > $i )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(t6_yellow_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_lattice3 @ ( k2_yellow_1 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
               => ( r1_tarski @ ( k2_xboole_0 @ B @ C ) @ ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ( ( v1_lattice3 @ ( k2_yellow_1 @ A ) )
         => ! [B: $i] :
              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
                 => ( r1_tarski @ ( k2_xboole_0 @ B @ C ) @ ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_yellow_1])).

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
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(redefinition_k13_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( k13_lattice3 @ A @ B @ C )
        = ( k10_lattice3 @ A @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v1_lattice3 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( ( k13_lattice3 @ X11 @ X10 @ X12 )
        = ( k10_lattice3 @ X11 @ X10 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k13_lattice3])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( ( k13_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X26: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( ( k13_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
        = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C )
        = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf(t22_yellow_0,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( D
                      = ( k13_lattice3 @ A @ B @ C ) )
                  <=> ( ( r1_orders_2 @ A @ B @ D )
                      & ( r1_orders_2 @ A @ C @ D )
                      & ! [E: $i] :
                          ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                         => ( ( ( r1_orders_2 @ A @ B @ E )
                              & ( r1_orders_2 @ A @ C @ E ) )
                           => ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( X18
       != ( k13_lattice3 @ X17 @ X16 @ X19 ) )
      | ( r1_orders_2 @ X17 @ X19 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v1_lattice3 @ X17 )
      | ~ ( v5_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t22_yellow_0])).

thf('18',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( v5_orders_2 @ X17 )
      | ~ ( v1_lattice3 @ X17 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( r1_orders_2 @ X17 @ X19 @ ( k13_lattice3 @ X17 @ X16 @ X19 ) )
      | ~ ( m1_subset_1 @ ( k13_lattice3 @ X17 @ X16 @ X19 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v1_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('22',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('23',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(dt_k13_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k13_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v1_lattice3 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( m1_subset_1 @ ( k13_lattice3 @ X8 @ X7 @ X9 ) @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k13_lattice3])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('28',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('29',plain,(
    ! [X26: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('30',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ( m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28','29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['21','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('36',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
        = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B )
        = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('41',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('42',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf(t13_lattice3,axiom,(
    ! [A: $i] :
      ( ( ( v5_orders_2 @ A )
        & ( v1_lattice3 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( k10_lattice3 @ A @ B @ C )
                = ( k10_lattice3 @ A @ C @ B ) ) ) ) ) )).

thf('44',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( ( k10_lattice3 @ X14 @ X13 @ X15 )
        = ( k10_lattice3 @ X14 @ X15 @ X13 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v1_lattice3 @ X14 )
      | ~ ( v5_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t13_lattice3])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X26: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('47',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('48',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
        = ( k10_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','46','47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X1 @ X0 )
        = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ X0 @ sk_B )
        = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','50'])).

thf('52',plain,
    ( ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['40','51'])).

thf('53',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['39','52'])).

thf('54',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['34','53'])).

thf('55',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('56',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('57',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['2','15'])).

thf('58',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('60',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('61',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X26: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('63',plain,(
    r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['19','20','54','55','56','57','58','59','60','61','62'])).

thf('64',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
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

thf('65',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_orders_2 @ X4 )
      | ~ ( v3_orders_2 @ X4 )
      | ( v2_struct_0 @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( r3_orders_2 @ X4 @ X3 @ X5 )
      | ~ ( r1_orders_2 @ X4 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_orders_2])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v3_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('68',plain,(
    ! [X24: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('69',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['34','53'])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('74',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('75',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X30 ) @ X29 @ X31 )
      | ( r1_tarski @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ ( k2_yellow_1 @ X30 ) ) )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('76',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('77',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('78',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ X30 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X30 ) @ X29 @ X31 )
      | ( r1_tarski @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['74','78'])).

thf('80',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['34','53'])).

thf('81',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('82',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( r1_tarski @ sk_C @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['39','52'])).

thf('86',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ~ ( v5_orders_2 @ X17 )
      | ~ ( v1_lattice3 @ X17 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( r1_orders_2 @ X17 @ X19 @ ( k13_lattice3 @ X17 @ X16 @ X19 ) )
      | ~ ( m1_subset_1 @ ( k13_lattice3 @ X17 @ X16 @ X19 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('87',plain,
    ( ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
    | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v1_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v5_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('89',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['34','53'])).

thf('90',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('91',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('92',plain,
    ( ( k13_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_C @ sk_B )
    = ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['39','52'])).

thf('93',plain,(
    ! [X27: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t1_yellow_1])).

thf('94',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('95',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('96',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X26: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('98',plain,(
    r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['87','88','89','90','91','92','93','94','95','96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('100',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['34','53'])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('103',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['100','101','102'])).

thf('104',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X29 @ X30 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X30 ) @ X29 @ X31 )
      | ( r1_tarski @ X29 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ X30 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('105',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A )
    | ( r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['34','53'])).

thf('107',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('108',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( r1_tarski @ sk_B @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('111',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ X0 ) @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
      | ~ ( r1_tarski @ X0 @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','112'])).

thf('114',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ~ ( r1_tarski @ ( k2_xboole_0 @ sk_B @ sk_C ) @ ( k10_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X22: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf(cc1_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('118',plain,(
    ! [X6: $i] :
      ( ~ ( v1_lattice3 @ X6 )
      | ~ ( v2_struct_0 @ X6 )
      | ~ ( l1_orders_2 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattice3])).

thf('119',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_lattice3 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ~ ( v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['116','119'])).

thf('121',plain,(
    v1_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    $false ),
    inference(demod,[status(thm)],['120','121'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hQpgMMdvah
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:17:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.51/0.69  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.51/0.69  % Solved by: fo/fo7.sh
% 0.51/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.69  % done 262 iterations in 0.236s
% 0.51/0.69  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.51/0.69  % SZS output start Refutation
% 0.51/0.69  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.51/0.69  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.51/0.69  thf(k13_lattice3_type, type, k13_lattice3: $i > $i > $i > $i).
% 0.51/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.51/0.69  thf(v1_lattice3_type, type, v1_lattice3: $i > $o).
% 0.51/0.69  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.51/0.69  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.51/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.69  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.51/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.69  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.69  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.51/0.69  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.51/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.51/0.69  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.51/0.69  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.51/0.69  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.51/0.69  thf(k10_lattice3_type, type, k10_lattice3: $i > $i > $i > $i).
% 0.51/0.69  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.51/0.69  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.51/0.69  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.51/0.69  thf(t6_yellow_1, conjecture,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.51/0.69       ( ( v1_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.51/0.69         ( ![B:$i]:
% 0.51/0.69           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.51/0.69             ( ![C:$i]:
% 0.51/0.69               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.51/0.69                 ( r1_tarski @
% 0.51/0.69                   ( k2_xboole_0 @ B @ C ) @ 
% 0.51/0.69                   ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) ) ) ) ) ) ) ))).
% 0.51/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.69    (~( ![A:$i]:
% 0.51/0.69        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.51/0.69          ( ( v1_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.51/0.69            ( ![B:$i]:
% 0.51/0.69              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.51/0.69                ( ![C:$i]:
% 0.51/0.69                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.51/0.69                    ( r1_tarski @
% 0.51/0.69                      ( k2_xboole_0 @ B @ C ) @ 
% 0.51/0.69                      ( k10_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) ) ) ) ) ) ) ) )),
% 0.51/0.69    inference('cnf.neg', [status(esa)], [t6_yellow_1])).
% 0.51/0.69  thf('0', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf(t1_yellow_1, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( ( u1_orders_2 @ ( k2_yellow_1 @ A ) ) = ( k1_yellow_1 @ A ) ) & 
% 0.51/0.69       ( ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) = ( A ) ) ))).
% 0.51/0.69  thf('1', plain, (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.51/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.51/0.69  thf('2', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['0', '1'])).
% 0.51/0.69  thf('3', plain,
% 0.51/0.69      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('4', plain, (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.51/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.51/0.69  thf('5', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['3', '4'])).
% 0.51/0.69  thf('6', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('7', plain, (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.51/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.51/0.69  thf(redefinition_k13_lattice3, axiom,
% 0.51/0.69    (![A:$i,B:$i,C:$i]:
% 0.51/0.69     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.51/0.69         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.51/0.69         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.69       ( ( k13_lattice3 @ A @ B @ C ) = ( k10_lattice3 @ A @ B @ C ) ) ))).
% 0.51/0.69  thf('8', plain,
% 0.51/0.69      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.51/0.69          | ~ (l1_orders_2 @ X11)
% 0.51/0.69          | ~ (v1_lattice3 @ X11)
% 0.51/0.69          | ~ (v5_orders_2 @ X11)
% 0.51/0.69          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.51/0.69          | ((k13_lattice3 @ X11 @ X10 @ X12)
% 0.51/0.69              = (k10_lattice3 @ X11 @ X10 @ X12)))),
% 0.51/0.69      inference('cnf', [status(esa)], [redefinition_k13_lattice3])).
% 0.51/0.69  thf('9', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X1 @ X0)
% 0.51/0.69          | ((k13_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.51/0.69              = (k10_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2))
% 0.51/0.69          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.51/0.69          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.51/0.69          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0))
% 0.51/0.69          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.51/0.69  thf('10', plain,
% 0.51/0.69      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.51/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.51/0.69  thf(fc5_yellow_1, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.51/0.69       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.51/0.69       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.51/0.69       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.51/0.69  thf('11', plain, (![X26 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X26))),
% 0.51/0.69      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.51/0.69  thf(dt_k2_yellow_1, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.51/0.69       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.51/0.69  thf('12', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.51/0.69      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.51/0.69  thf('13', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X1 @ X0)
% 0.51/0.69          | ((k13_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.51/0.69              = (k10_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2))
% 0.51/0.69          | ~ (m1_subset_1 @ X2 @ X0)
% 0.51/0.69          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0)))),
% 0.51/0.69      inference('demod', [status(thm)], ['9', '10', '11', '12'])).
% 0.51/0.69  thf('14', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.51/0.69          | ((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 0.51/0.69              = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0))
% 0.51/0.69          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['6', '13'])).
% 0.51/0.69  thf('15', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.51/0.69          | ((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)
% 0.51/0.69              = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_C)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['5', '14'])).
% 0.51/0.69  thf('16', plain,
% 0.51/0.69      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.51/0.69         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.51/0.69      inference('sup-', [status(thm)], ['2', '15'])).
% 0.51/0.69  thf(t22_yellow_0, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.51/0.69       ( ![B:$i]:
% 0.51/0.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.69           ( ![C:$i]:
% 0.51/0.69             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.69               ( ![D:$i]:
% 0.51/0.69                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.69                   ( ( ( D ) = ( k13_lattice3 @ A @ B @ C ) ) <=>
% 0.51/0.69                     ( ( r1_orders_2 @ A @ B @ D ) & 
% 0.51/0.69                       ( r1_orders_2 @ A @ C @ D ) & 
% 0.51/0.69                       ( ![E:$i]:
% 0.51/0.69                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.69                           ( ( ( r1_orders_2 @ A @ B @ E ) & 
% 0.51/0.69                               ( r1_orders_2 @ A @ C @ E ) ) =>
% 0.51/0.69                             ( r1_orders_2 @ A @ D @ E ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.51/0.69  thf('17', plain,
% 0.51/0.69      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.51/0.69          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.51/0.69          | ((X18) != (k13_lattice3 @ X17 @ X16 @ X19))
% 0.51/0.69          | (r1_orders_2 @ X17 @ X19 @ X18)
% 0.51/0.69          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.51/0.69          | ~ (l1_orders_2 @ X17)
% 0.51/0.69          | ~ (v1_lattice3 @ X17)
% 0.51/0.69          | ~ (v5_orders_2 @ X17))),
% 0.51/0.69      inference('cnf', [status(esa)], [t22_yellow_0])).
% 0.51/0.69  thf('18', plain,
% 0.51/0.69      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.51/0.69         (~ (v5_orders_2 @ X17)
% 0.51/0.69          | ~ (v1_lattice3 @ X17)
% 0.51/0.69          | ~ (l1_orders_2 @ X17)
% 0.51/0.69          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.51/0.69          | (r1_orders_2 @ X17 @ X19 @ (k13_lattice3 @ X17 @ X16 @ X19))
% 0.51/0.69          | ~ (m1_subset_1 @ (k13_lattice3 @ X17 @ X16 @ X19) @ 
% 0.51/0.69               (u1_struct_0 @ X17))
% 0.51/0.69          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17)))),
% 0.51/0.69      inference('simplify', [status(thm)], ['17'])).
% 0.51/0.69  thf('19', plain,
% 0.51/0.69      ((~ (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.51/0.69           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.51/0.69        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.51/0.69        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.51/0.69           (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.51/0.69        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.51/0.69        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.51/0.69        | ~ (v1_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.51/0.69        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['16', '18'])).
% 0.51/0.69  thf('20', plain,
% 0.51/0.69      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.51/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.51/0.69  thf('21', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['3', '4'])).
% 0.51/0.69  thf('22', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['0', '1'])).
% 0.51/0.69  thf('23', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('24', plain,
% 0.51/0.69      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.51/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.51/0.69  thf(dt_k13_lattice3, axiom,
% 0.51/0.69    (![A:$i,B:$i,C:$i]:
% 0.51/0.69     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) & 
% 0.51/0.69         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.51/0.69         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.69       ( m1_subset_1 @ ( k13_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.51/0.69  thf('25', plain,
% 0.51/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 0.51/0.69          | ~ (l1_orders_2 @ X8)
% 0.51/0.69          | ~ (v1_lattice3 @ X8)
% 0.51/0.69          | ~ (v5_orders_2 @ X8)
% 0.51/0.69          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 0.51/0.69          | (m1_subset_1 @ (k13_lattice3 @ X8 @ X7 @ X9) @ (u1_struct_0 @ X8)))),
% 0.51/0.69      inference('cnf', [status(esa)], [dt_k13_lattice3])).
% 0.51/0.69  thf('26', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X1 @ X0)
% 0.51/0.69          | (m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ 
% 0.51/0.69             (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.51/0.69          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.51/0.69          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.51/0.69          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0))
% 0.51/0.69          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['24', '25'])).
% 0.51/0.69  thf('27', plain,
% 0.51/0.69      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.51/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.51/0.69  thf('28', plain,
% 0.51/0.69      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.51/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.51/0.69  thf('29', plain, (![X26 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X26))),
% 0.51/0.69      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.51/0.69  thf('30', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.51/0.69      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.51/0.69  thf('31', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X1 @ X0)
% 0.51/0.69          | (m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2) @ X0)
% 0.51/0.69          | ~ (m1_subset_1 @ X2 @ X0)
% 0.51/0.69          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0)))),
% 0.51/0.69      inference('demod', [status(thm)], ['26', '27', '28', '29', '30'])).
% 0.51/0.69  thf('32', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.51/0.69          | (m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0) @ 
% 0.51/0.69             sk_A)
% 0.51/0.69          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['23', '31'])).
% 0.51/0.69  thf('33', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.51/0.69          | (m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B) @ 
% 0.51/0.69             sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['22', '32'])).
% 0.51/0.69  thf('34', plain,
% 0.51/0.69      ((m1_subset_1 @ (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B) @ 
% 0.51/0.69        sk_A)),
% 0.51/0.69      inference('sup-', [status(thm)], ['21', '33'])).
% 0.51/0.69  thf('35', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['3', '4'])).
% 0.51/0.69  thf('36', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['0', '1'])).
% 0.51/0.69  thf('37', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.51/0.69          | ((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 0.51/0.69              = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0))
% 0.51/0.69          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['6', '13'])).
% 0.51/0.69  thf('38', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.51/0.69          | ((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)
% 0.51/0.69              = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['36', '37'])).
% 0.51/0.69  thf('39', plain,
% 0.51/0.69      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 0.51/0.69         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B))),
% 0.51/0.69      inference('sup-', [status(thm)], ['35', '38'])).
% 0.51/0.69  thf('40', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['3', '4'])).
% 0.51/0.69  thf('41', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['0', '1'])).
% 0.51/0.69  thf('42', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('43', plain,
% 0.51/0.69      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.51/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.51/0.69  thf(t13_lattice3, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( ( v5_orders_2 @ A ) & ( v1_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.51/0.69       ( ![B:$i]:
% 0.51/0.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.69           ( ![C:$i]:
% 0.51/0.69             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.51/0.69               ( ( k10_lattice3 @ A @ B @ C ) = ( k10_lattice3 @ A @ C @ B ) ) ) ) ) ) ))).
% 0.51/0.69  thf('44', plain,
% 0.51/0.69      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.51/0.69          | ((k10_lattice3 @ X14 @ X13 @ X15)
% 0.51/0.69              = (k10_lattice3 @ X14 @ X15 @ X13))
% 0.51/0.69          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.51/0.69          | ~ (l1_orders_2 @ X14)
% 0.51/0.69          | ~ (v1_lattice3 @ X14)
% 0.51/0.69          | ~ (v5_orders_2 @ X14))),
% 0.51/0.69      inference('cnf', [status(esa)], [t13_lattice3])).
% 0.51/0.69  thf('45', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X1 @ X0)
% 0.51/0.69          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.51/0.69          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0))
% 0.51/0.69          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.51/0.69          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.51/0.69          | ((k10_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.51/0.69              = (k10_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['43', '44'])).
% 0.51/0.69  thf('46', plain, (![X26 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X26))),
% 0.51/0.69      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.51/0.69  thf('47', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.51/0.69      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.51/0.69  thf('48', plain,
% 0.51/0.69      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.51/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.51/0.69  thf('49', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X1 @ X0)
% 0.51/0.69          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0))
% 0.51/0.69          | ~ (m1_subset_1 @ X2 @ X0)
% 0.51/0.69          | ((k10_lattice3 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.51/0.69              = (k10_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1)))),
% 0.51/0.69      inference('demod', [status(thm)], ['45', '46', '47', '48'])).
% 0.51/0.69  thf('50', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i]:
% 0.51/0.69         (((k10_lattice3 @ (k2_yellow_1 @ sk_A) @ X1 @ X0)
% 0.51/0.69            = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ X1))
% 0.51/0.69          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.51/0.69          | ~ (m1_subset_1 @ X1 @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['42', '49'])).
% 0.51/0.69  thf('51', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.51/0.69          | ((k10_lattice3 @ (k2_yellow_1 @ sk_A) @ X0 @ sk_B)
% 0.51/0.69              = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['41', '50'])).
% 0.51/0.69  thf('52', plain,
% 0.51/0.69      (((k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 0.51/0.69         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.51/0.69      inference('sup-', [status(thm)], ['40', '51'])).
% 0.51/0.69  thf('53', plain,
% 0.51/0.69      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 0.51/0.69         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['39', '52'])).
% 0.51/0.69  thf('54', plain,
% 0.51/0.69      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.51/0.69        sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['34', '53'])).
% 0.51/0.69  thf('55', plain,
% 0.51/0.69      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.51/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.51/0.69  thf('56', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['0', '1'])).
% 0.51/0.69  thf('57', plain,
% 0.51/0.69      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)
% 0.51/0.69         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.51/0.69      inference('sup-', [status(thm)], ['2', '15'])).
% 0.51/0.69  thf('58', plain,
% 0.51/0.69      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.51/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.51/0.69  thf('59', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['3', '4'])).
% 0.51/0.69  thf('60', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.51/0.69      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.51/0.69  thf('61', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('62', plain, (![X26 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X26))),
% 0.51/0.69      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.51/0.69  thf('63', plain,
% 0.51/0.69      ((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.51/0.69        (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)],
% 0.51/0.69                ['19', '20', '54', '55', '56', '57', '58', '59', '60', '61', 
% 0.51/0.69                 '62'])).
% 0.51/0.69  thf('64', plain,
% 0.51/0.69      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.51/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.51/0.69  thf(redefinition_r3_orders_2, axiom,
% 0.51/0.69    (![A:$i,B:$i,C:$i]:
% 0.51/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.51/0.69         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.51/0.69         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.69       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.51/0.69  thf('65', plain,
% 0.51/0.69      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X4))
% 0.51/0.69          | ~ (l1_orders_2 @ X4)
% 0.51/0.69          | ~ (v3_orders_2 @ X4)
% 0.51/0.69          | (v2_struct_0 @ X4)
% 0.51/0.69          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 0.51/0.69          | (r3_orders_2 @ X4 @ X3 @ X5)
% 0.51/0.69          | ~ (r1_orders_2 @ X4 @ X3 @ X5))),
% 0.51/0.69      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.51/0.69  thf('66', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X1 @ X0)
% 0.51/0.69          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.51/0.69          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.51/0.69          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.51/0.69          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.51/0.69          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.51/0.69          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['64', '65'])).
% 0.51/0.69  thf('67', plain,
% 0.51/0.69      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.51/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.51/0.69  thf('68', plain, (![X24 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X24))),
% 0.51/0.69      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.51/0.69  thf('69', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.51/0.69      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.51/0.69  thf('70', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X1 @ X0)
% 0.51/0.69          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.51/0.69          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.51/0.69          | ~ (m1_subset_1 @ X2 @ X0)
% 0.51/0.69          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.51/0.69      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.51/0.69  thf('71', plain,
% 0.51/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.51/0.69        | ~ (m1_subset_1 @ 
% 0.51/0.69             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.51/0.69        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.51/0.69           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.51/0.69        | ~ (m1_subset_1 @ sk_C @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['63', '70'])).
% 0.51/0.69  thf('72', plain,
% 0.51/0.69      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.51/0.69        sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['34', '53'])).
% 0.51/0.69  thf('73', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['3', '4'])).
% 0.51/0.69  thf('74', plain,
% 0.51/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.51/0.69        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_C @ 
% 0.51/0.69           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.51/0.69      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.51/0.69  thf(t3_yellow_1, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.51/0.69       ( ![B:$i]:
% 0.51/0.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.51/0.69           ( ![C:$i]:
% 0.51/0.69             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.51/0.69               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.51/0.69                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.51/0.69  thf('75', plain,
% 0.51/0.69      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ (k2_yellow_1 @ X30)))
% 0.51/0.69          | ~ (r3_orders_2 @ (k2_yellow_1 @ X30) @ X29 @ X31)
% 0.51/0.69          | (r1_tarski @ X29 @ X31)
% 0.51/0.69          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ (k2_yellow_1 @ X30)))
% 0.51/0.69          | (v1_xboole_0 @ X30))),
% 0.51/0.69      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.51/0.69  thf('76', plain,
% 0.51/0.69      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.51/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.51/0.69  thf('77', plain,
% 0.51/0.69      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.51/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.51/0.69  thf('78', plain,
% 0.51/0.69      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X29 @ X30)
% 0.51/0.69          | ~ (r3_orders_2 @ (k2_yellow_1 @ X30) @ X29 @ X31)
% 0.51/0.69          | (r1_tarski @ X29 @ X31)
% 0.51/0.69          | ~ (m1_subset_1 @ X31 @ X30)
% 0.51/0.69          | (v1_xboole_0 @ X30))),
% 0.51/0.69      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.51/0.69  thf('79', plain,
% 0.51/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.51/0.69        | (v1_xboole_0 @ sk_A)
% 0.51/0.69        | ~ (m1_subset_1 @ 
% 0.51/0.69             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.51/0.69        | (r1_tarski @ sk_C @ 
% 0.51/0.69           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.51/0.69        | ~ (m1_subset_1 @ sk_C @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['74', '78'])).
% 0.51/0.69  thf('80', plain,
% 0.51/0.69      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.51/0.69        sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['34', '53'])).
% 0.51/0.69  thf('81', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['3', '4'])).
% 0.51/0.69  thf('82', plain,
% 0.51/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.51/0.69        | (v1_xboole_0 @ sk_A)
% 0.51/0.69        | (r1_tarski @ sk_C @ 
% 0.51/0.69           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.51/0.69      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.51/0.69  thf('83', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('84', plain,
% 0.51/0.69      (((r1_tarski @ sk_C @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.51/0.69        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.51/0.69      inference('clc', [status(thm)], ['82', '83'])).
% 0.51/0.69  thf('85', plain,
% 0.51/0.69      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 0.51/0.69         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['39', '52'])).
% 0.51/0.69  thf('86', plain,
% 0.51/0.69      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.51/0.69         (~ (v5_orders_2 @ X17)
% 0.51/0.69          | ~ (v1_lattice3 @ X17)
% 0.51/0.69          | ~ (l1_orders_2 @ X17)
% 0.51/0.69          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.51/0.69          | (r1_orders_2 @ X17 @ X19 @ (k13_lattice3 @ X17 @ X16 @ X19))
% 0.51/0.69          | ~ (m1_subset_1 @ (k13_lattice3 @ X17 @ X16 @ X19) @ 
% 0.51/0.69               (u1_struct_0 @ X17))
% 0.51/0.69          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17)))),
% 0.51/0.69      inference('simplify', [status(thm)], ['17'])).
% 0.51/0.69  thf('87', plain,
% 0.51/0.69      ((~ (m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.51/0.69           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.51/0.69        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.51/0.69        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.51/0.69           (k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B))
% 0.51/0.69        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.51/0.69        | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A))
% 0.51/0.69        | ~ (v1_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.51/0.69        | ~ (v5_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['85', '86'])).
% 0.51/0.69  thf('88', plain,
% 0.51/0.69      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.51/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.51/0.69  thf('89', plain,
% 0.51/0.69      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.51/0.69        sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['34', '53'])).
% 0.51/0.69  thf('90', plain,
% 0.51/0.69      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.51/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.51/0.69  thf('91', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['3', '4'])).
% 0.51/0.69  thf('92', plain,
% 0.51/0.69      (((k13_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_C @ sk_B)
% 0.51/0.69         = (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)], ['39', '52'])).
% 0.51/0.69  thf('93', plain,
% 0.51/0.69      (![X27 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X27)) = (X27))),
% 0.51/0.69      inference('cnf', [status(esa)], [t1_yellow_1])).
% 0.51/0.69  thf('94', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['0', '1'])).
% 0.51/0.69  thf('95', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.51/0.69      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.51/0.69  thf('96', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('97', plain, (![X26 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X26))),
% 0.51/0.69      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.51/0.69  thf('98', plain,
% 0.51/0.69      ((r1_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.51/0.69        (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.51/0.69      inference('demod', [status(thm)],
% 0.51/0.69                ['87', '88', '89', '90', '91', '92', '93', '94', '95', '96', 
% 0.51/0.69                 '97'])).
% 0.51/0.69  thf('99', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X1 @ X0)
% 0.51/0.69          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.51/0.69          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.51/0.69          | ~ (m1_subset_1 @ X2 @ X0)
% 0.51/0.69          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.51/0.69      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.51/0.69  thf('100', plain,
% 0.51/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.51/0.69        | ~ (m1_subset_1 @ 
% 0.51/0.69             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.51/0.69        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.51/0.69           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.51/0.69        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['98', '99'])).
% 0.51/0.69  thf('101', plain,
% 0.51/0.69      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.51/0.69        sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['34', '53'])).
% 0.51/0.69  thf('102', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['0', '1'])).
% 0.51/0.69  thf('103', plain,
% 0.51/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.51/0.69        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ sk_B @ 
% 0.51/0.69           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.51/0.69      inference('demod', [status(thm)], ['100', '101', '102'])).
% 0.51/0.69  thf('104', plain,
% 0.51/0.69      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.51/0.69         (~ (m1_subset_1 @ X29 @ X30)
% 0.51/0.69          | ~ (r3_orders_2 @ (k2_yellow_1 @ X30) @ X29 @ X31)
% 0.51/0.69          | (r1_tarski @ X29 @ X31)
% 0.51/0.69          | ~ (m1_subset_1 @ X31 @ X30)
% 0.51/0.69          | (v1_xboole_0 @ X30))),
% 0.51/0.69      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.51/0.69  thf('105', plain,
% 0.51/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.51/0.69        | (v1_xboole_0 @ sk_A)
% 0.51/0.69        | ~ (m1_subset_1 @ 
% 0.51/0.69             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A)
% 0.51/0.69        | (r1_tarski @ sk_B @ 
% 0.51/0.69           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.51/0.69        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['103', '104'])).
% 0.51/0.69  thf('106', plain,
% 0.51/0.69      ((m1_subset_1 @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.51/0.69        sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['34', '53'])).
% 0.51/0.69  thf('107', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.51/0.69      inference('demod', [status(thm)], ['0', '1'])).
% 0.51/0.69  thf('108', plain,
% 0.51/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.51/0.69        | (v1_xboole_0 @ sk_A)
% 0.51/0.69        | (r1_tarski @ sk_B @ 
% 0.51/0.69           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.51/0.69      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.51/0.69  thf('109', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('110', plain,
% 0.51/0.69      (((r1_tarski @ sk_B @ (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.51/0.69        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.51/0.69      inference('clc', [status(thm)], ['108', '109'])).
% 0.51/0.69  thf(t8_xboole_1, axiom,
% 0.51/0.69    (![A:$i,B:$i,C:$i]:
% 0.51/0.69     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.51/0.69       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.51/0.69  thf('111', plain,
% 0.51/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.69         (~ (r1_tarski @ X0 @ X1)
% 0.51/0.69          | ~ (r1_tarski @ X2 @ X1)
% 0.51/0.69          | (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.51/0.69      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.51/0.69  thf('112', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.51/0.69          | (r1_tarski @ (k2_xboole_0 @ sk_B @ X0) @ 
% 0.51/0.69             (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.51/0.69          | ~ (r1_tarski @ X0 @ 
% 0.51/0.69               (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['110', '111'])).
% 0.51/0.69  thf('113', plain,
% 0.51/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.51/0.69        | (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.51/0.69           (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.51/0.69        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['84', '112'])).
% 0.51/0.69  thf('114', plain,
% 0.51/0.69      (((r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.51/0.69         (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))
% 0.51/0.69        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.51/0.69      inference('simplify', [status(thm)], ['113'])).
% 0.51/0.69  thf('115', plain,
% 0.51/0.69      (~ (r1_tarski @ (k2_xboole_0 @ sk_B @ sk_C) @ 
% 0.51/0.69          (k10_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('116', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 0.51/0.69      inference('clc', [status(thm)], ['114', '115'])).
% 0.51/0.69  thf('117', plain, (![X22 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.51/0.69      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.51/0.69  thf(cc1_lattice3, axiom,
% 0.51/0.69    (![A:$i]:
% 0.51/0.69     ( ( l1_orders_2 @ A ) =>
% 0.51/0.69       ( ( v1_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.51/0.69  thf('118', plain,
% 0.51/0.69      (![X6 : $i]:
% 0.51/0.69         (~ (v1_lattice3 @ X6) | ~ (v2_struct_0 @ X6) | ~ (l1_orders_2 @ X6))),
% 0.51/0.69      inference('cnf', [status(esa)], [cc1_lattice3])).
% 0.51/0.69  thf('119', plain,
% 0.51/0.69      (![X0 : $i]:
% 0.51/0.69         (~ (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.51/0.69          | ~ (v1_lattice3 @ (k2_yellow_1 @ X0)))),
% 0.51/0.69      inference('sup-', [status(thm)], ['117', '118'])).
% 0.51/0.69  thf('120', plain, (~ (v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.51/0.69      inference('sup-', [status(thm)], ['116', '119'])).
% 0.51/0.69  thf('121', plain, ((v1_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.51/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.69  thf('122', plain, ($false), inference('demod', [status(thm)], ['120', '121'])).
% 0.51/0.69  
% 0.51/0.69  % SZS output end Refutation
% 0.51/0.69  
% 0.51/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
