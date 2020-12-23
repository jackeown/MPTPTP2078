%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9vKsp9KOBp

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:05 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  153 (1795 expanded)
%              Number of leaves         :   37 ( 611 expanded)
%              Depth                    :   28
%              Number of atoms          : 1478 (18658 expanded)
%              Number of equality atoms :   46 (1460 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(g1_orders_2_type,type,(
    g1_orders_2: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(u1_orders_2_type,type,(
    u1_orders_2: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k11_lattice3_type,type,(
    k11_lattice3: $i > $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k1_yellow_1_type,type,(
    k1_yellow_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(v1_orders_2_type,type,(
    v1_orders_2: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v2_lattice3_type,type,(
    v2_lattice3: $i > $o )).

thf(r3_orders_2_type,type,(
    r3_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k11_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( m1_subset_1 @ ( k11_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ( m1_subset_1 @ ( k11_lattice3 @ X14 @ X13 @ X15 ) @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_lattice3])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_k2_yellow_1,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('4',plain,(
    ! [X23: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ X0 ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(d1_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k2_yellow_1 @ A )
      = ( g1_orders_2 @ A @ ( k1_yellow_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X21: $i] :
      ( ( k2_yellow_1 @ X21 )
      = ( g1_orders_2 @ X21 @ ( k1_yellow_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_yellow_1])).

thf(abstractness_v1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v1_orders_2 @ A )
       => ( A
          = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X3: $i] :
      ( ~ ( v1_orders_2 @ X3 )
      | ( X3
        = ( g1_orders_2 @ ( u1_struct_0 @ X3 ) @ ( u1_orders_2 @ X3 ) ) )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf('9',plain,(
    ! [X21: $i] :
      ( ( k2_yellow_1 @ X21 )
      = ( g1_orders_2 @ X21 @ ( k1_yellow_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_yellow_1])).

thf(dt_u1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( m1_subset_1 @ ( u1_orders_2 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X4 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf(free_g1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
     => ! [C: $i,D: $i] :
          ( ( ( g1_orders_2 @ A @ B )
            = ( g1_orders_2 @ C @ D ) )
         => ( ( A = C )
            & ( B = D ) ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( ( g1_orders_2 @ X7 @ X8 )
       != ( g1_orders_2 @ X5 @ X6 ) )
      | ( X8 = X6 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ X0 ) @ ( u1_orders_2 @ X0 ) )
       != ( g1_orders_2 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( g1_orders_2 @ ( u1_struct_0 @ X1 ) @ ( u1_orders_2 @ X1 ) )
       != ( k2_yellow_1 @ X0 ) )
      | ( ( u1_orders_2 @ X1 )
        = ( k1_yellow_1 @ X0 ) )
      | ~ ( l1_orders_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k2_yellow_1 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( u1_orders_2 @ X0 )
        = ( k1_yellow_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X1: $i] :
      ( ( ( u1_orders_2 @ ( k2_yellow_1 @ X1 ) )
        = ( k1_yellow_1 @ X1 ) )
      | ~ ( v1_orders_2 @ ( k2_yellow_1 @ X1 ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X23: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('17',plain,(
    ! [X22: $i] :
      ( v1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('18',plain,(
    ! [X1: $i] :
      ( ( u1_orders_2 @ ( k2_yellow_1 @ X1 ) )
      = ( k1_yellow_1 @ X1 ) ) ),
    inference('simplify_reflect+',[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( u1_orders_2 @ X4 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ X4 ) @ ( u1_struct_0 @ X4 ) ) ) )
      | ~ ( l1_orders_2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_u1_orders_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_yellow_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X23: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k1_yellow_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( ( g1_orders_2 @ X7 @ X8 )
       != ( g1_orders_2 @ X5 @ X6 ) )
      | ( X7 = X5 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[free_g1_orders_2])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X1 )
      | ( ( g1_orders_2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k1_yellow_1 @ X0 ) )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X1: $i] :
      ( ( u1_orders_2 @ ( k2_yellow_1 @ X1 ) )
      = ( k1_yellow_1 @ X1 ) ) ),
    inference('simplify_reflect+',[status(thm)],['15','16','17'])).

thf('26',plain,(
    ! [X3: $i] :
      ( ~ ( v1_orders_2 @ X3 )
      | ( X3
        = ( g1_orders_2 @ ( u1_struct_0 @ X3 ) @ ( u1_orders_2 @ X3 ) ) )
      | ~ ( l1_orders_2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[abstractness_v1_orders_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_yellow_1 @ X0 )
        = ( g1_orders_2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k1_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v1_orders_2 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X23: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('29',plain,(
    ! [X22: $i] :
      ( v1_orders_2 @ ( k2_yellow_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_yellow_1 @ X0 )
      = ( g1_orders_2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) @ ( k1_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) )
        = X1 )
      | ( ( k2_yellow_1 @ X0 )
       != ( g1_orders_2 @ X1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_yellow_1 @ X1 )
       != ( k2_yellow_1 @ X0 ) )
      | ( ( u1_struct_0 @ ( k2_yellow_1 @ X1 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['7','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['32'])).

thf('34',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['6','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['32'])).

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

thf('36',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( X18
       != ( k11_lattice3 @ X17 @ X16 @ X19 ) )
      | ( r1_orders_2 @ X17 @ X18 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v2_lattice3 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('37',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v2_lattice3 @ X17 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( r1_orders_2 @ X17 @ ( k11_lattice3 @ X17 @ X16 @ X19 ) @ X19 )
      | ~ ( m1_subset_1 @ ( k11_lattice3 @ X17 @ X16 @ X19 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['32'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['32'])).

thf('41',plain,(
    ! [X23: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf(fc5_yellow_1,axiom,(
    ! [A: $i] :
      ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v4_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v3_orders_2 @ ( k2_yellow_1 @ A ) )
      & ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ) )).

thf('42',plain,(
    ! [X27: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39','40','41','42'])).

thf('44',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['32'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['32'])).

thf('51',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['44','45','48','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['32'])).

thf(redefinition_r3_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_orders_2 @ A @ B @ C )
      <=> ( r1_orders_2 @ A @ B @ C ) ) ) )).

thf('54',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( r3_orders_2 @ X10 @ X9 @ X11 )
      | ~ ( r1_orders_2 @ X10 @ X9 @ X11 ) ) ),
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
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['32'])).

thf('57',plain,(
    ! [X25: $i] :
      ( v3_orders_2 @ ( k2_yellow_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('58',plain,(
    ! [X23: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
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
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['52','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf('62',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['6','33'])).

thf('63',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf(t3_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) )
             => ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C )
              <=> ( r1_tarski @ B @ C ) ) ) ) ) )).

thf('65',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) ) )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X29 ) @ X28 @ X30 )
      | ( r1_tarski @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ ( k2_yellow_1 @ X29 ) ) )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t3_yellow_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['32'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['32'])).

thf('68',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ X29 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X29 ) @ X28 @ X30 )
      | ( r1_tarski @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ X29 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['64','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf('71',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['6','33'])).

thf('72',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_C )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['6','33'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['32'])).

thf('77',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( X18
       != ( k11_lattice3 @ X17 @ X16 @ X19 ) )
      | ( r1_orders_2 @ X17 @ X18 @ X16 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v2_lattice3 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[l28_lattice3])).

thf('78',plain,(
    ! [X16: $i,X17: $i,X19: $i] :
      ( ( v2_struct_0 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v2_lattice3 @ X17 )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( r1_orders_2 @ X17 @ ( k11_lattice3 @ X17 @ X16 @ X19 ) @ X16 )
      | ~ ( m1_subset_1 @ ( k11_lattice3 @ X17 @ X16 @ X19 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) ) )
      | ~ ( l1_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v5_orders_2 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['32'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( u1_struct_0 @ ( k2_yellow_1 @ X0 ) )
      = X0 ) ),
    inference(eq_res,[status(thm)],['32'])).

thf('82',plain,(
    ! [X23: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf('83',plain,(
    ! [X27: $i] :
      ( v5_orders_2 @ ( k2_yellow_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc5_yellow_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X0 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ ( k11_lattice3 @ ( k2_yellow_1 @ X0 ) @ X2 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['79','80','81','82','83'])).

thf('85',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['75','84'])).

thf('86',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['46','47'])).

thf('88',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['49','50'])).

thf('89',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['85','86','87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r1_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ( r3_orders_2 @ ( k2_yellow_1 @ X0 ) @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ X0 )
      | ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('91',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ sk_A )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['49','50'])).

thf('93',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['6','33'])).

thf('94',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['91','92','93'])).

thf('95',plain,
    ( ( r3_orders_2 @ ( k2_yellow_1 @ sk_A ) @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X28 @ X29 )
      | ~ ( r3_orders_2 @ ( k2_yellow_1 @ X29 ) @ X28 @ X30 )
      | ( r1_tarski @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ X29 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('97',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ~ ( m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['49','50'])).

thf('99',plain,(
    m1_subset_1 @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['6','33'])).

thf('100',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ sk_B )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X2 )
      | ( r1_tarski @ X0 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
      | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ X0 ) )
      | ~ ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) )
    | ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['74','104'])).

thf('106',plain,
    ( ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) )
    | ( v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    ~ ( r1_tarski @ ( k11_lattice3 @ ( k2_yellow_1 @ sk_A ) @ sk_B @ sk_C ) @ ( k3_xboole_0 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v2_struct_0 @ ( k2_yellow_1 @ sk_A ) ),
    inference(clc,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X23: $i] :
      ( l1_orders_2 @ ( k2_yellow_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_yellow_1])).

thf(cc2_lattice3,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( ( v2_lattice3 @ A )
       => ~ ( v2_struct_0 @ A ) ) ) )).

thf('110',plain,(
    ! [X12: $i] :
      ( ~ ( v2_lattice3 @ X12 )
      | ~ ( v2_struct_0 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_lattice3])).

thf('111',plain,(
    ! [X0: $i] :
      ( ~ ( v2_struct_0 @ ( k2_yellow_1 @ X0 ) )
      | ~ ( v2_lattice3 @ ( k2_yellow_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['108','111'])).

thf('113',plain,(
    v2_lattice3 @ ( k2_yellow_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    $false ),
    inference(demod,[status(thm)],['112','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9vKsp9KOBp
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:40:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.68  % Solved by: fo/fo7.sh
% 0.46/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.68  % done 326 iterations in 0.251s
% 0.46/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.68  % SZS output start Refutation
% 0.46/0.68  thf(g1_orders_2_type, type, g1_orders_2: $i > $i > $i).
% 0.46/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.68  thf(u1_orders_2_type, type, u1_orders_2: $i > $i).
% 0.46/0.68  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.46/0.68  thf(k11_lattice3_type, type, k11_lattice3: $i > $i > $i > $i).
% 0.46/0.68  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.46/0.68  thf(k1_yellow_1_type, type, k1_yellow_1: $i > $i).
% 0.46/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.68  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.46/0.68  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.46/0.68  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.46/0.68  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.46/0.68  thf(v1_orders_2_type, type, v1_orders_2: $i > $o).
% 0.46/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.68  thf(v2_lattice3_type, type, v2_lattice3: $i > $o).
% 0.46/0.68  thf(r3_orders_2_type, type, r3_orders_2: $i > $i > $i > $o).
% 0.46/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.46/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.46/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.68  thf(t7_yellow_1, conjecture,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.68       ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.46/0.68         ( ![B:$i]:
% 0.46/0.68           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.46/0.68             ( ![C:$i]:
% 0.46/0.68               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.46/0.68                 ( r1_tarski @
% 0.46/0.68                   ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 0.46/0.68                   ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ))).
% 0.46/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.68    (~( ![A:$i]:
% 0.46/0.68        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.68          ( ( v2_lattice3 @ ( k2_yellow_1 @ A ) ) =>
% 0.46/0.68            ( ![B:$i]:
% 0.46/0.68              ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.46/0.68                ( ![C:$i]:
% 0.46/0.68                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.46/0.68                    ( r1_tarski @
% 0.46/0.68                      ( k11_lattice3 @ ( k2_yellow_1 @ A ) @ B @ C ) @ 
% 0.46/0.68                      ( k3_xboole_0 @ B @ C ) ) ) ) ) ) ) ) )),
% 0.46/0.68    inference('cnf.neg', [status(esa)], [t7_yellow_1])).
% 0.46/0.68  thf('0', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('1', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(dt_k11_lattice3, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.46/0.68         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.68       ( m1_subset_1 @ ( k11_lattice3 @ A @ B @ C ) @ ( u1_struct_0 @ A ) ) ))).
% 0.46/0.68  thf('2', plain,
% 0.46/0.68      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 0.46/0.68          | ~ (l1_orders_2 @ X14)
% 0.46/0.68          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 0.46/0.68          | (m1_subset_1 @ (k11_lattice3 @ X14 @ X13 @ X15) @ 
% 0.46/0.68             (u1_struct_0 @ X14)))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k11_lattice3])).
% 0.46/0.68  thf('3', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 0.46/0.68           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.46/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.46/0.68          | ~ (l1_orders_2 @ (k2_yellow_1 @ sk_A)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.68  thf(dt_k2_yellow_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( l1_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.46/0.68       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.46/0.68  thf('4', plain, (![X23 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X23))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.68  thf('5', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ X0) @ 
% 0.46/0.68           (u1_struct_0 @ (k2_yellow_1 @ sk_A)))
% 0.46/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ (k2_yellow_1 @ sk_A))))),
% 0.46/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.46/0.68  thf('6', plain,
% 0.46/0.68      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.68        (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['0', '5'])).
% 0.46/0.68  thf(d1_yellow_1, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( k2_yellow_1 @ A ) = ( g1_orders_2 @ A @ ( k1_yellow_1 @ A ) ) ))).
% 0.46/0.68  thf('7', plain,
% 0.46/0.68      (![X21 : $i]:
% 0.46/0.68         ((k2_yellow_1 @ X21) = (g1_orders_2 @ X21 @ (k1_yellow_1 @ X21)))),
% 0.46/0.68      inference('cnf', [status(esa)], [d1_yellow_1])).
% 0.46/0.68  thf(abstractness_v1_orders_2, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( l1_orders_2 @ A ) =>
% 0.46/0.68       ( ( v1_orders_2 @ A ) =>
% 0.46/0.68         ( ( A ) = ( g1_orders_2 @ ( u1_struct_0 @ A ) @ ( u1_orders_2 @ A ) ) ) ) ))).
% 0.46/0.68  thf('8', plain,
% 0.46/0.68      (![X3 : $i]:
% 0.46/0.68         (~ (v1_orders_2 @ X3)
% 0.46/0.68          | ((X3) = (g1_orders_2 @ (u1_struct_0 @ X3) @ (u1_orders_2 @ X3)))
% 0.46/0.68          | ~ (l1_orders_2 @ X3))),
% 0.46/0.68      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 0.46/0.68  thf('9', plain,
% 0.46/0.68      (![X21 : $i]:
% 0.46/0.68         ((k2_yellow_1 @ X21) = (g1_orders_2 @ X21 @ (k1_yellow_1 @ X21)))),
% 0.46/0.68      inference('cnf', [status(esa)], [d1_yellow_1])).
% 0.46/0.68  thf(dt_u1_orders_2, axiom,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( l1_orders_2 @ A ) =>
% 0.46/0.68       ( m1_subset_1 @
% 0.46/0.68         ( u1_orders_2 @ A ) @ 
% 0.46/0.68         ( k1_zfmisc_1 @
% 0.46/0.68           ( k2_zfmisc_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.46/0.68  thf('10', plain,
% 0.46/0.68      (![X4 : $i]:
% 0.46/0.68         ((m1_subset_1 @ (u1_orders_2 @ X4) @ 
% 0.46/0.68           (k1_zfmisc_1 @ 
% 0.46/0.68            (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X4))))
% 0.46/0.68          | ~ (l1_orders_2 @ X4))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.46/0.68  thf(free_g1_orders_2, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) =>
% 0.46/0.68       ( ![C:$i,D:$i]:
% 0.46/0.68         ( ( ( g1_orders_2 @ A @ B ) = ( g1_orders_2 @ C @ D ) ) =>
% 0.46/0.68           ( ( ( A ) = ( C ) ) & ( ( B ) = ( D ) ) ) ) ) ))).
% 0.46/0.68  thf('11', plain,
% 0.46/0.68      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.68         (((g1_orders_2 @ X7 @ X8) != (g1_orders_2 @ X5 @ X6))
% 0.46/0.68          | ((X8) = (X6))
% 0.46/0.68          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X7))))),
% 0.46/0.68      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.46/0.68  thf('12', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         (~ (l1_orders_2 @ X0)
% 0.46/0.68          | ((u1_orders_2 @ X0) = (X1))
% 0.46/0.68          | ((g1_orders_2 @ (u1_struct_0 @ X0) @ (u1_orders_2 @ X0))
% 0.46/0.68              != (g1_orders_2 @ X2 @ X1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.46/0.68  thf('13', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (((g1_orders_2 @ (u1_struct_0 @ X1) @ (u1_orders_2 @ X1))
% 0.46/0.68            != (k2_yellow_1 @ X0))
% 0.46/0.68          | ((u1_orders_2 @ X1) = (k1_yellow_1 @ X0))
% 0.46/0.68          | ~ (l1_orders_2 @ X1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['9', '12'])).
% 0.46/0.68  thf('14', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (((X0) != (k2_yellow_1 @ X1))
% 0.46/0.68          | ~ (l1_orders_2 @ X0)
% 0.46/0.68          | ~ (v1_orders_2 @ X0)
% 0.46/0.68          | ~ (l1_orders_2 @ X0)
% 0.46/0.68          | ((u1_orders_2 @ X0) = (k1_yellow_1 @ X1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['8', '13'])).
% 0.46/0.68  thf('15', plain,
% 0.46/0.68      (![X1 : $i]:
% 0.46/0.68         (((u1_orders_2 @ (k2_yellow_1 @ X1)) = (k1_yellow_1 @ X1))
% 0.46/0.68          | ~ (v1_orders_2 @ (k2_yellow_1 @ X1))
% 0.46/0.68          | ~ (l1_orders_2 @ (k2_yellow_1 @ X1)))),
% 0.46/0.68      inference('simplify', [status(thm)], ['14'])).
% 0.46/0.68  thf('16', plain, (![X23 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X23))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.68  thf('17', plain, (![X22 : $i]: (v1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.68  thf('18', plain,
% 0.46/0.68      (![X1 : $i]: ((u1_orders_2 @ (k2_yellow_1 @ X1)) = (k1_yellow_1 @ X1))),
% 0.46/0.68      inference('simplify_reflect+', [status(thm)], ['15', '16', '17'])).
% 0.46/0.68  thf('19', plain,
% 0.46/0.68      (![X4 : $i]:
% 0.46/0.68         ((m1_subset_1 @ (u1_orders_2 @ X4) @ 
% 0.46/0.68           (k1_zfmisc_1 @ 
% 0.46/0.68            (k2_zfmisc_1 @ (u1_struct_0 @ X4) @ (u1_struct_0 @ X4))))
% 0.46/0.68          | ~ (l1_orders_2 @ X4))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_u1_orders_2])).
% 0.46/0.68  thf('20', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((m1_subset_1 @ (k1_yellow_1 @ X0) @ 
% 0.46/0.68           (k1_zfmisc_1 @ 
% 0.46/0.68            (k2_zfmisc_1 @ (u1_struct_0 @ (k2_yellow_1 @ X0)) @ 
% 0.46/0.68             (u1_struct_0 @ (k2_yellow_1 @ X0)))))
% 0.46/0.68          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['18', '19'])).
% 0.46/0.68  thf('21', plain, (![X23 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X23))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.68  thf('22', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (m1_subset_1 @ (k1_yellow_1 @ X0) @ 
% 0.46/0.68          (k1_zfmisc_1 @ 
% 0.46/0.68           (k2_zfmisc_1 @ (u1_struct_0 @ (k2_yellow_1 @ X0)) @ 
% 0.46/0.68            (u1_struct_0 @ (k2_yellow_1 @ X0)))))),
% 0.46/0.68      inference('demod', [status(thm)], ['20', '21'])).
% 0.46/0.68  thf('23', plain,
% 0.46/0.68      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.68         (((g1_orders_2 @ X7 @ X8) != (g1_orders_2 @ X5 @ X6))
% 0.46/0.68          | ((X7) = (X5))
% 0.46/0.68          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X7))))),
% 0.46/0.68      inference('cnf', [status(esa)], [free_g1_orders_2])).
% 0.46/0.68  thf('24', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         (((u1_struct_0 @ (k2_yellow_1 @ X0)) = (X1))
% 0.46/0.68          | ((g1_orders_2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)) @ 
% 0.46/0.68              (k1_yellow_1 @ X0)) != (g1_orders_2 @ X1 @ X2)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['22', '23'])).
% 0.46/0.68  thf('25', plain,
% 0.46/0.68      (![X1 : $i]: ((u1_orders_2 @ (k2_yellow_1 @ X1)) = (k1_yellow_1 @ X1))),
% 0.46/0.68      inference('simplify_reflect+', [status(thm)], ['15', '16', '17'])).
% 0.46/0.68  thf('26', plain,
% 0.46/0.68      (![X3 : $i]:
% 0.46/0.68         (~ (v1_orders_2 @ X3)
% 0.46/0.68          | ((X3) = (g1_orders_2 @ (u1_struct_0 @ X3) @ (u1_orders_2 @ X3)))
% 0.46/0.68          | ~ (l1_orders_2 @ X3))),
% 0.46/0.68      inference('cnf', [status(esa)], [abstractness_v1_orders_2])).
% 0.46/0.68  thf('27', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((k2_yellow_1 @ X0)
% 0.46/0.68            = (g1_orders_2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)) @ 
% 0.46/0.68               (k1_yellow_1 @ X0)))
% 0.46/0.68          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.46/0.68          | ~ (v1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['25', '26'])).
% 0.46/0.68  thf('28', plain, (![X23 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X23))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.68  thf('29', plain, (![X22 : $i]: (v1_orders_2 @ (k2_yellow_1 @ X22))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.68  thf('30', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k2_yellow_1 @ X0)
% 0.46/0.68           = (g1_orders_2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)) @ 
% 0.46/0.68              (k1_yellow_1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.46/0.68  thf('31', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.68         (((u1_struct_0 @ (k2_yellow_1 @ X0)) = (X1))
% 0.46/0.68          | ((k2_yellow_1 @ X0) != (g1_orders_2 @ X1 @ X2)))),
% 0.46/0.68      inference('demod', [status(thm)], ['24', '30'])).
% 0.46/0.68  thf('32', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (((k2_yellow_1 @ X1) != (k2_yellow_1 @ X0))
% 0.46/0.68          | ((u1_struct_0 @ (k2_yellow_1 @ X1)) = (X0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['7', '31'])).
% 0.46/0.68  thf('33', plain, (![X0 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.46/0.68      inference('eq_res', [status(thm)], ['32'])).
% 0.46/0.68  thf('34', plain,
% 0.46/0.68      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.68        sk_A)),
% 0.46/0.68      inference('demod', [status(thm)], ['6', '33'])).
% 0.46/0.69  thf('35', plain, (![X0 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.46/0.69      inference('eq_res', [status(thm)], ['32'])).
% 0.46/0.69  thf(l28_lattice3, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v5_orders_2 @ A ) & 
% 0.46/0.69         ( v2_lattice3 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.46/0.69       ( ![B:$i]:
% 0.46/0.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.69           ( ![C:$i]:
% 0.46/0.69             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.69               ( ![D:$i]:
% 0.46/0.69                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.69                   ( ( ( D ) = ( k11_lattice3 @ A @ B @ C ) ) <=>
% 0.46/0.69                     ( ( r1_orders_2 @ A @ D @ B ) & 
% 0.46/0.69                       ( r1_orders_2 @ A @ D @ C ) & 
% 0.46/0.69                       ( ![E:$i]:
% 0.46/0.69                         ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 0.46/0.69                           ( ( ( r1_orders_2 @ A @ E @ B ) & 
% 0.46/0.69                               ( r1_orders_2 @ A @ E @ C ) ) =>
% 0.46/0.69                             ( r1_orders_2 @ A @ E @ D ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.69  thf('36', plain,
% 0.46/0.69      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.46/0.69          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.46/0.69          | ((X18) != (k11_lattice3 @ X17 @ X16 @ X19))
% 0.46/0.69          | (r1_orders_2 @ X17 @ X18 @ X19)
% 0.46/0.69          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.46/0.69          | ~ (l1_orders_2 @ X17)
% 0.46/0.69          | ~ (v2_lattice3 @ X17)
% 0.46/0.69          | ~ (v5_orders_2 @ X17)
% 0.46/0.69          | (v2_struct_0 @ X17))),
% 0.46/0.69      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.46/0.69  thf('37', plain,
% 0.46/0.69      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.46/0.69         ((v2_struct_0 @ X17)
% 0.46/0.69          | ~ (v5_orders_2 @ X17)
% 0.46/0.69          | ~ (v2_lattice3 @ X17)
% 0.46/0.69          | ~ (l1_orders_2 @ X17)
% 0.46/0.69          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.46/0.69          | (r1_orders_2 @ X17 @ (k11_lattice3 @ X17 @ X16 @ X19) @ X19)
% 0.46/0.69          | ~ (m1_subset_1 @ (k11_lattice3 @ X17 @ X16 @ X19) @ 
% 0.46/0.69               (u1_struct_0 @ X17))
% 0.46/0.69          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17)))),
% 0.46/0.69      inference('simplify', [status(thm)], ['36'])).
% 0.46/0.69  thf('38', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X0)
% 0.46/0.69          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.46/0.69          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.46/0.69             (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X1)
% 0.46/0.69          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.46/0.69          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.46/0.69          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 0.46/0.69          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.46/0.69          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['35', '37'])).
% 0.46/0.69  thf('39', plain, (![X0 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.46/0.69      inference('eq_res', [status(thm)], ['32'])).
% 0.46/0.69  thf('40', plain, (![X0 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.46/0.69      inference('eq_res', [status(thm)], ['32'])).
% 0.46/0.69  thf('41', plain, (![X23 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X23))),
% 0.46/0.69      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.69  thf(fc5_yellow_1, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( v5_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.46/0.69       ( v4_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.46/0.69       ( v3_orders_2 @ ( k2_yellow_1 @ A ) ) & 
% 0.46/0.69       ( v1_orders_2 @ ( k2_yellow_1 @ A ) ) ))).
% 0.46/0.69  thf('42', plain, (![X27 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X27))),
% 0.46/0.69      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.46/0.69  thf('43', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X0)
% 0.46/0.69          | ~ (m1_subset_1 @ X2 @ X0)
% 0.46/0.69          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.46/0.69             (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X1)
% 0.46/0.69          | ~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.69          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 0.46/0.69          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.46/0.69      inference('demod', [status(thm)], ['38', '39', '40', '41', '42'])).
% 0.46/0.69  thf('44', plain,
% 0.46/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.69        | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.46/0.69        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.46/0.69        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.46/0.69           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.46/0.69        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['34', '43'])).
% 0.46/0.69  thf('45', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('46', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_C @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('47', plain, (![X0 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.46/0.69      inference('eq_res', [status(thm)], ['32'])).
% 0.46/0.69  thf('48', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.46/0.69      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.69  thf('49', plain,
% 0.46/0.69      ((m1_subset_1 @ sk_B @ (u1_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('50', plain, (![X0 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.46/0.69      inference('eq_res', [status(thm)], ['32'])).
% 0.46/0.69  thf('51', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.46/0.69      inference('demod', [status(thm)], ['49', '50'])).
% 0.46/0.69  thf('52', plain,
% 0.46/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.69        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.46/0.69           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 0.46/0.69      inference('demod', [status(thm)], ['44', '45', '48', '51'])).
% 0.46/0.69  thf('53', plain, (![X0 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.46/0.69      inference('eq_res', [status(thm)], ['32'])).
% 0.46/0.69  thf(redefinition_r3_orders_2, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i]:
% 0.46/0.69     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.46/0.69         ( l1_orders_2 @ A ) & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 0.46/0.69         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 0.46/0.69       ( ( r3_orders_2 @ A @ B @ C ) <=> ( r1_orders_2 @ A @ B @ C ) ) ))).
% 0.46/0.69  thf('54', plain,
% 0.46/0.69      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.46/0.69          | ~ (l1_orders_2 @ X10)
% 0.46/0.69          | ~ (v3_orders_2 @ X10)
% 0.46/0.69          | (v2_struct_0 @ X10)
% 0.46/0.69          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.46/0.69          | (r3_orders_2 @ X10 @ X9 @ X11)
% 0.46/0.69          | ~ (r1_orders_2 @ X10 @ X9 @ X11))),
% 0.46/0.69      inference('cnf', [status(esa)], [redefinition_r3_orders_2])).
% 0.46/0.69  thf('55', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.69          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.46/0.69          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.46/0.69          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.46/0.69          | (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.46/0.69          | ~ (v3_orders_2 @ (k2_yellow_1 @ X0))
% 0.46/0.69          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['53', '54'])).
% 0.46/0.69  thf('56', plain, (![X0 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.46/0.69      inference('eq_res', [status(thm)], ['32'])).
% 0.46/0.69  thf('57', plain, (![X25 : $i]: (v3_orders_2 @ (k2_yellow_1 @ X25))),
% 0.46/0.69      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.46/0.69  thf('58', plain, (![X23 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X23))),
% 0.46/0.69      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.69  thf('59', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.69          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.46/0.69          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.46/0.69          | ~ (m1_subset_1 @ X2 @ X0)
% 0.46/0.69          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.46/0.69      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.46/0.69  thf('60', plain,
% 0.46/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.69        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.69        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.46/0.69        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.46/0.69           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.46/0.69        | ~ (m1_subset_1 @ 
% 0.46/0.69             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['52', '59'])).
% 0.46/0.69  thf('61', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.46/0.69      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.69  thf('62', plain,
% 0.46/0.69      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69        sk_A)),
% 0.46/0.69      inference('demod', [status(thm)], ['6', '33'])).
% 0.46/0.69  thf('63', plain,
% 0.46/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.69        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.69        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.46/0.69           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C))),
% 0.46/0.69      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.46/0.69  thf('64', plain,
% 0.46/0.69      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.46/0.69         (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.46/0.69        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.46/0.69      inference('simplify', [status(thm)], ['63'])).
% 0.46/0.69  thf(t3_yellow_1, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.69       ( ![B:$i]:
% 0.46/0.69         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.46/0.69           ( ![C:$i]:
% 0.46/0.69             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ ( k2_yellow_1 @ A ) ) ) =>
% 0.46/0.69               ( ( r3_orders_2 @ ( k2_yellow_1 @ A ) @ B @ C ) <=>
% 0.46/0.69                 ( r1_tarski @ B @ C ) ) ) ) ) ) ))).
% 0.46/0.69  thf('65', plain,
% 0.46/0.69      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X28 @ (u1_struct_0 @ (k2_yellow_1 @ X29)))
% 0.46/0.69          | ~ (r3_orders_2 @ (k2_yellow_1 @ X29) @ X28 @ X30)
% 0.46/0.69          | (r1_tarski @ X28 @ X30)
% 0.46/0.69          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ (k2_yellow_1 @ X29)))
% 0.46/0.69          | (v1_xboole_0 @ X29))),
% 0.46/0.69      inference('cnf', [status(esa)], [t3_yellow_1])).
% 0.46/0.69  thf('66', plain, (![X0 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.46/0.69      inference('eq_res', [status(thm)], ['32'])).
% 0.46/0.69  thf('67', plain, (![X0 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.46/0.69      inference('eq_res', [status(thm)], ['32'])).
% 0.46/0.69  thf('68', plain,
% 0.46/0.69      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X28 @ X29)
% 0.46/0.69          | ~ (r3_orders_2 @ (k2_yellow_1 @ X29) @ X28 @ X30)
% 0.46/0.69          | (r1_tarski @ X28 @ X30)
% 0.46/0.69          | ~ (m1_subset_1 @ X30 @ X29)
% 0.46/0.69          | (v1_xboole_0 @ X29))),
% 0.46/0.69      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.46/0.69  thf('69', plain,
% 0.46/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.69        | (v1_xboole_0 @ sk_A)
% 0.46/0.69        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.46/0.69        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69           sk_C)
% 0.46/0.69        | ~ (m1_subset_1 @ 
% 0.46/0.69             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['64', '68'])).
% 0.46/0.69  thf('70', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.46/0.69      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.69  thf('71', plain,
% 0.46/0.69      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69        sk_A)),
% 0.46/0.69      inference('demod', [status(thm)], ['6', '33'])).
% 0.46/0.69  thf('72', plain,
% 0.46/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.69        | (v1_xboole_0 @ sk_A)
% 0.46/0.69        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69           sk_C))),
% 0.46/0.69      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.46/0.69  thf('73', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('74', plain,
% 0.46/0.69      (((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_C)
% 0.46/0.69        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.46/0.69      inference('clc', [status(thm)], ['72', '73'])).
% 0.46/0.69  thf('75', plain,
% 0.46/0.69      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69        sk_A)),
% 0.46/0.69      inference('demod', [status(thm)], ['6', '33'])).
% 0.46/0.69  thf('76', plain, (![X0 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.46/0.69      inference('eq_res', [status(thm)], ['32'])).
% 0.46/0.69  thf('77', plain,
% 0.46/0.69      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 0.46/0.69          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 0.46/0.69          | ((X18) != (k11_lattice3 @ X17 @ X16 @ X19))
% 0.46/0.69          | (r1_orders_2 @ X17 @ X18 @ X16)
% 0.46/0.69          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.46/0.69          | ~ (l1_orders_2 @ X17)
% 0.46/0.69          | ~ (v2_lattice3 @ X17)
% 0.46/0.69          | ~ (v5_orders_2 @ X17)
% 0.46/0.69          | (v2_struct_0 @ X17))),
% 0.46/0.69      inference('cnf', [status(esa)], [l28_lattice3])).
% 0.46/0.69  thf('78', plain,
% 0.46/0.69      (![X16 : $i, X17 : $i, X19 : $i]:
% 0.46/0.69         ((v2_struct_0 @ X17)
% 0.46/0.69          | ~ (v5_orders_2 @ X17)
% 0.46/0.69          | ~ (v2_lattice3 @ X17)
% 0.46/0.69          | ~ (l1_orders_2 @ X17)
% 0.46/0.69          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 0.46/0.69          | (r1_orders_2 @ X17 @ (k11_lattice3 @ X17 @ X16 @ X19) @ X16)
% 0.46/0.69          | ~ (m1_subset_1 @ (k11_lattice3 @ X17 @ X16 @ X19) @ 
% 0.46/0.69               (u1_struct_0 @ X17))
% 0.46/0.69          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17)))),
% 0.46/0.69      inference('simplify', [status(thm)], ['77'])).
% 0.46/0.69  thf('79', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X0)
% 0.46/0.69          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.46/0.69          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.46/0.69             (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X2)
% 0.46/0.69          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ (k2_yellow_1 @ X0)))
% 0.46/0.69          | ~ (l1_orders_2 @ (k2_yellow_1 @ X0))
% 0.46/0.69          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 0.46/0.69          | ~ (v5_orders_2 @ (k2_yellow_1 @ X0))
% 0.46/0.69          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['76', '78'])).
% 0.46/0.69  thf('80', plain, (![X0 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.46/0.69      inference('eq_res', [status(thm)], ['32'])).
% 0.46/0.69  thf('81', plain, (![X0 : $i]: ((u1_struct_0 @ (k2_yellow_1 @ X0)) = (X0))),
% 0.46/0.69      inference('eq_res', [status(thm)], ['32'])).
% 0.46/0.69  thf('82', plain, (![X23 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X23))),
% 0.46/0.69      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.69  thf('83', plain, (![X27 : $i]: (v5_orders_2 @ (k2_yellow_1 @ X27))),
% 0.46/0.69      inference('cnf', [status(esa)], [fc5_yellow_1])).
% 0.46/0.69  thf('84', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X0)
% 0.46/0.69          | ~ (m1_subset_1 @ X2 @ X0)
% 0.46/0.69          | (r1_orders_2 @ (k2_yellow_1 @ X0) @ 
% 0.46/0.69             (k11_lattice3 @ (k2_yellow_1 @ X0) @ X2 @ X1) @ X2)
% 0.46/0.69          | ~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.69          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0))
% 0.46/0.69          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.46/0.69      inference('demod', [status(thm)], ['79', '80', '81', '82', '83'])).
% 0.46/0.69  thf('85', plain,
% 0.46/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.69        | ~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))
% 0.46/0.69        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.46/0.69        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.46/0.69           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.46/0.69        | ~ (m1_subset_1 @ sk_B @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['75', '84'])).
% 0.46/0.69  thf('86', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('87', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.46/0.69      inference('demod', [status(thm)], ['46', '47'])).
% 0.46/0.69  thf('88', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.46/0.69      inference('demod', [status(thm)], ['49', '50'])).
% 0.46/0.69  thf('89', plain,
% 0.46/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.69        | (r1_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.46/0.69           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 0.46/0.69      inference('demod', [status(thm)], ['85', '86', '87', '88'])).
% 0.46/0.69  thf('90', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X1 @ X0)
% 0.46/0.69          | ~ (r1_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.46/0.69          | (r3_orders_2 @ (k2_yellow_1 @ X0) @ X1 @ X2)
% 0.46/0.69          | ~ (m1_subset_1 @ X2 @ X0)
% 0.46/0.69          | (v2_struct_0 @ (k2_yellow_1 @ X0)))),
% 0.46/0.69      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.46/0.69  thf('91', plain,
% 0.46/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.69        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.69        | ~ (m1_subset_1 @ sk_B @ sk_A)
% 0.46/0.69        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.46/0.69           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.46/0.69        | ~ (m1_subset_1 @ 
% 0.46/0.69             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['89', '90'])).
% 0.46/0.69  thf('92', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.46/0.69      inference('demod', [status(thm)], ['49', '50'])).
% 0.46/0.69  thf('93', plain,
% 0.46/0.69      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69        sk_A)),
% 0.46/0.69      inference('demod', [status(thm)], ['6', '33'])).
% 0.46/0.69  thf('94', plain,
% 0.46/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.69        | (v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.69        | (r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.46/0.69           (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B))),
% 0.46/0.69      inference('demod', [status(thm)], ['91', '92', '93'])).
% 0.46/0.69  thf('95', plain,
% 0.46/0.69      (((r3_orders_2 @ (k2_yellow_1 @ sk_A) @ 
% 0.46/0.69         (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.46/0.69        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.46/0.69      inference('simplify', [status(thm)], ['94'])).
% 0.46/0.69  thf('96', plain,
% 0.46/0.69      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.69         (~ (m1_subset_1 @ X28 @ X29)
% 0.46/0.69          | ~ (r3_orders_2 @ (k2_yellow_1 @ X29) @ X28 @ X30)
% 0.46/0.69          | (r1_tarski @ X28 @ X30)
% 0.46/0.69          | ~ (m1_subset_1 @ X30 @ X29)
% 0.46/0.69          | (v1_xboole_0 @ X29))),
% 0.46/0.69      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.46/0.69  thf('97', plain,
% 0.46/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.69        | (v1_xboole_0 @ sk_A)
% 0.46/0.69        | ~ (m1_subset_1 @ sk_B @ sk_A)
% 0.46/0.69        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69           sk_B)
% 0.46/0.69        | ~ (m1_subset_1 @ 
% 0.46/0.69             (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['95', '96'])).
% 0.46/0.69  thf('98', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.46/0.69      inference('demod', [status(thm)], ['49', '50'])).
% 0.46/0.69  thf('99', plain,
% 0.46/0.69      ((m1_subset_1 @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69        sk_A)),
% 0.46/0.69      inference('demod', [status(thm)], ['6', '33'])).
% 0.46/0.69  thf('100', plain,
% 0.46/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.69        | (v1_xboole_0 @ sk_A)
% 0.46/0.69        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69           sk_B))),
% 0.46/0.69      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.46/0.69  thf('101', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('102', plain,
% 0.46/0.69      (((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ sk_B)
% 0.46/0.69        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.46/0.69      inference('clc', [status(thm)], ['100', '101'])).
% 0.46/0.69  thf(t19_xboole_1, axiom,
% 0.46/0.69    (![A:$i,B:$i,C:$i]:
% 0.46/0.69     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 0.46/0.69       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.46/0.69  thf('103', plain,
% 0.46/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.69         (~ (r1_tarski @ X0 @ X1)
% 0.46/0.69          | ~ (r1_tarski @ X0 @ X2)
% 0.46/0.69          | (r1_tarski @ X0 @ (k3_xboole_0 @ X1 @ X2)))),
% 0.46/0.69      inference('cnf', [status(esa)], [t19_xboole_1])).
% 0.46/0.69  thf('104', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         ((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.69          | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69             (k3_xboole_0 @ sk_B @ X0))
% 0.46/0.69          | ~ (r1_tarski @ 
% 0.46/0.69               (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ X0))),
% 0.46/0.69      inference('sup-', [status(thm)], ['102', '103'])).
% 0.46/0.69  thf('105', plain,
% 0.46/0.69      (((v2_struct_0 @ (k2_yellow_1 @ sk_A))
% 0.46/0.69        | (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69           (k3_xboole_0 @ sk_B @ sk_C))
% 0.46/0.69        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['74', '104'])).
% 0.46/0.69  thf('106', plain,
% 0.46/0.69      (((r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69         (k3_xboole_0 @ sk_B @ sk_C))
% 0.46/0.69        | (v2_struct_0 @ (k2_yellow_1 @ sk_A)))),
% 0.46/0.69      inference('simplify', [status(thm)], ['105'])).
% 0.46/0.69  thf('107', plain,
% 0.46/0.69      (~ (r1_tarski @ (k11_lattice3 @ (k2_yellow_1 @ sk_A) @ sk_B @ sk_C) @ 
% 0.46/0.69          (k3_xboole_0 @ sk_B @ sk_C))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('108', plain, ((v2_struct_0 @ (k2_yellow_1 @ sk_A))),
% 0.46/0.69      inference('clc', [status(thm)], ['106', '107'])).
% 0.46/0.69  thf('109', plain, (![X23 : $i]: (l1_orders_2 @ (k2_yellow_1 @ X23))),
% 0.46/0.69      inference('cnf', [status(esa)], [dt_k2_yellow_1])).
% 0.46/0.69  thf(cc2_lattice3, axiom,
% 0.46/0.69    (![A:$i]:
% 0.46/0.69     ( ( l1_orders_2 @ A ) =>
% 0.46/0.69       ( ( v2_lattice3 @ A ) => ( ~( v2_struct_0 @ A ) ) ) ))).
% 0.46/0.69  thf('110', plain,
% 0.46/0.69      (![X12 : $i]:
% 0.46/0.69         (~ (v2_lattice3 @ X12) | ~ (v2_struct_0 @ X12) | ~ (l1_orders_2 @ X12))),
% 0.46/0.69      inference('cnf', [status(esa)], [cc2_lattice3])).
% 0.46/0.69  thf('111', plain,
% 0.46/0.69      (![X0 : $i]:
% 0.46/0.69         (~ (v2_struct_0 @ (k2_yellow_1 @ X0))
% 0.46/0.69          | ~ (v2_lattice3 @ (k2_yellow_1 @ X0)))),
% 0.46/0.69      inference('sup-', [status(thm)], ['109', '110'])).
% 0.46/0.69  thf('112', plain, (~ (v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.46/0.69      inference('sup-', [status(thm)], ['108', '111'])).
% 0.46/0.69  thf('113', plain, ((v2_lattice3 @ (k2_yellow_1 @ sk_A))),
% 0.46/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.69  thf('114', plain, ($false), inference('demod', [status(thm)], ['112', '113'])).
% 0.46/0.69  
% 0.46/0.69  % SZS output end Refutation
% 0.46/0.69  
% 0.46/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
