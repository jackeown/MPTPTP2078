%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.77qX8HRRzZ

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:35 EST 2020

% Result     : Theorem 14.14s
% Output     : Refutation 14.22s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 570 expanded)
%              Number of leaves         :   49 ( 179 expanded)
%              Depth                    :   24
%              Number of atoms          : 3112 (9953 expanded)
%              Number of equality atoms :   99 ( 312 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(a_2_5_lattice3_type,type,(
    a_2_5_lattice3: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(a_2_6_lattice3_type,type,(
    a_2_6_lattice3: $i > $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t47_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( ( k16_lattice3 @ A @ B )
            = ( k16_lattice3 @ A @ ( a_2_6_lattice3 @ A @ B ) ) )
          & ( ( k15_lattice3 @ A @ B )
            = ( k15_lattice3 @ A @ ( a_2_5_lattice3 @ A @ B ) ) ) ) ) )).

thf('0',plain,(
    ! [X40: $i,X42: $i] :
      ( ( ( k15_lattice3 @ X40 @ X42 )
        = ( k15_lattice3 @ X40 @ ( a_2_5_lattice3 @ X40 @ X42 ) ) )
      | ~ ( l3_lattices @ X40 )
      | ~ ( v4_lattice3 @ X40 )
      | ~ ( v10_lattices @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t47_lattice3])).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l3_lattices @ X28 )
      | ( v2_struct_0 @ X28 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X28 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(d13_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( ( v13_lattices @ A )
      <=> ? [B: $i] :
            ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( ( k2_lattices @ A @ B @ C )
                    = B )
                  & ( ( k2_lattices @ A @ C @ B )
                    = B ) ) )
            & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( sk_C_2 @ X22 @ X23 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( v13_lattices @ X23 )
      | ~ ( l1_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d13_lattices])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( m1_subset_1 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t43_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( ( k15_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
              = B )
            & ( ( k16_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
              = B ) ) ) ) )).

thf('5',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ( ( k15_lattice3 @ X36 @ ( k6_domain_1 @ ( u1_struct_0 @ X36 ) @ X35 ) )
        = X35 )
      | ~ ( l3_lattices @ X36 )
      | ~ ( v4_lattice3 @ X36 )
      | ~ ( v10_lattices @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t43_lattice3])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) )
        = ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) )
        = ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l3_lattices @ X28 )
      | ( v2_struct_0 @ X28 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X28 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t46_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( r3_lattices @ A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) )
            & ( r3_lattices @ A @ ( k16_lattice3 @ A @ C ) @ ( k16_lattice3 @ A @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( r1_tarski @ X37 @ X38 )
      | ( r3_lattices @ X39 @ ( k15_lattice3 @ X39 @ X37 ) @ ( k15_lattice3 @ X39 @ X38 ) )
      | ~ ( l3_lattices @ X39 )
      | ~ ( v4_lattice3 @ X39 )
      | ~ ( v10_lattices @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t46_lattice3])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l3_lattices @ X28 )
      | ( v2_struct_0 @ X28 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X28 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('13',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l3_lattices @ X28 )
      | ( v2_struct_0 @ X28 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X28 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(redefinition_r3_lattices,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A )
        & ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
        & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) )
     => ( ( r3_lattices @ A @ B @ C )
      <=> ( r1_lattices @ A @ B @ C ) ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v9_lattices @ X17 )
      | ~ ( v8_lattices @ X17 )
      | ~ ( v6_lattices @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( r1_lattices @ X17 @ X16 @ X18 )
      | ~ ( r3_lattices @ X17 @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v6_lattices @ X1 )
      | ~ ( v8_lattices @ X1 )
      | ~ ( v9_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X1 )
      | ~ ( v8_lattices @ X1 )
      | ~ ( v6_lattices @ X1 )
      | ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l3_lattices @ X28 )
      | ( v2_struct_0 @ X28 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X28 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(t21_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_lattices @ A @ B @ C )
              <=> ( ( k2_lattices @ A @ B @ C )
                  = B ) ) ) ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ~ ( r1_lattices @ X20 @ X19 @ X21 )
      | ( ( k2_lattices @ X20 @ X19 @ X21 )
        = X19 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v9_lattices @ X20 )
      | ~ ( v8_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v6_lattices @ X1 )
      | ~ ( v8_lattices @ X1 )
      | ~ ( v9_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v8_lattices @ X1 )
      | ~ ( v9_lattices @ X1 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( ( k2_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) )
        = ( k15_lattice3 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) )
        = ( k15_lattice3 @ X1 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v9_lattices @ X1 )
      | ~ ( v8_lattices @ X1 )
      | ~ ( v6_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['8','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l3_lattices @ X28 )
      | ( v2_struct_0 @ X28 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X28 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('30',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l3_lattices @ X28 )
      | ( v2_struct_0 @ X28 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X28 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(d6_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( ( v6_lattices @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( k2_lattices @ A @ B @ C )
                  = ( k2_lattices @ A @ C @ B ) ) ) ) ) ) )).

thf('31',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v6_lattices @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ( ( k2_lattices @ X25 @ X27 @ X26 )
        = ( k2_lattices @ X25 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d6_lattices])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ X2 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) ) )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ X2 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) ) )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
        = ( k2_lattices @ X0 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
        = ( k2_lattices @ X0 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) )
        = ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X40: $i,X42: $i] :
      ( ( ( k15_lattice3 @ X40 @ X42 )
        = ( k15_lattice3 @ X40 @ ( a_2_5_lattice3 @ X40 @ X42 ) ) )
      | ~ ( l3_lattices @ X40 )
      | ~ ( v4_lattice3 @ X40 )
      | ~ ( v10_lattices @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t47_lattice3])).

thf('45',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('46',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(fraenkel_a_2_5_lattice3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v10_lattices @ B )
        & ( v4_lattice3 @ B )
        & ( l3_lattices @ B ) )
     => ( ( r2_hidden @ A @ ( a_2_5_lattice3 @ B @ C ) )
      <=> ? [D: $i] :
            ( ? [E: $i] :
                ( ( r2_hidden @ E @ C )
                & ( r3_lattices @ B @ D @ E )
                & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('47',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( l3_lattices @ X30 )
      | ~ ( v4_lattice3 @ X30 )
      | ~ ( v10_lattices @ X30 )
      | ( v2_struct_0 @ X30 )
      | ( r2_hidden @ ( sk_E @ X31 @ X30 @ X32 ) @ X31 )
      | ~ ( r2_hidden @ X32 @ ( a_2_5_lattice3 @ X30 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_5_lattice3])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( a_2_5_lattice3 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E @ X0 @ X1 @ ( sk_C @ X2 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('49',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( r1_tarski @ ( a_2_5_lattice3 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ ( sk_E @ X0 @ X1 @ ( sk_C @ X2 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','50'])).

thf('52',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( a_2_5_lattice3 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X40: $i,X42: $i] :
      ( ( ( k15_lattice3 @ X40 @ X42 )
        = ( k15_lattice3 @ X40 @ ( a_2_5_lattice3 @ X40 @ X42 ) ) )
      | ~ ( l3_lattices @ X40 )
      | ~ ( v4_lattice3 @ X40 )
      | ~ ( v10_lattices @ X40 )
      | ( v2_struct_0 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t47_lattice3])).

thf('57',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l3_lattices @ X28 )
      | ( v2_struct_0 @ X28 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X28 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('58',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_lattices @ X23 @ ( sk_C_2 @ X22 @ X23 ) @ X22 )
       != X22 )
      | ( ( k2_lattices @ X23 @ X22 @ ( sk_C_2 @ X22 @ X23 ) )
       != X22 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( v13_lattices @ X23 )
      | ~ ( l1_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d13_lattices])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( ( k2_lattices @ X0 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
       != ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X1 @ ( sk_C_2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) )
       != ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l1_lattices @ X1 )
      | ( v13_lattices @ X1 )
      | ( ( k2_lattices @ X1 @ ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) @ ( sk_C_2 @ ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) @ X1 ) )
       != ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['56','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X1 @ ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) @ ( sk_C_2 @ ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) @ X1 ) )
       != ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) )
      | ( v13_lattices @ X1 )
      | ~ ( l1_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( ( k2_lattices @ X1 @ ( sk_C_2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) )
       != ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_lattices @ X0 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
       != ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf(t50_lattice3,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v13_lattices @ A )
        & ( l3_lattices @ A )
        & ( ( k5_lattices @ A )
          = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v13_lattices @ A )
          & ( l3_lattices @ A )
          & ( ( k5_lattices @ A )
            = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_lattice3])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( v13_lattices @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('79',plain,(
    ! [X15: $i] :
      ( ( l1_lattices @ X15 )
      | ~ ( l3_lattices @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('80',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf(cc1_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A ) )
       => ( ~ ( v2_struct_0 @ A )
          & ( v4_lattices @ A )
          & ( v5_lattices @ A )
          & ( v6_lattices @ A )
          & ( v7_lattices @ A )
          & ( v8_lattices @ A )
          & ( v9_lattices @ A ) ) ) ) )).

thf('81',plain,(
    ! [X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v6_lattices @ X10 )
      | ~ ( l3_lattices @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('82',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,(
    ! [X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v8_lattices @ X10 )
      | ~ ( l3_lattices @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ! [X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v9_lattices @ X10 )
      | ~ ( l3_lattices @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['74','75','76','77','80','86','92','98'])).

thf('100',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l3_lattices @ X28 )
      | ( v2_struct_0 @ X28 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X28 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(dt_k5_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('101',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf(d16_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( ( v13_lattices @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( B
                = ( k5_lattices @ A ) )
            <=> ! [C: $i] :
                  ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
                 => ( ( ( k2_lattices @ A @ B @ C )
                      = B )
                    & ( ( k2_lattices @ A @ C @ B )
                      = B ) ) ) ) ) ) ) )).

thf('102',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v13_lattices @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ( X12
       != ( k5_lattices @ X11 ) )
      | ( ( k2_lattices @ X11 @ X13 @ X12 )
        = X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d16_lattices])).

thf('103',plain,(
    ! [X11: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( l1_lattices @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( ( k2_lattices @ X11 @ X13 @ ( k5_lattices @ X11 ) )
        = ( k5_lattices @ X11 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X11 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v13_lattices @ X11 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['101','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['100','105'])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('109',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('110',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ( ( k15_lattice3 @ X36 @ ( k6_domain_1 @ ( u1_struct_0 @ X36 ) @ X35 ) )
        = X35 )
      | ~ ( l3_lattices @ X36 )
      | ~ ( v4_lattice3 @ X36 )
      | ~ ( v10_lattices @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t43_lattice3])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k5_lattices @ X0 ) ) )
        = ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k5_lattices @ X0 ) ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('117',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('118',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['108','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['107','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['129'])).

thf('131',plain,
    ( ( ( ( k5_lattices @ sk_A )
       != ( k5_lattices @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A )
      | ~ ( v13_lattices @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v6_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['128','130'])).

thf('132',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('134',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('137',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('138',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('139',plain,
    ( ( ( ( k5_lattices @ sk_A )
       != ( k5_lattices @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v13_lattices @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['131','132','133','134','135','136','137','138'])).

thf('140',plain,
    ( ( ~ ( v13_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,
    ( $false
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['99','142'])).

thf('144',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['129'])).

thf('145',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ~ ( l3_lattices @ sk_A )
   <= ~ ( l3_lattices @ sk_A ) ),
    inference(split,[status(esa)],['129'])).

thf('149',plain,(
    l3_lattices @ sk_A ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,
    ( ~ ( v10_lattices @ sk_A )
   <= ~ ( v10_lattices @ sk_A ) ),
    inference(split,[status(esa)],['129'])).

thf('152',plain,(
    v10_lattices @ sk_A ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['74','75','76','77','80','86','92','98'])).

thf('154',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ~ ( v13_lattices @ sk_A ) ),
    inference(split,[status(esa)],['129'])).

thf('155',plain,(
    v13_lattices @ sk_A ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['129'])).

thf('157',plain,(
    ( k5_lattices @ sk_A )
 != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ),
    inference('sat_resolution*',[status(thm)],['146','149','152','155','156'])).

thf('158',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['143','157'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.77qX8HRRzZ
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:31:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 14.14/14.37  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 14.14/14.37  % Solved by: fo/fo7.sh
% 14.14/14.37  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.14/14.37  % done 5987 iterations in 13.920s
% 14.14/14.37  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 14.14/14.37  % SZS output start Refutation
% 14.14/14.37  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 14.14/14.37  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 14.14/14.37  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 14.14/14.37  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 14.14/14.37  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 14.14/14.37  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 14.14/14.37  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 14.14/14.37  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 14.14/14.37  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 14.14/14.37  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 14.14/14.37  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 14.14/14.37  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 14.14/14.37  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 14.14/14.37  thf(a_2_5_lattice3_type, type, a_2_5_lattice3: $i > $i > $i).
% 14.14/14.37  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 14.14/14.37  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 14.14/14.37  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 14.14/14.37  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 14.14/14.37  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 14.14/14.37  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 14.14/14.37  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 14.14/14.37  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 14.14/14.37  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 14.14/14.37  thf(a_2_6_lattice3_type, type, a_2_6_lattice3: $i > $i > $i).
% 14.14/14.37  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 14.14/14.37  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 14.14/14.37  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 14.14/14.37  thf(sk_A_type, type, sk_A: $i).
% 14.14/14.37  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 14.14/14.37  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 14.14/14.37  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 14.14/14.37  thf(t47_lattice3, axiom,
% 14.14/14.37    (![A:$i]:
% 14.14/14.37     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 14.14/14.37         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 14.14/14.37       ( ![B:$i]:
% 14.14/14.37         ( ( ( k16_lattice3 @ A @ B ) =
% 14.14/14.37             ( k16_lattice3 @ A @ ( a_2_6_lattice3 @ A @ B ) ) ) & 
% 14.14/14.37           ( ( k15_lattice3 @ A @ B ) =
% 14.14/14.37             ( k15_lattice3 @ A @ ( a_2_5_lattice3 @ A @ B ) ) ) ) ) ))).
% 14.14/14.37  thf('0', plain,
% 14.14/14.37      (![X40 : $i, X42 : $i]:
% 14.14/14.37         (((k15_lattice3 @ X40 @ X42)
% 14.14/14.37            = (k15_lattice3 @ X40 @ (a_2_5_lattice3 @ X40 @ X42)))
% 14.14/14.37          | ~ (l3_lattices @ X40)
% 14.14/14.37          | ~ (v4_lattice3 @ X40)
% 14.14/14.37          | ~ (v10_lattices @ X40)
% 14.14/14.37          | (v2_struct_0 @ X40))),
% 14.14/14.37      inference('cnf', [status(esa)], [t47_lattice3])).
% 14.14/14.37  thf(dt_k15_lattice3, axiom,
% 14.14/14.37    (![A:$i,B:$i]:
% 14.14/14.37     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 14.14/14.37       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 14.14/14.37  thf('1', plain,
% 14.14/14.37      (![X28 : $i, X29 : $i]:
% 14.14/14.37         (~ (l3_lattices @ X28)
% 14.14/14.37          | (v2_struct_0 @ X28)
% 14.14/14.37          | (m1_subset_1 @ (k15_lattice3 @ X28 @ X29) @ (u1_struct_0 @ X28)))),
% 14.14/14.37      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 14.14/14.37  thf(d13_lattices, axiom,
% 14.22/14.37    (![A:$i]:
% 14.22/14.37     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 14.22/14.37       ( ( v13_lattices @ A ) <=>
% 14.22/14.37         ( ?[B:$i]:
% 14.22/14.37           ( ( ![C:$i]:
% 14.22/14.37               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 14.22/14.37                 ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 14.22/14.37                   ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) & 
% 14.22/14.37             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 14.22/14.37  thf('2', plain,
% 14.22/14.37      (![X22 : $i, X23 : $i]:
% 14.22/14.37         ((m1_subset_1 @ (sk_C_2 @ X22 @ X23) @ (u1_struct_0 @ X23))
% 14.22/14.37          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 14.22/14.37          | (v13_lattices @ X23)
% 14.22/14.37          | ~ (l1_lattices @ X23)
% 14.22/14.37          | (v2_struct_0 @ X23))),
% 14.22/14.37      inference('cnf', [status(esa)], [d13_lattices])).
% 14.22/14.37  thf('3', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         ((v2_struct_0 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ~ (l1_lattices @ X0)
% 14.22/14.37          | (v13_lattices @ X0)
% 14.22/14.37          | (m1_subset_1 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 14.22/14.37             (u1_struct_0 @ X0)))),
% 14.22/14.37      inference('sup-', [status(thm)], ['1', '2'])).
% 14.22/14.37  thf('4', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         ((m1_subset_1 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 14.22/14.37           (u1_struct_0 @ X0))
% 14.22/14.37          | (v13_lattices @ X0)
% 14.22/14.37          | ~ (l1_lattices @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0))),
% 14.22/14.37      inference('simplify', [status(thm)], ['3'])).
% 14.22/14.37  thf(t43_lattice3, axiom,
% 14.22/14.37    (![A:$i]:
% 14.22/14.37     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 14.22/14.37         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 14.22/14.37       ( ![B:$i]:
% 14.22/14.37         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 14.22/14.37           ( ( ( k15_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 14.22/14.37               ( B ) ) & 
% 14.22/14.37             ( ( k16_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 14.22/14.37               ( B ) ) ) ) ) ))).
% 14.22/14.37  thf('5', plain,
% 14.22/14.37      (![X35 : $i, X36 : $i]:
% 14.22/14.37         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X36))
% 14.22/14.37          | ((k15_lattice3 @ X36 @ (k6_domain_1 @ (u1_struct_0 @ X36) @ X35))
% 14.22/14.37              = (X35))
% 14.22/14.37          | ~ (l3_lattices @ X36)
% 14.22/14.37          | ~ (v4_lattice3 @ X36)
% 14.22/14.37          | ~ (v10_lattices @ X36)
% 14.22/14.37          | (v2_struct_0 @ X36))),
% 14.22/14.37      inference('cnf', [status(esa)], [t43_lattice3])).
% 14.22/14.37  thf('6', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         ((v2_struct_0 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | ~ (l1_lattices @ X0)
% 14.22/14.37          | (v13_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | ((k15_lattice3 @ X0 @ 
% 14.22/14.37              (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 14.22/14.37               (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 14.22/14.37              = (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0)))),
% 14.22/14.37      inference('sup-', [status(thm)], ['4', '5'])).
% 14.22/14.37  thf('7', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         (((k15_lattice3 @ X0 @ 
% 14.22/14.37            (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 14.22/14.37             (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 14.22/14.37            = (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | (v13_lattices @ X0)
% 14.22/14.37          | ~ (l1_lattices @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0))),
% 14.22/14.37      inference('simplify', [status(thm)], ['6'])).
% 14.22/14.37  thf('8', plain,
% 14.22/14.37      (![X28 : $i, X29 : $i]:
% 14.22/14.37         (~ (l3_lattices @ X28)
% 14.22/14.37          | (v2_struct_0 @ X28)
% 14.22/14.37          | (m1_subset_1 @ (k15_lattice3 @ X28 @ X29) @ (u1_struct_0 @ X28)))),
% 14.22/14.37      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 14.22/14.37  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 14.22/14.37  thf('9', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 14.22/14.37      inference('cnf', [status(esa)], [t2_xboole_1])).
% 14.22/14.37  thf(t46_lattice3, axiom,
% 14.22/14.37    (![A:$i]:
% 14.22/14.37     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 14.22/14.37         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 14.22/14.37       ( ![B:$i,C:$i]:
% 14.22/14.37         ( ( r1_tarski @ B @ C ) =>
% 14.22/14.37           ( ( r3_lattices @
% 14.22/14.37               A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) & 
% 14.22/14.37             ( r3_lattices @
% 14.22/14.37               A @ ( k16_lattice3 @ A @ C ) @ ( k16_lattice3 @ A @ B ) ) ) ) ) ))).
% 14.22/14.37  thf('10', plain,
% 14.22/14.37      (![X37 : $i, X38 : $i, X39 : $i]:
% 14.22/14.37         (~ (r1_tarski @ X37 @ X38)
% 14.22/14.37          | (r3_lattices @ X39 @ (k15_lattice3 @ X39 @ X37) @ 
% 14.22/14.37             (k15_lattice3 @ X39 @ X38))
% 14.22/14.37          | ~ (l3_lattices @ X39)
% 14.22/14.37          | ~ (v4_lattice3 @ X39)
% 14.22/14.37          | ~ (v10_lattices @ X39)
% 14.22/14.37          | (v2_struct_0 @ X39))),
% 14.22/14.37      inference('cnf', [status(esa)], [t46_lattice3])).
% 14.22/14.37  thf('11', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         ((v2_struct_0 @ X1)
% 14.22/14.37          | ~ (v10_lattices @ X1)
% 14.22/14.37          | ~ (v4_lattice3 @ X1)
% 14.22/14.37          | ~ (l3_lattices @ X1)
% 14.22/14.37          | (r3_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 14.22/14.37             (k15_lattice3 @ X1 @ X0)))),
% 14.22/14.37      inference('sup-', [status(thm)], ['9', '10'])).
% 14.22/14.37  thf('12', plain,
% 14.22/14.37      (![X28 : $i, X29 : $i]:
% 14.22/14.37         (~ (l3_lattices @ X28)
% 14.22/14.37          | (v2_struct_0 @ X28)
% 14.22/14.37          | (m1_subset_1 @ (k15_lattice3 @ X28 @ X29) @ (u1_struct_0 @ X28)))),
% 14.22/14.37      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 14.22/14.37  thf('13', plain,
% 14.22/14.37      (![X28 : $i, X29 : $i]:
% 14.22/14.37         (~ (l3_lattices @ X28)
% 14.22/14.37          | (v2_struct_0 @ X28)
% 14.22/14.37          | (m1_subset_1 @ (k15_lattice3 @ X28 @ X29) @ (u1_struct_0 @ X28)))),
% 14.22/14.37      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 14.22/14.37  thf(redefinition_r3_lattices, axiom,
% 14.22/14.37    (![A:$i,B:$i,C:$i]:
% 14.22/14.37     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 14.22/14.37         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 14.22/14.37         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 14.22/14.37         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 14.22/14.37       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 14.22/14.37  thf('14', plain,
% 14.22/14.37      (![X16 : $i, X17 : $i, X18 : $i]:
% 14.22/14.37         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 14.22/14.37          | ~ (l3_lattices @ X17)
% 14.22/14.37          | ~ (v9_lattices @ X17)
% 14.22/14.37          | ~ (v8_lattices @ X17)
% 14.22/14.37          | ~ (v6_lattices @ X17)
% 14.22/14.37          | (v2_struct_0 @ X17)
% 14.22/14.37          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 14.22/14.37          | (r1_lattices @ X17 @ X16 @ X18)
% 14.22/14.37          | ~ (r3_lattices @ X17 @ X16 @ X18))),
% 14.22/14.37      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 14.22/14.37  thf('15', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.37         ((v2_struct_0 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 14.22/14.37          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 14.22/14.37          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ~ (v6_lattices @ X0)
% 14.22/14.37          | ~ (v8_lattices @ X0)
% 14.22/14.37          | ~ (v9_lattices @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0))),
% 14.22/14.37      inference('sup-', [status(thm)], ['13', '14'])).
% 14.22/14.37  thf('16', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.37         (~ (v9_lattices @ X0)
% 14.22/14.37          | ~ (v8_lattices @ X0)
% 14.22/14.37          | ~ (v6_lattices @ X0)
% 14.22/14.37          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 14.22/14.37          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 14.22/14.37          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0))),
% 14.22/14.37      inference('simplify', [status(thm)], ['15'])).
% 14.22/14.37  thf('17', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.37         ((v2_struct_0 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 14.22/14.37               (k15_lattice3 @ X0 @ X1))
% 14.22/14.37          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 14.22/14.37             (k15_lattice3 @ X0 @ X1))
% 14.22/14.37          | ~ (v6_lattices @ X0)
% 14.22/14.37          | ~ (v8_lattices @ X0)
% 14.22/14.37          | ~ (v9_lattices @ X0))),
% 14.22/14.37      inference('sup-', [status(thm)], ['12', '16'])).
% 14.22/14.37  thf('18', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.37         (~ (v9_lattices @ X0)
% 14.22/14.37          | ~ (v8_lattices @ X0)
% 14.22/14.37          | ~ (v6_lattices @ X0)
% 14.22/14.37          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 14.22/14.37             (k15_lattice3 @ X0 @ X1))
% 14.22/14.37          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 14.22/14.37               (k15_lattice3 @ X0 @ X1))
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0))),
% 14.22/14.37      inference('simplify', [status(thm)], ['17'])).
% 14.22/14.37  thf('19', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         (~ (l3_lattices @ X1)
% 14.22/14.37          | ~ (v4_lattice3 @ X1)
% 14.22/14.37          | ~ (v10_lattices @ X1)
% 14.22/14.37          | (v2_struct_0 @ X1)
% 14.22/14.37          | (v2_struct_0 @ X1)
% 14.22/14.37          | ~ (l3_lattices @ X1)
% 14.22/14.37          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 14.22/14.37             (k15_lattice3 @ X1 @ X0))
% 14.22/14.37          | ~ (v6_lattices @ X1)
% 14.22/14.37          | ~ (v8_lattices @ X1)
% 14.22/14.37          | ~ (v9_lattices @ X1))),
% 14.22/14.37      inference('sup-', [status(thm)], ['11', '18'])).
% 14.22/14.37  thf('20', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         (~ (v9_lattices @ X1)
% 14.22/14.37          | ~ (v8_lattices @ X1)
% 14.22/14.37          | ~ (v6_lattices @ X1)
% 14.22/14.37          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 14.22/14.37             (k15_lattice3 @ X1 @ X0))
% 14.22/14.37          | (v2_struct_0 @ X1)
% 14.22/14.37          | ~ (v10_lattices @ X1)
% 14.22/14.37          | ~ (v4_lattice3 @ X1)
% 14.22/14.37          | ~ (l3_lattices @ X1))),
% 14.22/14.37      inference('simplify', [status(thm)], ['19'])).
% 14.22/14.37  thf('21', plain,
% 14.22/14.37      (![X28 : $i, X29 : $i]:
% 14.22/14.37         (~ (l3_lattices @ X28)
% 14.22/14.37          | (v2_struct_0 @ X28)
% 14.22/14.37          | (m1_subset_1 @ (k15_lattice3 @ X28 @ X29) @ (u1_struct_0 @ X28)))),
% 14.22/14.37      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 14.22/14.37  thf(t21_lattices, axiom,
% 14.22/14.37    (![A:$i]:
% 14.22/14.37     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 14.22/14.37         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 14.22/14.37       ( ![B:$i]:
% 14.22/14.37         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 14.22/14.37           ( ![C:$i]:
% 14.22/14.37             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 14.22/14.37               ( ( r1_lattices @ A @ B @ C ) <=>
% 14.22/14.37                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 14.22/14.37  thf('22', plain,
% 14.22/14.37      (![X19 : $i, X20 : $i, X21 : $i]:
% 14.22/14.37         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 14.22/14.37          | ~ (r1_lattices @ X20 @ X19 @ X21)
% 14.22/14.37          | ((k2_lattices @ X20 @ X19 @ X21) = (X19))
% 14.22/14.37          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 14.22/14.37          | ~ (l3_lattices @ X20)
% 14.22/14.37          | ~ (v9_lattices @ X20)
% 14.22/14.37          | ~ (v8_lattices @ X20)
% 14.22/14.37          | (v2_struct_0 @ X20))),
% 14.22/14.37      inference('cnf', [status(esa)], [t21_lattices])).
% 14.22/14.37  thf('23', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.37         ((v2_struct_0 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ~ (v8_lattices @ X0)
% 14.22/14.37          | ~ (v9_lattices @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 14.22/14.37          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 14.22/14.37              = (k15_lattice3 @ X0 @ X1))
% 14.22/14.37          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 14.22/14.37      inference('sup-', [status(thm)], ['21', '22'])).
% 14.22/14.37  thf('24', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.37         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 14.22/14.37          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 14.22/14.37              = (k15_lattice3 @ X0 @ X1))
% 14.22/14.37          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 14.22/14.37          | ~ (v9_lattices @ X0)
% 14.22/14.37          | ~ (v8_lattices @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0))),
% 14.22/14.37      inference('simplify', [status(thm)], ['23'])).
% 14.22/14.37  thf('25', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         (~ (l3_lattices @ X1)
% 14.22/14.37          | ~ (v4_lattice3 @ X1)
% 14.22/14.37          | ~ (v10_lattices @ X1)
% 14.22/14.37          | (v2_struct_0 @ X1)
% 14.22/14.37          | ~ (v6_lattices @ X1)
% 14.22/14.37          | ~ (v8_lattices @ X1)
% 14.22/14.37          | ~ (v9_lattices @ X1)
% 14.22/14.37          | (v2_struct_0 @ X1)
% 14.22/14.37          | ~ (l3_lattices @ X1)
% 14.22/14.37          | ~ (v8_lattices @ X1)
% 14.22/14.37          | ~ (v9_lattices @ X1)
% 14.22/14.37          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 14.22/14.37          | ((k2_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 14.22/14.37              (k15_lattice3 @ X1 @ X0)) = (k15_lattice3 @ X1 @ k1_xboole_0)))),
% 14.22/14.37      inference('sup-', [status(thm)], ['20', '24'])).
% 14.22/14.37  thf('26', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         (((k2_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 14.22/14.37            (k15_lattice3 @ X1 @ X0)) = (k15_lattice3 @ X1 @ k1_xboole_0))
% 14.22/14.37          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 14.22/14.37          | ~ (v9_lattices @ X1)
% 14.22/14.37          | ~ (v8_lattices @ X1)
% 14.22/14.37          | ~ (v6_lattices @ X1)
% 14.22/14.37          | (v2_struct_0 @ X1)
% 14.22/14.37          | ~ (v10_lattices @ X1)
% 14.22/14.37          | ~ (v4_lattice3 @ X1)
% 14.22/14.37          | ~ (l3_lattices @ X1))),
% 14.22/14.37      inference('simplify', [status(thm)], ['25'])).
% 14.22/14.37  thf('27', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         ((v2_struct_0 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ~ (v6_lattices @ X0)
% 14.22/14.37          | ~ (v8_lattices @ X0)
% 14.22/14.37          | ~ (v9_lattices @ X0)
% 14.22/14.37          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 14.22/14.37              (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 14.22/14.37      inference('sup-', [status(thm)], ['8', '26'])).
% 14.22/14.37  thf('28', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 14.22/14.37            (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 14.22/14.37          | ~ (v9_lattices @ X0)
% 14.22/14.37          | ~ (v8_lattices @ X0)
% 14.22/14.37          | ~ (v6_lattices @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0))),
% 14.22/14.37      inference('simplify', [status(thm)], ['27'])).
% 14.22/14.37  thf('29', plain,
% 14.22/14.37      (![X28 : $i, X29 : $i]:
% 14.22/14.37         (~ (l3_lattices @ X28)
% 14.22/14.37          | (v2_struct_0 @ X28)
% 14.22/14.37          | (m1_subset_1 @ (k15_lattice3 @ X28 @ X29) @ (u1_struct_0 @ X28)))),
% 14.22/14.37      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 14.22/14.37  thf('30', plain,
% 14.22/14.37      (![X28 : $i, X29 : $i]:
% 14.22/14.37         (~ (l3_lattices @ X28)
% 14.22/14.37          | (v2_struct_0 @ X28)
% 14.22/14.37          | (m1_subset_1 @ (k15_lattice3 @ X28 @ X29) @ (u1_struct_0 @ X28)))),
% 14.22/14.37      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 14.22/14.37  thf(d6_lattices, axiom,
% 14.22/14.37    (![A:$i]:
% 14.22/14.37     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 14.22/14.37       ( ( v6_lattices @ A ) <=>
% 14.22/14.37         ( ![B:$i]:
% 14.22/14.37           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 14.22/14.37             ( ![C:$i]:
% 14.22/14.37               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 14.22/14.37                 ( ( k2_lattices @ A @ B @ C ) = ( k2_lattices @ A @ C @ B ) ) ) ) ) ) ) ))).
% 14.22/14.37  thf('31', plain,
% 14.22/14.37      (![X25 : $i, X26 : $i, X27 : $i]:
% 14.22/14.37         (~ (v6_lattices @ X25)
% 14.22/14.37          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 14.22/14.37          | ((k2_lattices @ X25 @ X27 @ X26) = (k2_lattices @ X25 @ X26 @ X27))
% 14.22/14.37          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 14.22/14.37          | ~ (l1_lattices @ X25)
% 14.22/14.37          | (v2_struct_0 @ X25))),
% 14.22/14.37      inference('cnf', [status(esa)], [d6_lattices])).
% 14.22/14.37  thf('32', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.37         ((v2_struct_0 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ~ (l1_lattices @ X0)
% 14.22/14.37          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 14.22/14.37          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 14.22/14.37              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 14.22/14.37          | ~ (v6_lattices @ X0))),
% 14.22/14.37      inference('sup-', [status(thm)], ['30', '31'])).
% 14.22/14.37  thf('33', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.37         (~ (v6_lattices @ X0)
% 14.22/14.37          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 14.22/14.37              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 14.22/14.37          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 14.22/14.37          | ~ (l1_lattices @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0))),
% 14.22/14.37      inference('simplify', [status(thm)], ['32'])).
% 14.22/14.37  thf('34', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.37         ((v2_struct_0 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | ~ (l1_lattices @ X0)
% 14.22/14.37          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 14.22/14.37              (k15_lattice3 @ X0 @ X2))
% 14.22/14.37              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 14.22/14.37                 (k15_lattice3 @ X0 @ X1)))
% 14.22/14.37          | ~ (v6_lattices @ X0))),
% 14.22/14.37      inference('sup-', [status(thm)], ['29', '33'])).
% 14.22/14.37  thf('35', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.37         (~ (v6_lattices @ X0)
% 14.22/14.37          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 14.22/14.37              (k15_lattice3 @ X0 @ X2))
% 14.22/14.37              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 14.22/14.37                 (k15_lattice3 @ X0 @ X1)))
% 14.22/14.37          | ~ (l1_lattices @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0))),
% 14.22/14.37      inference('simplify', [status(thm)], ['34'])).
% 14.22/14.37  thf('36', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 14.22/14.37            = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 14.22/14.37               (k15_lattice3 @ X0 @ k1_xboole_0)))
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | ~ (v6_lattices @ X0)
% 14.22/14.37          | ~ (v8_lattices @ X0)
% 14.22/14.37          | ~ (v9_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | ~ (l1_lattices @ X0)
% 14.22/14.37          | ~ (v6_lattices @ X0))),
% 14.22/14.37      inference('sup+', [status(thm)], ['28', '35'])).
% 14.22/14.37  thf('37', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         (~ (l1_lattices @ X0)
% 14.22/14.37          | ~ (v9_lattices @ X0)
% 14.22/14.37          | ~ (v8_lattices @ X0)
% 14.22/14.37          | ~ (v6_lattices @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 14.22/14.37              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 14.22/14.37                 (k15_lattice3 @ X0 @ k1_xboole_0))))),
% 14.22/14.37      inference('simplify', [status(thm)], ['36'])).
% 14.22/14.37  thf('38', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 14.22/14.37            = (k2_lattices @ X0 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 14.22/14.37               (k15_lattice3 @ X0 @ k1_xboole_0)))
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | ~ (l1_lattices @ X0)
% 14.22/14.37          | (v13_lattices @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | ~ (v6_lattices @ X0)
% 14.22/14.37          | ~ (v8_lattices @ X0)
% 14.22/14.37          | ~ (v9_lattices @ X0)
% 14.22/14.37          | ~ (l1_lattices @ X0))),
% 14.22/14.37      inference('sup+', [status(thm)], ['7', '37'])).
% 14.22/14.37  thf('39', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         (~ (v9_lattices @ X0)
% 14.22/14.37          | ~ (v8_lattices @ X0)
% 14.22/14.37          | ~ (v6_lattices @ X0)
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | (v13_lattices @ X0)
% 14.22/14.37          | ~ (l1_lattices @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 14.22/14.37              = (k2_lattices @ X0 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 14.22/14.37                 (k15_lattice3 @ X0 @ k1_xboole_0))))),
% 14.22/14.37      inference('simplify', [status(thm)], ['38'])).
% 14.22/14.37  thf('40', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         (((k15_lattice3 @ X0 @ 
% 14.22/14.37            (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 14.22/14.37             (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 14.22/14.37            = (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | (v13_lattices @ X0)
% 14.22/14.37          | ~ (l1_lattices @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0))),
% 14.22/14.37      inference('simplify', [status(thm)], ['6'])).
% 14.22/14.37  thf('41', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 14.22/14.37            (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 14.22/14.37          | ~ (v9_lattices @ X0)
% 14.22/14.37          | ~ (v8_lattices @ X0)
% 14.22/14.37          | ~ (v6_lattices @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0))),
% 14.22/14.37      inference('simplify', [status(thm)], ['27'])).
% 14.22/14.37  thf('42', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 14.22/14.37            (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 14.22/14.37            = (k15_lattice3 @ X0 @ k1_xboole_0))
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | ~ (l1_lattices @ X0)
% 14.22/14.37          | (v13_lattices @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | ~ (v6_lattices @ X0)
% 14.22/14.37          | ~ (v8_lattices @ X0)
% 14.22/14.37          | ~ (v9_lattices @ X0))),
% 14.22/14.37      inference('sup+', [status(thm)], ['40', '41'])).
% 14.22/14.37  thf('43', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         (~ (v9_lattices @ X0)
% 14.22/14.37          | ~ (v8_lattices @ X0)
% 14.22/14.37          | ~ (v6_lattices @ X0)
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | (v13_lattices @ X0)
% 14.22/14.37          | ~ (l1_lattices @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 14.22/14.37              (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 14.22/14.37              = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 14.22/14.37      inference('simplify', [status(thm)], ['42'])).
% 14.22/14.37  thf('44', plain,
% 14.22/14.37      (![X40 : $i, X42 : $i]:
% 14.22/14.37         (((k15_lattice3 @ X40 @ X42)
% 14.22/14.37            = (k15_lattice3 @ X40 @ (a_2_5_lattice3 @ X40 @ X42)))
% 14.22/14.37          | ~ (l3_lattices @ X40)
% 14.22/14.37          | ~ (v4_lattice3 @ X40)
% 14.22/14.37          | ~ (v10_lattices @ X40)
% 14.22/14.37          | (v2_struct_0 @ X40))),
% 14.22/14.37      inference('cnf', [status(esa)], [t47_lattice3])).
% 14.22/14.37  thf('45', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 14.22/14.37      inference('cnf', [status(esa)], [t2_xboole_1])).
% 14.22/14.37  thf(d3_tarski, axiom,
% 14.22/14.37    (![A:$i,B:$i]:
% 14.22/14.37     ( ( r1_tarski @ A @ B ) <=>
% 14.22/14.37       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 14.22/14.37  thf('46', plain,
% 14.22/14.37      (![X1 : $i, X3 : $i]:
% 14.22/14.37         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 14.22/14.37      inference('cnf', [status(esa)], [d3_tarski])).
% 14.22/14.37  thf(fraenkel_a_2_5_lattice3, axiom,
% 14.22/14.37    (![A:$i,B:$i,C:$i]:
% 14.22/14.37     ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 14.22/14.37         ( v4_lattice3 @ B ) & ( l3_lattices @ B ) ) =>
% 14.22/14.37       ( ( r2_hidden @ A @ ( a_2_5_lattice3 @ B @ C ) ) <=>
% 14.22/14.37         ( ?[D:$i]:
% 14.22/14.37           ( ( ?[E:$i]:
% 14.22/14.37               ( ( r2_hidden @ E @ C ) & ( r3_lattices @ B @ D @ E ) & 
% 14.22/14.37                 ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 14.22/14.37             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 14.22/14.37  thf('47', plain,
% 14.22/14.37      (![X30 : $i, X31 : $i, X32 : $i]:
% 14.22/14.37         (~ (l3_lattices @ X30)
% 14.22/14.37          | ~ (v4_lattice3 @ X30)
% 14.22/14.37          | ~ (v10_lattices @ X30)
% 14.22/14.37          | (v2_struct_0 @ X30)
% 14.22/14.37          | (r2_hidden @ (sk_E @ X31 @ X30 @ X32) @ X31)
% 14.22/14.37          | ~ (r2_hidden @ X32 @ (a_2_5_lattice3 @ X30 @ X31)))),
% 14.22/14.37      inference('cnf', [status(esa)], [fraenkel_a_2_5_lattice3])).
% 14.22/14.37  thf('48', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.37         ((r1_tarski @ (a_2_5_lattice3 @ X1 @ X0) @ X2)
% 14.22/14.37          | (r2_hidden @ 
% 14.22/14.37             (sk_E @ X0 @ X1 @ (sk_C @ X2 @ (a_2_5_lattice3 @ X1 @ X0))) @ X0)
% 14.22/14.37          | (v2_struct_0 @ X1)
% 14.22/14.37          | ~ (v10_lattices @ X1)
% 14.22/14.37          | ~ (v4_lattice3 @ X1)
% 14.22/14.37          | ~ (l3_lattices @ X1))),
% 14.22/14.37      inference('sup-', [status(thm)], ['46', '47'])).
% 14.22/14.37  thf(t7_ordinal1, axiom,
% 14.22/14.37    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 14.22/14.37  thf('49', plain,
% 14.22/14.37      (![X8 : $i, X9 : $i]: (~ (r2_hidden @ X8 @ X9) | ~ (r1_tarski @ X9 @ X8))),
% 14.22/14.37      inference('cnf', [status(esa)], [t7_ordinal1])).
% 14.22/14.37  thf('50', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.37         (~ (l3_lattices @ X1)
% 14.22/14.37          | ~ (v4_lattice3 @ X1)
% 14.22/14.37          | ~ (v10_lattices @ X1)
% 14.22/14.37          | (v2_struct_0 @ X1)
% 14.22/14.37          | (r1_tarski @ (a_2_5_lattice3 @ X1 @ X0) @ X2)
% 14.22/14.37          | ~ (r1_tarski @ X0 @ 
% 14.22/14.37               (sk_E @ X0 @ X1 @ (sk_C @ X2 @ (a_2_5_lattice3 @ X1 @ X0)))))),
% 14.22/14.37      inference('sup-', [status(thm)], ['48', '49'])).
% 14.22/14.37  thf('51', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         ((r1_tarski @ (a_2_5_lattice3 @ X0 @ k1_xboole_0) @ X1)
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0))),
% 14.22/14.37      inference('sup-', [status(thm)], ['45', '50'])).
% 14.22/14.37  thf('52', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 14.22/14.37      inference('cnf', [status(esa)], [t2_xboole_1])).
% 14.22/14.37  thf(d10_xboole_0, axiom,
% 14.22/14.37    (![A:$i,B:$i]:
% 14.22/14.37     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 14.22/14.37  thf('53', plain,
% 14.22/14.37      (![X4 : $i, X6 : $i]:
% 14.22/14.37         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 14.22/14.37      inference('cnf', [status(esa)], [d10_xboole_0])).
% 14.22/14.37  thf('54', plain,
% 14.22/14.37      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 14.22/14.37      inference('sup-', [status(thm)], ['52', '53'])).
% 14.22/14.37  thf('55', plain,
% 14.22/14.37      (![X0 : $i]:
% 14.22/14.37         (~ (l3_lattices @ X0)
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ((a_2_5_lattice3 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 14.22/14.37      inference('sup-', [status(thm)], ['51', '54'])).
% 14.22/14.37  thf('56', plain,
% 14.22/14.37      (![X40 : $i, X42 : $i]:
% 14.22/14.37         (((k15_lattice3 @ X40 @ X42)
% 14.22/14.37            = (k15_lattice3 @ X40 @ (a_2_5_lattice3 @ X40 @ X42)))
% 14.22/14.37          | ~ (l3_lattices @ X40)
% 14.22/14.37          | ~ (v4_lattice3 @ X40)
% 14.22/14.37          | ~ (v10_lattices @ X40)
% 14.22/14.37          | (v2_struct_0 @ X40))),
% 14.22/14.37      inference('cnf', [status(esa)], [t47_lattice3])).
% 14.22/14.37  thf('57', plain,
% 14.22/14.37      (![X28 : $i, X29 : $i]:
% 14.22/14.37         (~ (l3_lattices @ X28)
% 14.22/14.37          | (v2_struct_0 @ X28)
% 14.22/14.37          | (m1_subset_1 @ (k15_lattice3 @ X28 @ X29) @ (u1_struct_0 @ X28)))),
% 14.22/14.37      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 14.22/14.37  thf('58', plain,
% 14.22/14.37      (![X22 : $i, X23 : $i]:
% 14.22/14.37         (((k2_lattices @ X23 @ (sk_C_2 @ X22 @ X23) @ X22) != (X22))
% 14.22/14.37          | ((k2_lattices @ X23 @ X22 @ (sk_C_2 @ X22 @ X23)) != (X22))
% 14.22/14.37          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 14.22/14.37          | (v13_lattices @ X23)
% 14.22/14.37          | ~ (l1_lattices @ X23)
% 14.22/14.37          | (v2_struct_0 @ X23))),
% 14.22/14.37      inference('cnf', [status(esa)], [d13_lattices])).
% 14.22/14.37  thf('59', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         ((v2_struct_0 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ~ (l1_lattices @ X0)
% 14.22/14.37          | (v13_lattices @ X0)
% 14.22/14.37          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 14.22/14.37              (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 14.22/14.37              != (k15_lattice3 @ X0 @ X1))
% 14.22/14.37          | ((k2_lattices @ X0 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 14.22/14.37              (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1)))),
% 14.22/14.37      inference('sup-', [status(thm)], ['57', '58'])).
% 14.22/14.37  thf('60', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         (((k2_lattices @ X0 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 14.22/14.37            (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1))
% 14.22/14.37          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 14.22/14.37              (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 14.22/14.37              != (k15_lattice3 @ X0 @ X1))
% 14.22/14.37          | (v13_lattices @ X0)
% 14.22/14.37          | ~ (l1_lattices @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0))),
% 14.22/14.37      inference('simplify', [status(thm)], ['59'])).
% 14.22/14.37  thf('61', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         (((k2_lattices @ X1 @ (sk_C_2 @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 14.22/14.37            (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)))
% 14.22/14.37            != (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)))
% 14.22/14.37          | (v2_struct_0 @ X1)
% 14.22/14.37          | ~ (v10_lattices @ X1)
% 14.22/14.37          | ~ (v4_lattice3 @ X1)
% 14.22/14.37          | ~ (l3_lattices @ X1)
% 14.22/14.37          | (v2_struct_0 @ X1)
% 14.22/14.37          | ~ (l3_lattices @ X1)
% 14.22/14.37          | ~ (l1_lattices @ X1)
% 14.22/14.37          | (v13_lattices @ X1)
% 14.22/14.37          | ((k2_lattices @ X1 @ 
% 14.22/14.37              (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)) @ 
% 14.22/14.37              (sk_C_2 @ (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)) @ X1))
% 14.22/14.37              != (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0))))),
% 14.22/14.37      inference('sup-', [status(thm)], ['56', '60'])).
% 14.22/14.37  thf('62', plain,
% 14.22/14.37      (![X0 : $i, X1 : $i]:
% 14.22/14.37         (((k2_lattices @ X1 @ 
% 14.22/14.37            (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)) @ 
% 14.22/14.37            (sk_C_2 @ (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)) @ X1))
% 14.22/14.37            != (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)))
% 14.22/14.37          | (v13_lattices @ X1)
% 14.22/14.37          | ~ (l1_lattices @ X1)
% 14.22/14.37          | ~ (l3_lattices @ X1)
% 14.22/14.37          | ~ (v4_lattice3 @ X1)
% 14.22/14.37          | ~ (v10_lattices @ X1)
% 14.22/14.37          | (v2_struct_0 @ X1)
% 14.22/14.37          | ((k2_lattices @ X1 @ (sk_C_2 @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 14.22/14.37              (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)))
% 14.22/14.37              != (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0))))),
% 14.22/14.37      inference('simplify', [status(thm)], ['61'])).
% 14.22/14.37  thf('63', plain,
% 14.22/14.37      (![X0 : $i]:
% 14.22/14.37         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 14.22/14.37            (sk_C_2 @ 
% 14.22/14.37             (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)) @ X0))
% 14.22/14.37            != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | ((k2_lattices @ X0 @ 
% 14.22/14.37              (sk_C_2 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 14.22/14.37              (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 14.22/14.37              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | ~ (l1_lattices @ X0)
% 14.22/14.37          | (v13_lattices @ X0))),
% 14.22/14.37      inference('sup-', [status(thm)], ['55', '62'])).
% 14.22/14.37  thf('64', plain,
% 14.22/14.37      (![X0 : $i]:
% 14.22/14.37         ((v13_lattices @ X0)
% 14.22/14.37          | ~ (l1_lattices @ X0)
% 14.22/14.37          | ((k2_lattices @ X0 @ 
% 14.22/14.37              (sk_C_2 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 14.22/14.37              (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 14.22/14.37              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 14.22/14.37              (sk_C_2 @ 
% 14.22/14.37               (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)) @ X0))
% 14.22/14.37              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0))))),
% 14.22/14.37      inference('simplify', [status(thm)], ['63'])).
% 14.22/14.37  thf('65', plain,
% 14.22/14.37      (![X0 : $i]:
% 14.22/14.37         (((k2_lattices @ X0 @ 
% 14.22/14.37            (sk_C_2 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 14.22/14.37            (k15_lattice3 @ X0 @ k1_xboole_0))
% 14.22/14.37            != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 14.22/14.37              (sk_C_2 @ 
% 14.22/14.37               (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)) @ X0))
% 14.22/14.37              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | ~ (l1_lattices @ X0)
% 14.22/14.37          | (v13_lattices @ X0))),
% 14.22/14.37      inference('sup-', [status(thm)], ['44', '64'])).
% 14.22/14.37  thf('66', plain,
% 14.22/14.37      (![X0 : $i]:
% 14.22/14.37         ((v13_lattices @ X0)
% 14.22/14.37          | ~ (l1_lattices @ X0)
% 14.22/14.37          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 14.22/14.37              (sk_C_2 @ 
% 14.22/14.37               (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)) @ X0))
% 14.22/14.37              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 14.22/14.37          | ~ (l3_lattices @ X0)
% 14.22/14.37          | ~ (v4_lattice3 @ X0)
% 14.22/14.37          | ~ (v10_lattices @ X0)
% 14.22/14.37          | (v2_struct_0 @ X0)
% 14.22/14.37          | ((k2_lattices @ X0 @ 
% 14.22/14.37              (sk_C_2 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 14.22/14.38              (k15_lattice3 @ X0 @ k1_xboole_0))
% 14.22/14.38              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0))))),
% 14.22/14.38      inference('simplify', [status(thm)], ['65'])).
% 14.22/14.38  thf('67', plain,
% 14.22/14.38      (![X0 : $i]:
% 14.22/14.38         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 14.22/14.38            != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 14.22/14.38          | (v2_struct_0 @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | (v13_lattices @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (v6_lattices @ X0)
% 14.22/14.38          | ~ (v8_lattices @ X0)
% 14.22/14.38          | ~ (v9_lattices @ X0)
% 14.22/14.38          | ((k2_lattices @ X0 @ 
% 14.22/14.38              (sk_C_2 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 14.22/14.38              (k15_lattice3 @ X0 @ k1_xboole_0))
% 14.22/14.38              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 14.22/14.38          | (v2_struct_0 @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | (v13_lattices @ X0))),
% 14.22/14.38      inference('sup-', [status(thm)], ['43', '66'])).
% 14.22/14.38  thf('68', plain,
% 14.22/14.38      (![X0 : $i]:
% 14.22/14.38         (((k2_lattices @ X0 @ 
% 14.22/14.38            (sk_C_2 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 14.22/14.38            (k15_lattice3 @ X0 @ k1_xboole_0))
% 14.22/14.38            != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 14.22/14.38          | ~ (v9_lattices @ X0)
% 14.22/14.38          | ~ (v8_lattices @ X0)
% 14.22/14.38          | ~ (v6_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | (v13_lattices @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0)
% 14.22/14.38          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 14.22/14.38              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0))))),
% 14.22/14.38      inference('simplify', [status(thm)], ['67'])).
% 14.22/14.38  thf('69', plain,
% 14.22/14.38      (![X0 : $i]:
% 14.22/14.38         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 14.22/14.38            != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 14.22/14.38          | (v2_struct_0 @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | (v13_lattices @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (v6_lattices @ X0)
% 14.22/14.38          | ~ (v8_lattices @ X0)
% 14.22/14.38          | ~ (v9_lattices @ X0)
% 14.22/14.38          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 14.22/14.38              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 14.22/14.38          | (v2_struct_0 @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | (v13_lattices @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (v6_lattices @ X0)
% 14.22/14.38          | ~ (v8_lattices @ X0)
% 14.22/14.38          | ~ (v9_lattices @ X0))),
% 14.22/14.38      inference('sup-', [status(thm)], ['39', '68'])).
% 14.22/14.38  thf('70', plain,
% 14.22/14.38      (![X0 : $i]:
% 14.22/14.38         (~ (v9_lattices @ X0)
% 14.22/14.38          | ~ (v8_lattices @ X0)
% 14.22/14.38          | ~ (v6_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | (v13_lattices @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0)
% 14.22/14.38          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 14.22/14.38              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0))))),
% 14.22/14.38      inference('simplify', [status(thm)], ['69'])).
% 14.22/14.38  thf('71', plain,
% 14.22/14.38      (![X0 : $i]:
% 14.22/14.38         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 14.22/14.38            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 14.22/14.38          | (v2_struct_0 @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | (v13_lattices @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (v6_lattices @ X0)
% 14.22/14.38          | ~ (v8_lattices @ X0)
% 14.22/14.38          | ~ (v9_lattices @ X0))),
% 14.22/14.38      inference('sup-', [status(thm)], ['0', '70'])).
% 14.22/14.38  thf('72', plain,
% 14.22/14.38      (![X0 : $i]:
% 14.22/14.38         (~ (v9_lattices @ X0)
% 14.22/14.38          | ~ (v8_lattices @ X0)
% 14.22/14.38          | ~ (v6_lattices @ X0)
% 14.22/14.38          | (v13_lattices @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0))),
% 14.22/14.38      inference('simplify', [status(thm)], ['71'])).
% 14.22/14.38  thf(t50_lattice3, conjecture,
% 14.22/14.38    (![A:$i]:
% 14.22/14.38     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 14.22/14.38         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 14.22/14.38       ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 14.22/14.38         ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 14.22/14.38         ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ))).
% 14.22/14.38  thf(zf_stmt_0, negated_conjecture,
% 14.22/14.38    (~( ![A:$i]:
% 14.22/14.38        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 14.22/14.38            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 14.22/14.38          ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 14.22/14.38            ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 14.22/14.38            ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ) )),
% 14.22/14.38    inference('cnf.neg', [status(esa)], [t50_lattice3])).
% 14.22/14.38  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('74', plain,
% 14.22/14.38      ((~ (v10_lattices @ sk_A)
% 14.22/14.38        | ~ (v4_lattice3 @ sk_A)
% 14.22/14.38        | ~ (l3_lattices @ sk_A)
% 14.22/14.38        | ~ (l1_lattices @ sk_A)
% 14.22/14.38        | (v13_lattices @ sk_A)
% 14.22/14.38        | ~ (v6_lattices @ sk_A)
% 14.22/14.38        | ~ (v8_lattices @ sk_A)
% 14.22/14.38        | ~ (v9_lattices @ sk_A))),
% 14.22/14.38      inference('sup-', [status(thm)], ['72', '73'])).
% 14.22/14.38  thf('75', plain, ((v10_lattices @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('76', plain, ((v4_lattice3 @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('77', plain, ((l3_lattices @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('78', plain, ((l3_lattices @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf(dt_l3_lattices, axiom,
% 14.22/14.38    (![A:$i]:
% 14.22/14.38     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 14.22/14.38  thf('79', plain,
% 14.22/14.38      (![X15 : $i]: ((l1_lattices @ X15) | ~ (l3_lattices @ X15))),
% 14.22/14.38      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 14.22/14.38  thf('80', plain, ((l1_lattices @ sk_A)),
% 14.22/14.38      inference('sup-', [status(thm)], ['78', '79'])).
% 14.22/14.38  thf(cc1_lattices, axiom,
% 14.22/14.38    (![A:$i]:
% 14.22/14.38     ( ( l3_lattices @ A ) =>
% 14.22/14.38       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 14.22/14.38         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 14.22/14.38           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 14.22/14.38           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 14.22/14.38  thf('81', plain,
% 14.22/14.38      (![X10 : $i]:
% 14.22/14.38         ((v2_struct_0 @ X10)
% 14.22/14.38          | ~ (v10_lattices @ X10)
% 14.22/14.38          | (v6_lattices @ X10)
% 14.22/14.38          | ~ (l3_lattices @ X10))),
% 14.22/14.38      inference('cnf', [status(esa)], [cc1_lattices])).
% 14.22/14.38  thf('82', plain, (~ (v2_struct_0 @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('83', plain,
% 14.22/14.38      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 14.22/14.38      inference('sup-', [status(thm)], ['81', '82'])).
% 14.22/14.38  thf('84', plain, ((l3_lattices @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('85', plain, ((v10_lattices @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('86', plain, ((v6_lattices @ sk_A)),
% 14.22/14.38      inference('demod', [status(thm)], ['83', '84', '85'])).
% 14.22/14.38  thf('87', plain,
% 14.22/14.38      (![X10 : $i]:
% 14.22/14.38         ((v2_struct_0 @ X10)
% 14.22/14.38          | ~ (v10_lattices @ X10)
% 14.22/14.38          | (v8_lattices @ X10)
% 14.22/14.38          | ~ (l3_lattices @ X10))),
% 14.22/14.38      inference('cnf', [status(esa)], [cc1_lattices])).
% 14.22/14.38  thf('88', plain, (~ (v2_struct_0 @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('89', plain,
% 14.22/14.38      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 14.22/14.38      inference('sup-', [status(thm)], ['87', '88'])).
% 14.22/14.38  thf('90', plain, ((l3_lattices @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('91', plain, ((v10_lattices @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('92', plain, ((v8_lattices @ sk_A)),
% 14.22/14.38      inference('demod', [status(thm)], ['89', '90', '91'])).
% 14.22/14.38  thf('93', plain,
% 14.22/14.38      (![X10 : $i]:
% 14.22/14.38         ((v2_struct_0 @ X10)
% 14.22/14.38          | ~ (v10_lattices @ X10)
% 14.22/14.38          | (v9_lattices @ X10)
% 14.22/14.38          | ~ (l3_lattices @ X10))),
% 14.22/14.38      inference('cnf', [status(esa)], [cc1_lattices])).
% 14.22/14.38  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('95', plain,
% 14.22/14.38      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 14.22/14.38      inference('sup-', [status(thm)], ['93', '94'])).
% 14.22/14.38  thf('96', plain, ((l3_lattices @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('97', plain, ((v10_lattices @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('98', plain, ((v9_lattices @ sk_A)),
% 14.22/14.38      inference('demod', [status(thm)], ['95', '96', '97'])).
% 14.22/14.38  thf('99', plain, ((v13_lattices @ sk_A)),
% 14.22/14.38      inference('demod', [status(thm)],
% 14.22/14.38                ['74', '75', '76', '77', '80', '86', '92', '98'])).
% 14.22/14.38  thf('100', plain,
% 14.22/14.38      (![X28 : $i, X29 : $i]:
% 14.22/14.38         (~ (l3_lattices @ X28)
% 14.22/14.38          | (v2_struct_0 @ X28)
% 14.22/14.38          | (m1_subset_1 @ (k15_lattice3 @ X28 @ X29) @ (u1_struct_0 @ X28)))),
% 14.22/14.38      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 14.22/14.38  thf(dt_k5_lattices, axiom,
% 14.22/14.38    (![A:$i]:
% 14.22/14.38     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 14.22/14.38       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 14.22/14.38  thf('101', plain,
% 14.22/14.38      (![X14 : $i]:
% 14.22/14.38         ((m1_subset_1 @ (k5_lattices @ X14) @ (u1_struct_0 @ X14))
% 14.22/14.38          | ~ (l1_lattices @ X14)
% 14.22/14.38          | (v2_struct_0 @ X14))),
% 14.22/14.38      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 14.22/14.38  thf(d16_lattices, axiom,
% 14.22/14.38    (![A:$i]:
% 14.22/14.38     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 14.22/14.38       ( ( v13_lattices @ A ) =>
% 14.22/14.38         ( ![B:$i]:
% 14.22/14.38           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 14.22/14.38             ( ( ( B ) = ( k5_lattices @ A ) ) <=>
% 14.22/14.38               ( ![C:$i]:
% 14.22/14.38                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 14.22/14.38                   ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 14.22/14.38                     ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 14.22/14.38  thf('102', plain,
% 14.22/14.38      (![X11 : $i, X12 : $i, X13 : $i]:
% 14.22/14.38         (~ (v13_lattices @ X11)
% 14.22/14.38          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 14.22/14.38          | ((X12) != (k5_lattices @ X11))
% 14.22/14.38          | ((k2_lattices @ X11 @ X13 @ X12) = (X12))
% 14.22/14.38          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 14.22/14.38          | ~ (l1_lattices @ X11)
% 14.22/14.38          | (v2_struct_0 @ X11))),
% 14.22/14.38      inference('cnf', [status(esa)], [d16_lattices])).
% 14.22/14.38  thf('103', plain,
% 14.22/14.38      (![X11 : $i, X13 : $i]:
% 14.22/14.38         ((v2_struct_0 @ X11)
% 14.22/14.38          | ~ (l1_lattices @ X11)
% 14.22/14.38          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 14.22/14.38          | ((k2_lattices @ X11 @ X13 @ (k5_lattices @ X11))
% 14.22/14.38              = (k5_lattices @ X11))
% 14.22/14.38          | ~ (m1_subset_1 @ (k5_lattices @ X11) @ (u1_struct_0 @ X11))
% 14.22/14.38          | ~ (v13_lattices @ X11))),
% 14.22/14.38      inference('simplify', [status(thm)], ['102'])).
% 14.22/14.38  thf('104', plain,
% 14.22/14.38      (![X0 : $i, X1 : $i]:
% 14.22/14.38         ((v2_struct_0 @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | ~ (v13_lattices @ X0)
% 14.22/14.38          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 14.22/14.38          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0))),
% 14.22/14.38      inference('sup-', [status(thm)], ['101', '103'])).
% 14.22/14.38  thf('105', plain,
% 14.22/14.38      (![X0 : $i, X1 : $i]:
% 14.22/14.38         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 14.22/14.38          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 14.22/14.38          | ~ (v13_lattices @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0))),
% 14.22/14.38      inference('simplify', [status(thm)], ['104'])).
% 14.22/14.38  thf('106', plain,
% 14.22/14.38      (![X0 : $i, X1 : $i]:
% 14.22/14.38         ((v2_struct_0 @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | ~ (v13_lattices @ X0)
% 14.22/14.38          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 14.22/14.38              = (k5_lattices @ X0)))),
% 14.22/14.38      inference('sup-', [status(thm)], ['100', '105'])).
% 14.22/14.38  thf('107', plain,
% 14.22/14.38      (![X0 : $i, X1 : $i]:
% 14.22/14.38         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 14.22/14.38            = (k5_lattices @ X0))
% 14.22/14.38          | ~ (v13_lattices @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0))),
% 14.22/14.38      inference('simplify', [status(thm)], ['106'])).
% 14.22/14.38  thf('108', plain,
% 14.22/14.38      (![X14 : $i]:
% 14.22/14.38         ((m1_subset_1 @ (k5_lattices @ X14) @ (u1_struct_0 @ X14))
% 14.22/14.38          | ~ (l1_lattices @ X14)
% 14.22/14.38          | (v2_struct_0 @ X14))),
% 14.22/14.38      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 14.22/14.38  thf('109', plain,
% 14.22/14.38      (![X14 : $i]:
% 14.22/14.38         ((m1_subset_1 @ (k5_lattices @ X14) @ (u1_struct_0 @ X14))
% 14.22/14.38          | ~ (l1_lattices @ X14)
% 14.22/14.38          | (v2_struct_0 @ X14))),
% 14.22/14.38      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 14.22/14.38  thf('110', plain,
% 14.22/14.38      (![X35 : $i, X36 : $i]:
% 14.22/14.38         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X36))
% 14.22/14.38          | ((k15_lattice3 @ X36 @ (k6_domain_1 @ (u1_struct_0 @ X36) @ X35))
% 14.22/14.38              = (X35))
% 14.22/14.38          | ~ (l3_lattices @ X36)
% 14.22/14.38          | ~ (v4_lattice3 @ X36)
% 14.22/14.38          | ~ (v10_lattices @ X36)
% 14.22/14.38          | (v2_struct_0 @ X36))),
% 14.22/14.38      inference('cnf', [status(esa)], [t43_lattice3])).
% 14.22/14.38  thf('111', plain,
% 14.22/14.38      (![X0 : $i]:
% 14.22/14.38         ((v2_struct_0 @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | ((k15_lattice3 @ X0 @ 
% 14.22/14.38              (k6_domain_1 @ (u1_struct_0 @ X0) @ (k5_lattices @ X0)))
% 14.22/14.38              = (k5_lattices @ X0)))),
% 14.22/14.38      inference('sup-', [status(thm)], ['109', '110'])).
% 14.22/14.38  thf('112', plain,
% 14.22/14.38      (![X0 : $i]:
% 14.22/14.38         (((k15_lattice3 @ X0 @ 
% 14.22/14.38            (k6_domain_1 @ (u1_struct_0 @ X0) @ (k5_lattices @ X0)))
% 14.22/14.38            = (k5_lattices @ X0))
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0))),
% 14.22/14.38      inference('simplify', [status(thm)], ['111'])).
% 14.22/14.38  thf('113', plain,
% 14.22/14.38      (![X0 : $i, X1 : $i]:
% 14.22/14.38         ((v2_struct_0 @ X1)
% 14.22/14.38          | ~ (v10_lattices @ X1)
% 14.22/14.38          | ~ (v4_lattice3 @ X1)
% 14.22/14.38          | ~ (l3_lattices @ X1)
% 14.22/14.38          | (r3_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 14.22/14.38             (k15_lattice3 @ X1 @ X0)))),
% 14.22/14.38      inference('sup-', [status(thm)], ['9', '10'])).
% 14.22/14.38  thf('114', plain,
% 14.22/14.38      (![X0 : $i]:
% 14.22/14.38         ((r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 14.22/14.38           (k5_lattices @ X0))
% 14.22/14.38          | (v2_struct_0 @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0))),
% 14.22/14.38      inference('sup+', [status(thm)], ['112', '113'])).
% 14.22/14.38  thf('115', plain,
% 14.22/14.38      (![X0 : $i]:
% 14.22/14.38         (~ (l3_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0)
% 14.22/14.38          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 14.22/14.38             (k5_lattices @ X0)))),
% 14.22/14.38      inference('simplify', [status(thm)], ['114'])).
% 14.22/14.38  thf('116', plain,
% 14.22/14.38      (![X14 : $i]:
% 14.22/14.38         ((m1_subset_1 @ (k5_lattices @ X14) @ (u1_struct_0 @ X14))
% 14.22/14.38          | ~ (l1_lattices @ X14)
% 14.22/14.38          | (v2_struct_0 @ X14))),
% 14.22/14.38      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 14.22/14.38  thf('117', plain,
% 14.22/14.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.38         (~ (v9_lattices @ X0)
% 14.22/14.38          | ~ (v8_lattices @ X0)
% 14.22/14.38          | ~ (v6_lattices @ X0)
% 14.22/14.38          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 14.22/14.38          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 14.22/14.38          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0))),
% 14.22/14.38      inference('simplify', [status(thm)], ['15'])).
% 14.22/14.38  thf('118', plain,
% 14.22/14.38      (![X0 : $i, X1 : $i]:
% 14.22/14.38         ((v2_struct_0 @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 14.22/14.38          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 14.22/14.38          | ~ (v6_lattices @ X0)
% 14.22/14.38          | ~ (v8_lattices @ X0)
% 14.22/14.38          | ~ (v9_lattices @ X0))),
% 14.22/14.38      inference('sup-', [status(thm)], ['116', '117'])).
% 14.22/14.38  thf('119', plain,
% 14.22/14.38      (![X0 : $i, X1 : $i]:
% 14.22/14.38         (~ (v9_lattices @ X0)
% 14.22/14.38          | ~ (v8_lattices @ X0)
% 14.22/14.38          | ~ (v6_lattices @ X0)
% 14.22/14.38          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 14.22/14.38          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0))),
% 14.22/14.38      inference('simplify', [status(thm)], ['118'])).
% 14.22/14.38  thf('120', plain,
% 14.22/14.38      (![X0 : $i]:
% 14.22/14.38         ((v2_struct_0 @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 14.22/14.38             (k5_lattices @ X0))
% 14.22/14.38          | ~ (v6_lattices @ X0)
% 14.22/14.38          | ~ (v8_lattices @ X0)
% 14.22/14.38          | ~ (v9_lattices @ X0))),
% 14.22/14.38      inference('sup-', [status(thm)], ['115', '119'])).
% 14.22/14.38  thf('121', plain,
% 14.22/14.38      (![X0 : $i]:
% 14.22/14.38         (~ (v9_lattices @ X0)
% 14.22/14.38          | ~ (v8_lattices @ X0)
% 14.22/14.38          | ~ (v6_lattices @ X0)
% 14.22/14.38          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 14.22/14.38             (k5_lattices @ X0))
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0))),
% 14.22/14.38      inference('simplify', [status(thm)], ['120'])).
% 14.22/14.38  thf('122', plain,
% 14.22/14.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.22/14.38         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 14.22/14.38          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 14.22/14.38              = (k15_lattice3 @ X0 @ X1))
% 14.22/14.38          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 14.22/14.38          | ~ (v9_lattices @ X0)
% 14.22/14.38          | ~ (v8_lattices @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0))),
% 14.22/14.38      inference('simplify', [status(thm)], ['23'])).
% 14.22/14.38  thf('123', plain,
% 14.22/14.38      (![X0 : $i]:
% 14.22/14.38         ((v2_struct_0 @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | ~ (v6_lattices @ X0)
% 14.22/14.38          | ~ (v8_lattices @ X0)
% 14.22/14.38          | ~ (v9_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | ~ (v8_lattices @ X0)
% 14.22/14.38          | ~ (v9_lattices @ X0)
% 14.22/14.38          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 14.22/14.38          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 14.22/14.38              (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 14.22/14.38      inference('sup-', [status(thm)], ['121', '122'])).
% 14.22/14.38  thf('124', plain,
% 14.22/14.38      (![X0 : $i]:
% 14.22/14.38         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 14.22/14.38            (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 14.22/14.38          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 14.22/14.38          | ~ (v9_lattices @ X0)
% 14.22/14.38          | ~ (v8_lattices @ X0)
% 14.22/14.38          | ~ (v6_lattices @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0))),
% 14.22/14.38      inference('simplify', [status(thm)], ['123'])).
% 14.22/14.38  thf('125', plain,
% 14.22/14.38      (![X0 : $i]:
% 14.22/14.38         ((v2_struct_0 @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | ~ (v6_lattices @ X0)
% 14.22/14.38          | ~ (v8_lattices @ X0)
% 14.22/14.38          | ~ (v9_lattices @ X0)
% 14.22/14.38          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 14.22/14.38              (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 14.22/14.38      inference('sup-', [status(thm)], ['108', '124'])).
% 14.22/14.38  thf('126', plain,
% 14.22/14.38      (![X0 : $i]:
% 14.22/14.38         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 14.22/14.38            (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 14.22/14.38          | ~ (v9_lattices @ X0)
% 14.22/14.38          | ~ (v8_lattices @ X0)
% 14.22/14.38          | ~ (v6_lattices @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0))),
% 14.22/14.38      inference('simplify', [status(thm)], ['125'])).
% 14.22/14.38  thf('127', plain,
% 14.22/14.38      (![X0 : $i]:
% 14.22/14.38         (((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 14.22/14.38          | (v2_struct_0 @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | ~ (v13_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | ~ (v6_lattices @ X0)
% 14.22/14.38          | ~ (v8_lattices @ X0)
% 14.22/14.38          | ~ (v9_lattices @ X0))),
% 14.22/14.38      inference('sup+', [status(thm)], ['107', '126'])).
% 14.22/14.38  thf('128', plain,
% 14.22/14.38      (![X0 : $i]:
% 14.22/14.38         (~ (v9_lattices @ X0)
% 14.22/14.38          | ~ (v8_lattices @ X0)
% 14.22/14.38          | ~ (v6_lattices @ X0)
% 14.22/14.38          | ~ (v4_lattice3 @ X0)
% 14.22/14.38          | ~ (v10_lattices @ X0)
% 14.22/14.38          | ~ (v13_lattices @ X0)
% 14.22/14.38          | ~ (l1_lattices @ X0)
% 14.22/14.38          | ~ (l3_lattices @ X0)
% 14.22/14.38          | (v2_struct_0 @ X0)
% 14.22/14.38          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 14.22/14.38      inference('simplify', [status(thm)], ['127'])).
% 14.22/14.38  thf('129', plain,
% 14.22/14.38      (((v2_struct_0 @ sk_A)
% 14.22/14.38        | ~ (v10_lattices @ sk_A)
% 14.22/14.38        | ~ (v13_lattices @ sk_A)
% 14.22/14.38        | ~ (l3_lattices @ sk_A)
% 14.22/14.38        | ((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('130', plain,
% 14.22/14.38      ((((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))
% 14.22/14.38         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 14.22/14.38      inference('split', [status(esa)], ['129'])).
% 14.22/14.38  thf('131', plain,
% 14.22/14.38      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 14.22/14.38         | (v2_struct_0 @ sk_A)
% 14.22/14.38         | ~ (l3_lattices @ sk_A)
% 14.22/14.38         | ~ (l1_lattices @ sk_A)
% 14.22/14.38         | ~ (v13_lattices @ sk_A)
% 14.22/14.38         | ~ (v10_lattices @ sk_A)
% 14.22/14.38         | ~ (v4_lattice3 @ sk_A)
% 14.22/14.38         | ~ (v6_lattices @ sk_A)
% 14.22/14.38         | ~ (v8_lattices @ sk_A)
% 14.22/14.38         | ~ (v9_lattices @ sk_A)))
% 14.22/14.38         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 14.22/14.38      inference('sup-', [status(thm)], ['128', '130'])).
% 14.22/14.38  thf('132', plain, ((l3_lattices @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('133', plain, ((l1_lattices @ sk_A)),
% 14.22/14.38      inference('sup-', [status(thm)], ['78', '79'])).
% 14.22/14.38  thf('134', plain, ((v10_lattices @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('135', plain, ((v4_lattice3 @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('136', plain, ((v6_lattices @ sk_A)),
% 14.22/14.38      inference('demod', [status(thm)], ['83', '84', '85'])).
% 14.22/14.38  thf('137', plain, ((v8_lattices @ sk_A)),
% 14.22/14.38      inference('demod', [status(thm)], ['89', '90', '91'])).
% 14.22/14.38  thf('138', plain, ((v9_lattices @ sk_A)),
% 14.22/14.38      inference('demod', [status(thm)], ['95', '96', '97'])).
% 14.22/14.38  thf('139', plain,
% 14.22/14.38      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 14.22/14.38         | (v2_struct_0 @ sk_A)
% 14.22/14.38         | ~ (v13_lattices @ sk_A)))
% 14.22/14.38         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 14.22/14.38      inference('demod', [status(thm)],
% 14.22/14.38                ['131', '132', '133', '134', '135', '136', '137', '138'])).
% 14.22/14.38  thf('140', plain,
% 14.22/14.38      (((~ (v13_lattices @ sk_A) | (v2_struct_0 @ sk_A)))
% 14.22/14.38         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 14.22/14.38      inference('simplify', [status(thm)], ['139'])).
% 14.22/14.38  thf('141', plain, (~ (v2_struct_0 @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('142', plain,
% 14.22/14.38      ((~ (v13_lattices @ sk_A))
% 14.22/14.38         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 14.22/14.38      inference('clc', [status(thm)], ['140', '141'])).
% 14.22/14.38  thf('143', plain,
% 14.22/14.38      (($false)
% 14.22/14.38         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 14.22/14.38      inference('sup-', [status(thm)], ['99', '142'])).
% 14.22/14.38  thf('144', plain, (((v2_struct_0 @ sk_A)) <= (((v2_struct_0 @ sk_A)))),
% 14.22/14.38      inference('split', [status(esa)], ['129'])).
% 14.22/14.38  thf('145', plain, (~ (v2_struct_0 @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('146', plain, (~ ((v2_struct_0 @ sk_A))),
% 14.22/14.38      inference('sup-', [status(thm)], ['144', '145'])).
% 14.22/14.38  thf('147', plain, ((l3_lattices @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('148', plain, ((~ (l3_lattices @ sk_A)) <= (~ ((l3_lattices @ sk_A)))),
% 14.22/14.38      inference('split', [status(esa)], ['129'])).
% 14.22/14.38  thf('149', plain, (((l3_lattices @ sk_A))),
% 14.22/14.38      inference('sup-', [status(thm)], ['147', '148'])).
% 14.22/14.38  thf('150', plain, ((v10_lattices @ sk_A)),
% 14.22/14.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.22/14.38  thf('151', plain, ((~ (v10_lattices @ sk_A)) <= (~ ((v10_lattices @ sk_A)))),
% 14.22/14.38      inference('split', [status(esa)], ['129'])).
% 14.22/14.38  thf('152', plain, (((v10_lattices @ sk_A))),
% 14.22/14.38      inference('sup-', [status(thm)], ['150', '151'])).
% 14.22/14.38  thf('153', plain, ((v13_lattices @ sk_A)),
% 14.22/14.38      inference('demod', [status(thm)],
% 14.22/14.38                ['74', '75', '76', '77', '80', '86', '92', '98'])).
% 14.22/14.38  thf('154', plain, ((~ (v13_lattices @ sk_A)) <= (~ ((v13_lattices @ sk_A)))),
% 14.22/14.38      inference('split', [status(esa)], ['129'])).
% 14.22/14.38  thf('155', plain, (((v13_lattices @ sk_A))),
% 14.22/14.38      inference('sup-', [status(thm)], ['153', '154'])).
% 14.22/14.38  thf('156', plain,
% 14.22/14.38      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))) | 
% 14.22/14.38       ~ ((v13_lattices @ sk_A)) | ~ ((v10_lattices @ sk_A)) | 
% 14.22/14.38       ~ ((l3_lattices @ sk_A)) | ((v2_struct_0 @ sk_A))),
% 14.22/14.38      inference('split', [status(esa)], ['129'])).
% 14.22/14.38  thf('157', plain,
% 14.22/14.38      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 14.22/14.38      inference('sat_resolution*', [status(thm)],
% 14.22/14.38                ['146', '149', '152', '155', '156'])).
% 14.22/14.38  thf('158', plain, ($false),
% 14.22/14.38      inference('simpl_trail', [status(thm)], ['143', '157'])).
% 14.22/14.38  
% 14.22/14.38  % SZS output end Refutation
% 14.22/14.38  
% 14.22/14.38  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
