%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.M1tZdbOyeO

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:38 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :  191 ( 559 expanded)
%              Number of leaves         :   44 ( 176 expanded)
%              Depth                    :   24
%              Number of atoms          : 2596 (9511 expanded)
%              Number of equality atoms :  102 ( 311 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(a_2_4_lattice3_type,type,(
    a_2_4_lattice3: $i > $i > $i )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(a_2_3_lattice3_type,type,(
    a_2_3_lattice3: $i > $i > $i )).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
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

thf('1',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ X14 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( v13_lattices @ X15 )
      | ~ ( l1_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_lattices])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t45_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( B
              = ( k15_lattice3 @ A @ ( a_2_3_lattice3 @ A @ B ) ) )
            & ( B
              = ( k16_lattice3 @ A @ ( a_2_4_lattice3 @ A @ B ) ) ) ) ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( X22
        = ( k15_lattice3 @ X23 @ ( a_2_3_lattice3 @ X23 @ X22 ) ) )
      | ~ ( l3_lattices @ X23 )
      | ~ ( v4_lattice3 @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t45_lattice3])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 )
        = ( k15_lattice3 @ X0 @ ( a_2_3_lattice3 @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 )
        = ( k15_lattice3 @ X0 @ ( a_2_3_lattice3 @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t48_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i,C: $i] :
          ( ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
             => ~ ( ( r2_hidden @ D @ B )
                  & ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) )
                     => ~ ( ( r3_lattices @ A @ D @ E )
                          & ( r2_hidden @ E @ C ) ) ) ) )
         => ( r3_lattices @ A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) ) ) )).

thf('9',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ ( sk_D @ X26 @ X27 @ X25 ) @ X27 )
      | ( r3_lattices @ X25 @ ( k15_lattice3 @ X25 @ X27 ) @ ( k15_lattice3 @ X25 @ X26 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v4_lattice3 @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_lattice3])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattices @ X1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( k15_lattice3 @ X1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D @ X2 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
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

thf('15',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l3_lattices @ X9 )
      | ~ ( v9_lattices @ X9 )
      | ~ ( v8_lattices @ X9 )
      | ~ ( v6_lattices @ X9 )
      | ( v2_struct_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( r1_lattices @ X9 @ X8 @ X10 )
      | ~ ( r3_lattices @ X9 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('16',plain,(
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
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
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
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v6_lattices @ X1 )
      | ~ ( v8_lattices @ X1 )
      | ~ ( v9_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X1 )
      | ~ ( v8_lattices @ X1 )
      | ~ ( v6_lattices @ X1 )
      | ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
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

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r1_lattices @ X12 @ X11 @ X13 )
      | ( ( k2_lattices @ X12 @ X11 @ X13 )
        = X11 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l3_lattices @ X12 )
      | ~ ( v9_lattices @ X12 )
      | ~ ( v8_lattices @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('24',plain,(
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
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
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
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) )
        = ( k15_lattice3 @ X1 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v9_lattices @ X1 )
      | ~ ( v8_lattices @ X1 )
      | ~ ( v6_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['7','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','29'])).

thf('31',plain,(
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
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 )
        = ( k15_lattice3 @ X0 @ ( a_2_3_lattice3 @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('34',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('35',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
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

thf('36',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v6_lattices @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ( ( k2_lattices @ X17 @ X19 @ X18 )
        = ( k2_lattices @ X17 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d6_lattices])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ X2 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) ) )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ X2 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) ) )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
        = ( k2_lattices @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','42'])).

thf('44',plain,(
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
        = ( k2_lattices @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('46',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k2_lattices @ X15 @ ( sk_C_1 @ X14 @ X15 ) @ X14 )
       != X14 )
      | ( ( k2_lattices @ X15 @ X14 @ ( sk_C_1 @ X14 @ X15 ) )
       != X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( v13_lattices @ X15 )
      | ~ ( l1_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_lattices])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( ( k2_lattices @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
       != ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
       != ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
       != ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

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

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( v13_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('57',plain,(
    ! [X7: $i] :
      ( ( l1_lattices @ X7 )
      | ~ ( l3_lattices @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('58',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('61',plain,(
    ! [X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v6_lattices @ X3 )
      | ~ ( l3_lattices @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('62',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v8_lattices @ X3 )
      | ~ ( l3_lattices @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ! [X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v9_lattices @ X3 )
      | ~ ( l3_lattices @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['54','55','58','59','60','66','72','78'])).

thf('80',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X20 @ X21 ) @ ( u1_struct_0 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('81',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v13_lattices @ X15 )
      | ( ( k2_lattices @ X15 @ X16 @ ( sk_B @ X15 ) )
        = ( sk_B @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_lattices])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_B @ X0 ) )
        = ( sk_B @ X0 ) )
      | ~ ( v13_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_B @ X0 ) )
        = ( sk_B @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X15: $i] :
      ( ~ ( v13_lattices @ X15 )
      | ( m1_subset_1 @ ( sk_B @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_lattices])).

thf('85',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( X22
        = ( k15_lattice3 @ X23 @ ( a_2_3_lattice3 @ X23 @ X22 ) ) )
      | ~ ( l3_lattices @ X23 )
      | ~ ( v4_lattice3 @ X23 )
      | ~ ( v10_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t45_lattice3])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( sk_B @ X0 )
        = ( k15_lattice3 @ X0 @ ( a_2_3_lattice3 @ X0 @ ( sk_B @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
        = ( k15_lattice3 @ X0 @ ( a_2_3_lattice3 @ X0 @ ( sk_B @ X0 ) ) ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_B @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_B @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['83','90'])).

thf('92',plain,(
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
      | ( ( sk_B @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['93'])).

thf('95',plain,
    ( ( ( ( k5_lattices @ sk_A )
       != ( sk_B @ sk_A ) )
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
    inference('sup-',[status(thm)],['92','94'])).

thf('96',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('98',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('101',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('102',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('103',plain,
    ( ( ( ( k5_lattices @ sk_A )
       != ( sk_B @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v13_lattices @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['95','96','97','98','99','100','101','102'])).

thf('104',plain,(
    ! [X15: $i] :
      ( ~ ( v13_lattices @ X15 )
      | ( m1_subset_1 @ ( sk_B @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_lattices])).

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

thf('105',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v13_lattices @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( m1_subset_1 @ ( sk_C @ X5 @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ( X5
        = ( k5_lattices @ X4 ) )
      | ~ ( l1_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d16_lattices])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( sk_B @ X0 )
        = ( k5_lattices @ X0 ) )
      | ( m1_subset_1 @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v13_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_B @ X0 )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v13_lattices @ X15 )
      | ( ( k2_lattices @ X15 @ ( sk_B @ X15 ) @ X16 )
        = ( sk_B @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_lattices])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( sk_B @ X0 )
        = ( k5_lattices @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( sk_B @ X0 ) @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) )
        = ( sk_B @ X0 ) )
      | ~ ( v13_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( sk_B @ X0 ) @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) )
        = ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_B @ X0 )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('112',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v13_lattices @ X15 )
      | ( ( k2_lattices @ X15 @ X16 @ ( sk_B @ X15 ) )
        = ( sk_B @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_lattices])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( sk_B @ X0 )
        = ( k5_lattices @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) @ ( sk_B @ X0 ) )
        = ( sk_B @ X0 ) )
      | ~ ( v13_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) @ ( sk_B @ X0 ) )
        = ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X15: $i] :
      ( ~ ( v13_lattices @ X15 )
      | ( m1_subset_1 @ ( sk_B @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( l1_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_lattices])).

thf('116',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v13_lattices @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( ( k2_lattices @ X4 @ ( sk_C @ X5 @ X4 ) @ X5 )
       != X5 )
      | ( ( k2_lattices @ X4 @ X5 @ ( sk_C @ X5 @ X4 ) )
       != X5 )
      | ( X5
        = ( k5_lattices @ X4 ) )
      | ~ ( l1_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d16_lattices])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( sk_B @ X0 )
        = ( k5_lattices @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( sk_B @ X0 ) @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) )
       != ( sk_B @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) @ ( sk_B @ X0 ) )
       != ( sk_B @ X0 ) )
      | ~ ( v13_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) @ ( sk_B @ X0 ) )
       != ( sk_B @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( sk_B @ X0 ) @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) )
       != ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != ( sk_B @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( sk_B @ X0 )
        = ( k5_lattices @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( sk_B @ X0 )
        = ( k5_lattices @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( sk_B @ X0 ) @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) )
       != ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['114','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( sk_B @ X0 ) @ ( sk_C @ ( sk_B @ X0 ) @ X0 ) )
       != ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
       != ( sk_B @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( sk_B @ X0 )
        = ( k5_lattices @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( sk_B @ X0 )
        = ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['110','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( sk_B @ X0 )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,
    ( ~ ( l1_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ( ( sk_B @ sk_A )
      = ( k5_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('126',plain,
    ( ~ ( v13_lattices @ sk_A )
    | ( ( sk_B @ sk_A )
      = ( k5_lattices @ sk_A ) ) ),
    inference(demod,[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ~ ( v13_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['103','126'])).

thf('128',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,
    ( $false
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','129'])).

thf('131',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['93'])).

thf('132',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ~ ( l3_lattices @ sk_A )
   <= ~ ( l3_lattices @ sk_A ) ),
    inference(split,[status(esa)],['93'])).

thf('136',plain,(
    l3_lattices @ sk_A ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ~ ( v10_lattices @ sk_A )
   <= ~ ( v10_lattices @ sk_A ) ),
    inference(split,[status(esa)],['93'])).

thf('139',plain,(
    v10_lattices @ sk_A ),
    inference('sup-',[status(thm)],['137','138'])).

thf('140',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['54','55','58','59','60','66','72','78'])).

thf('141',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ~ ( v13_lattices @ sk_A ) ),
    inference(split,[status(esa)],['93'])).

thf('142',plain,(
    v13_lattices @ sk_A ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['93'])).

thf('144',plain,(
    ( k5_lattices @ sk_A )
 != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ),
    inference('sat_resolution*',[status(thm)],['133','136','139','142','143'])).

thf('145',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['130','144'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.M1tZdbOyeO
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:55:50 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.20/0.33  % Running in FO mode
% 2.14/2.34  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.14/2.34  % Solved by: fo/fo7.sh
% 2.14/2.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.14/2.34  % done 1275 iterations in 1.908s
% 2.14/2.34  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.14/2.34  % SZS output start Refutation
% 2.14/2.34  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.14/2.34  thf(sk_B_type, type, sk_B: $i > $i).
% 2.14/2.34  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 2.14/2.34  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.14/2.34  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 2.14/2.34  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 2.14/2.34  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 2.14/2.34  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.14/2.34  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 2.14/2.34  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 2.14/2.34  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 2.14/2.34  thf(sk_A_type, type, sk_A: $i).
% 2.14/2.34  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.14/2.34  thf(a_2_4_lattice3_type, type, a_2_4_lattice3: $i > $i > $i).
% 2.14/2.34  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 2.14/2.34  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.14/2.34  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 2.14/2.34  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 2.14/2.34  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 2.14/2.34  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 2.14/2.34  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.14/2.34  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.14/2.34  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 2.14/2.34  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 2.14/2.34  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.14/2.34  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 2.14/2.34  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.14/2.34  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 2.14/2.34  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 2.14/2.34  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 2.14/2.34  thf(a_2_3_lattice3_type, type, a_2_3_lattice3: $i > $i > $i).
% 2.14/2.34  thf(dt_k15_lattice3, axiom,
% 2.14/2.34    (![A:$i,B:$i]:
% 2.14/2.34     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 2.14/2.34       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 2.14/2.34  thf('0', plain,
% 2.14/2.34      (![X20 : $i, X21 : $i]:
% 2.14/2.34         (~ (l3_lattices @ X20)
% 2.14/2.34          | (v2_struct_0 @ X20)
% 2.14/2.34          | (m1_subset_1 @ (k15_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 2.14/2.34      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.14/2.34  thf(d13_lattices, axiom,
% 2.14/2.34    (![A:$i]:
% 2.14/2.34     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 2.14/2.34       ( ( v13_lattices @ A ) <=>
% 2.14/2.34         ( ?[B:$i]:
% 2.14/2.34           ( ( ![C:$i]:
% 2.14/2.34               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.14/2.34                 ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 2.14/2.34                   ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) & 
% 2.14/2.34             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 2.14/2.34  thf('1', plain,
% 2.14/2.34      (![X14 : $i, X15 : $i]:
% 2.14/2.34         ((m1_subset_1 @ (sk_C_1 @ X14 @ X15) @ (u1_struct_0 @ X15))
% 2.14/2.34          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 2.14/2.34          | (v13_lattices @ X15)
% 2.14/2.34          | ~ (l1_lattices @ X15)
% 2.14/2.34          | (v2_struct_0 @ X15))),
% 2.14/2.34      inference('cnf', [status(esa)], [d13_lattices])).
% 2.14/2.34  thf('2', plain,
% 2.14/2.34      (![X0 : $i, X1 : $i]:
% 2.14/2.34         ((v2_struct_0 @ X0)
% 2.14/2.34          | ~ (l3_lattices @ X0)
% 2.14/2.34          | (v2_struct_0 @ X0)
% 2.14/2.34          | ~ (l1_lattices @ X0)
% 2.14/2.34          | (v13_lattices @ X0)
% 2.14/2.34          | (m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.14/2.34             (u1_struct_0 @ X0)))),
% 2.14/2.34      inference('sup-', [status(thm)], ['0', '1'])).
% 2.14/2.34  thf('3', plain,
% 2.14/2.34      (![X0 : $i, X1 : $i]:
% 2.14/2.34         ((m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.14/2.34           (u1_struct_0 @ X0))
% 2.14/2.34          | (v13_lattices @ X0)
% 2.14/2.34          | ~ (l1_lattices @ X0)
% 2.14/2.34          | ~ (l3_lattices @ X0)
% 2.14/2.34          | (v2_struct_0 @ X0))),
% 2.14/2.34      inference('simplify', [status(thm)], ['2'])).
% 2.14/2.34  thf(t45_lattice3, axiom,
% 2.14/2.34    (![A:$i]:
% 2.14/2.34     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.14/2.34         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.14/2.34       ( ![B:$i]:
% 2.14/2.34         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.14/2.34           ( ( ( B ) = ( k15_lattice3 @ A @ ( a_2_3_lattice3 @ A @ B ) ) ) & 
% 2.14/2.34             ( ( B ) = ( k16_lattice3 @ A @ ( a_2_4_lattice3 @ A @ B ) ) ) ) ) ) ))).
% 2.14/2.34  thf('4', plain,
% 2.14/2.34      (![X22 : $i, X23 : $i]:
% 2.14/2.34         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 2.14/2.34          | ((X22) = (k15_lattice3 @ X23 @ (a_2_3_lattice3 @ X23 @ X22)))
% 2.14/2.34          | ~ (l3_lattices @ X23)
% 2.14/2.34          | ~ (v4_lattice3 @ X23)
% 2.14/2.34          | ~ (v10_lattices @ X23)
% 2.14/2.34          | (v2_struct_0 @ X23))),
% 2.14/2.34      inference('cnf', [status(esa)], [t45_lattice3])).
% 2.14/2.34  thf('5', plain,
% 2.14/2.34      (![X0 : $i, X1 : $i]:
% 2.14/2.34         ((v2_struct_0 @ X0)
% 2.14/2.34          | ~ (l3_lattices @ X0)
% 2.14/2.34          | ~ (l1_lattices @ X0)
% 2.14/2.34          | (v13_lattices @ X0)
% 2.14/2.34          | (v2_struct_0 @ X0)
% 2.14/2.34          | ~ (v10_lattices @ X0)
% 2.14/2.34          | ~ (v4_lattice3 @ X0)
% 2.14/2.34          | ~ (l3_lattices @ X0)
% 2.14/2.34          | ((sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)
% 2.14/2.34              = (k15_lattice3 @ X0 @ 
% 2.14/2.34                 (a_2_3_lattice3 @ X0 @ 
% 2.14/2.34                  (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)))))),
% 2.14/2.34      inference('sup-', [status(thm)], ['3', '4'])).
% 2.14/2.34  thf('6', plain,
% 2.14/2.34      (![X0 : $i, X1 : $i]:
% 2.14/2.34         (((sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)
% 2.14/2.34            = (k15_lattice3 @ X0 @ 
% 2.14/2.34               (a_2_3_lattice3 @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))))
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | (v13_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['5'])).
% 2.14/2.35  thf('7', plain,
% 2.14/2.35      (![X20 : $i, X21 : $i]:
% 2.14/2.35         (~ (l3_lattices @ X20)
% 2.14/2.35          | (v2_struct_0 @ X20)
% 2.14/2.35          | (m1_subset_1 @ (k15_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 2.14/2.35      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.14/2.35  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.14/2.35  thf('8', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.14/2.35      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.14/2.35  thf(t48_lattice3, axiom,
% 2.14/2.35    (![A:$i]:
% 2.14/2.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.14/2.35         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.14/2.35       ( ![B:$i,C:$i]:
% 2.14/2.35         ( ( ![D:$i]:
% 2.14/2.35             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.14/2.35               ( ~( ( r2_hidden @ D @ B ) & 
% 2.14/2.35                    ( ![E:$i]:
% 2.14/2.35                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 2.14/2.35                        ( ~( ( r3_lattices @ A @ D @ E ) & 
% 2.14/2.35                             ( r2_hidden @ E @ C ) ) ) ) ) ) ) ) ) =>
% 2.14/2.35           ( r3_lattices @
% 2.14/2.35             A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) ) ) ))).
% 2.14/2.35  thf('9', plain,
% 2.14/2.35      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.14/2.35         ((r2_hidden @ (sk_D @ X26 @ X27 @ X25) @ X27)
% 2.14/2.35          | (r3_lattices @ X25 @ (k15_lattice3 @ X25 @ X27) @ 
% 2.14/2.35             (k15_lattice3 @ X25 @ X26))
% 2.14/2.35          | ~ (l3_lattices @ X25)
% 2.14/2.35          | ~ (v4_lattice3 @ X25)
% 2.14/2.35          | ~ (v10_lattices @ X25)
% 2.14/2.35          | (v2_struct_0 @ X25))),
% 2.14/2.35      inference('cnf', [status(esa)], [t48_lattice3])).
% 2.14/2.35  thf(t7_ordinal1, axiom,
% 2.14/2.35    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.14/2.35  thf('10', plain,
% 2.14/2.35      (![X1 : $i, X2 : $i]: (~ (r2_hidden @ X1 @ X2) | ~ (r1_tarski @ X2 @ X1))),
% 2.14/2.35      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.14/2.35  thf('11', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.14/2.35         ((v2_struct_0 @ X1)
% 2.14/2.35          | ~ (v10_lattices @ X1)
% 2.14/2.35          | ~ (v4_lattice3 @ X1)
% 2.14/2.35          | ~ (l3_lattices @ X1)
% 2.14/2.35          | (r3_lattices @ X1 @ (k15_lattice3 @ X1 @ X0) @ 
% 2.14/2.35             (k15_lattice3 @ X1 @ X2))
% 2.14/2.35          | ~ (r1_tarski @ X0 @ (sk_D @ X2 @ X0 @ X1)))),
% 2.14/2.35      inference('sup-', [status(thm)], ['9', '10'])).
% 2.14/2.35  thf('12', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i]:
% 2.14/2.35         ((r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.14/2.35           (k15_lattice3 @ X0 @ X1))
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('sup-', [status(thm)], ['8', '11'])).
% 2.14/2.35  thf('13', plain,
% 2.14/2.35      (![X20 : $i, X21 : $i]:
% 2.14/2.35         (~ (l3_lattices @ X20)
% 2.14/2.35          | (v2_struct_0 @ X20)
% 2.14/2.35          | (m1_subset_1 @ (k15_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 2.14/2.35      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.14/2.35  thf('14', plain,
% 2.14/2.35      (![X20 : $i, X21 : $i]:
% 2.14/2.35         (~ (l3_lattices @ X20)
% 2.14/2.35          | (v2_struct_0 @ X20)
% 2.14/2.35          | (m1_subset_1 @ (k15_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 2.14/2.35      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.14/2.35  thf(redefinition_r3_lattices, axiom,
% 2.14/2.35    (![A:$i,B:$i,C:$i]:
% 2.14/2.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 2.14/2.35         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 2.14/2.35         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 2.14/2.35         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 2.14/2.35       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 2.14/2.35  thf('15', plain,
% 2.14/2.35      (![X8 : $i, X9 : $i, X10 : $i]:
% 2.14/2.35         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 2.14/2.35          | ~ (l3_lattices @ X9)
% 2.14/2.35          | ~ (v9_lattices @ X9)
% 2.14/2.35          | ~ (v8_lattices @ X9)
% 2.14/2.35          | ~ (v6_lattices @ X9)
% 2.14/2.35          | (v2_struct_0 @ X9)
% 2.14/2.35          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 2.14/2.35          | (r1_lattices @ X9 @ X8 @ X10)
% 2.14/2.35          | ~ (r3_lattices @ X9 @ X8 @ X10))),
% 2.14/2.35      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 2.14/2.35  thf('16', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.14/2.35         ((v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.14/2.35          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.14/2.35          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v9_lattices @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0))),
% 2.14/2.35      inference('sup-', [status(thm)], ['14', '15'])).
% 2.14/2.35  thf('17', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.14/2.35         (~ (v9_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.14/2.35          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.14/2.35          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['16'])).
% 2.14/2.35  thf('18', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.14/2.35         ((v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.14/2.35               (k15_lattice3 @ X0 @ X1))
% 2.14/2.35          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.14/2.35             (k15_lattice3 @ X0 @ X1))
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v9_lattices @ X0))),
% 2.14/2.35      inference('sup-', [status(thm)], ['13', '17'])).
% 2.14/2.35  thf('19', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.14/2.35         (~ (v9_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.14/2.35             (k15_lattice3 @ X0 @ X1))
% 2.14/2.35          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.14/2.35               (k15_lattice3 @ X0 @ X1))
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['18'])).
% 2.14/2.35  thf('20', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i]:
% 2.14/2.35         ((v2_struct_0 @ X1)
% 2.14/2.35          | ~ (v10_lattices @ X1)
% 2.14/2.35          | ~ (v4_lattice3 @ X1)
% 2.14/2.35          | ~ (l3_lattices @ X1)
% 2.14/2.35          | (v2_struct_0 @ X1)
% 2.14/2.35          | ~ (l3_lattices @ X1)
% 2.14/2.35          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 2.14/2.35             (k15_lattice3 @ X1 @ X0))
% 2.14/2.35          | ~ (v6_lattices @ X1)
% 2.14/2.35          | ~ (v8_lattices @ X1)
% 2.14/2.35          | ~ (v9_lattices @ X1))),
% 2.14/2.35      inference('sup-', [status(thm)], ['12', '19'])).
% 2.14/2.35  thf('21', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i]:
% 2.14/2.35         (~ (v9_lattices @ X1)
% 2.14/2.35          | ~ (v8_lattices @ X1)
% 2.14/2.35          | ~ (v6_lattices @ X1)
% 2.14/2.35          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 2.14/2.35             (k15_lattice3 @ X1 @ X0))
% 2.14/2.35          | ~ (l3_lattices @ X1)
% 2.14/2.35          | ~ (v4_lattice3 @ X1)
% 2.14/2.35          | ~ (v10_lattices @ X1)
% 2.14/2.35          | (v2_struct_0 @ X1))),
% 2.14/2.35      inference('simplify', [status(thm)], ['20'])).
% 2.14/2.35  thf('22', plain,
% 2.14/2.35      (![X20 : $i, X21 : $i]:
% 2.14/2.35         (~ (l3_lattices @ X20)
% 2.14/2.35          | (v2_struct_0 @ X20)
% 2.14/2.35          | (m1_subset_1 @ (k15_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 2.14/2.35      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.14/2.35  thf(t21_lattices, axiom,
% 2.14/2.35    (![A:$i]:
% 2.14/2.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 2.14/2.35         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 2.14/2.35       ( ![B:$i]:
% 2.14/2.35         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.14/2.35           ( ![C:$i]:
% 2.14/2.35             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.14/2.35               ( ( r1_lattices @ A @ B @ C ) <=>
% 2.14/2.35                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 2.14/2.35  thf('23', plain,
% 2.14/2.35      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.14/2.35         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 2.14/2.35          | ~ (r1_lattices @ X12 @ X11 @ X13)
% 2.14/2.35          | ((k2_lattices @ X12 @ X11 @ X13) = (X11))
% 2.14/2.35          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 2.14/2.35          | ~ (l3_lattices @ X12)
% 2.14/2.35          | ~ (v9_lattices @ X12)
% 2.14/2.35          | ~ (v8_lattices @ X12)
% 2.14/2.35          | (v2_struct_0 @ X12))),
% 2.14/2.35      inference('cnf', [status(esa)], [t21_lattices])).
% 2.14/2.35  thf('24', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.14/2.35         ((v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v9_lattices @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.14/2.35          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.14/2.35              = (k15_lattice3 @ X0 @ X1))
% 2.14/2.35          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 2.14/2.35      inference('sup-', [status(thm)], ['22', '23'])).
% 2.14/2.35  thf('25', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.14/2.35         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.14/2.35          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.14/2.35              = (k15_lattice3 @ X0 @ X1))
% 2.14/2.35          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.14/2.35          | ~ (v9_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['24'])).
% 2.14/2.35  thf('26', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i]:
% 2.14/2.35         ((v2_struct_0 @ X1)
% 2.14/2.35          | ~ (v10_lattices @ X1)
% 2.14/2.35          | ~ (v4_lattice3 @ X1)
% 2.14/2.35          | ~ (l3_lattices @ X1)
% 2.14/2.35          | ~ (v6_lattices @ X1)
% 2.14/2.35          | ~ (v8_lattices @ X1)
% 2.14/2.35          | ~ (v9_lattices @ X1)
% 2.14/2.35          | (v2_struct_0 @ X1)
% 2.14/2.35          | ~ (l3_lattices @ X1)
% 2.14/2.35          | ~ (v8_lattices @ X1)
% 2.14/2.35          | ~ (v9_lattices @ X1)
% 2.14/2.35          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 2.14/2.35          | ((k2_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 2.14/2.35              (k15_lattice3 @ X1 @ X0)) = (k15_lattice3 @ X1 @ k1_xboole_0)))),
% 2.14/2.35      inference('sup-', [status(thm)], ['21', '25'])).
% 2.14/2.35  thf('27', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i]:
% 2.14/2.35         (((k2_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 2.14/2.35            (k15_lattice3 @ X1 @ X0)) = (k15_lattice3 @ X1 @ k1_xboole_0))
% 2.14/2.35          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 2.14/2.35          | ~ (v9_lattices @ X1)
% 2.14/2.35          | ~ (v8_lattices @ X1)
% 2.14/2.35          | ~ (v6_lattices @ X1)
% 2.14/2.35          | ~ (l3_lattices @ X1)
% 2.14/2.35          | ~ (v4_lattice3 @ X1)
% 2.14/2.35          | ~ (v10_lattices @ X1)
% 2.14/2.35          | (v2_struct_0 @ X1))),
% 2.14/2.35      inference('simplify', [status(thm)], ['26'])).
% 2.14/2.35  thf('28', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i]:
% 2.14/2.35         ((v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v9_lattices @ X0)
% 2.14/2.35          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.14/2.35              (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.14/2.35      inference('sup-', [status(thm)], ['7', '27'])).
% 2.14/2.35  thf('29', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i]:
% 2.14/2.35         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.14/2.35            (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.14/2.35          | ~ (v9_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['28'])).
% 2.14/2.35  thf('30', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i]:
% 2.14/2.35         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.14/2.35            (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.14/2.35            = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | (v13_lattices @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v9_lattices @ X0))),
% 2.14/2.35      inference('sup+', [status(thm)], ['6', '29'])).
% 2.14/2.35  thf('31', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i]:
% 2.14/2.35         (~ (v9_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | (v13_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.14/2.35              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.14/2.35              = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.14/2.35      inference('simplify', [status(thm)], ['30'])).
% 2.14/2.35  thf('32', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i]:
% 2.14/2.35         (((sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)
% 2.14/2.35            = (k15_lattice3 @ X0 @ 
% 2.14/2.35               (a_2_3_lattice3 @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))))
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | (v13_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['5'])).
% 2.14/2.35  thf('33', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i]:
% 2.14/2.35         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.14/2.35            (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.14/2.35          | ~ (v9_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['28'])).
% 2.14/2.35  thf('34', plain,
% 2.14/2.35      (![X20 : $i, X21 : $i]:
% 2.14/2.35         (~ (l3_lattices @ X20)
% 2.14/2.35          | (v2_struct_0 @ X20)
% 2.14/2.35          | (m1_subset_1 @ (k15_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 2.14/2.35      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.14/2.35  thf('35', plain,
% 2.14/2.35      (![X20 : $i, X21 : $i]:
% 2.14/2.35         (~ (l3_lattices @ X20)
% 2.14/2.35          | (v2_struct_0 @ X20)
% 2.14/2.35          | (m1_subset_1 @ (k15_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 2.14/2.35      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.14/2.35  thf(d6_lattices, axiom,
% 2.14/2.35    (![A:$i]:
% 2.14/2.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 2.14/2.35       ( ( v6_lattices @ A ) <=>
% 2.14/2.35         ( ![B:$i]:
% 2.14/2.35           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.14/2.35             ( ![C:$i]:
% 2.14/2.35               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.14/2.35                 ( ( k2_lattices @ A @ B @ C ) = ( k2_lattices @ A @ C @ B ) ) ) ) ) ) ) ))).
% 2.14/2.35  thf('36', plain,
% 2.14/2.35      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.14/2.35         (~ (v6_lattices @ X17)
% 2.14/2.35          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 2.14/2.35          | ((k2_lattices @ X17 @ X19 @ X18) = (k2_lattices @ X17 @ X18 @ X19))
% 2.14/2.35          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 2.14/2.35          | ~ (l1_lattices @ X17)
% 2.14/2.35          | (v2_struct_0 @ X17))),
% 2.14/2.35      inference('cnf', [status(esa)], [d6_lattices])).
% 2.14/2.35  thf('37', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.14/2.35         ((v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.14/2.35          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 2.14/2.35              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 2.14/2.35          | ~ (v6_lattices @ X0))),
% 2.14/2.35      inference('sup-', [status(thm)], ['35', '36'])).
% 2.14/2.35  thf('38', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.14/2.35         (~ (v6_lattices @ X0)
% 2.14/2.35          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 2.14/2.35              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 2.14/2.35          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['37'])).
% 2.14/2.35  thf('39', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.14/2.35         ((v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.14/2.35              (k15_lattice3 @ X0 @ X2))
% 2.14/2.35              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.14/2.35                 (k15_lattice3 @ X0 @ X1)))
% 2.14/2.35          | ~ (v6_lattices @ X0))),
% 2.14/2.35      inference('sup-', [status(thm)], ['34', '38'])).
% 2.14/2.35  thf('40', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.14/2.35         (~ (v6_lattices @ X0)
% 2.14/2.35          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.14/2.35              (k15_lattice3 @ X0 @ X2))
% 2.14/2.35              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.14/2.35                 (k15_lattice3 @ X0 @ X1)))
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['39'])).
% 2.14/2.35  thf('41', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i]:
% 2.14/2.35         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.14/2.35            = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.14/2.35               (k15_lattice3 @ X0 @ k1_xboole_0)))
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v9_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0))),
% 2.14/2.35      inference('sup+', [status(thm)], ['33', '40'])).
% 2.14/2.35  thf('42', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i]:
% 2.14/2.35         (~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (v9_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.14/2.35              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.14/2.35                 (k15_lattice3 @ X0 @ k1_xboole_0))))),
% 2.14/2.35      inference('simplify', [status(thm)], ['41'])).
% 2.14/2.35  thf('43', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i]:
% 2.14/2.35         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.14/2.35            = (k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.14/2.35               (k15_lattice3 @ X0 @ k1_xboole_0)))
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | (v13_lattices @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v9_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0))),
% 2.14/2.35      inference('sup+', [status(thm)], ['32', '42'])).
% 2.14/2.35  thf('44', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i]:
% 2.14/2.35         (~ (v9_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | (v13_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.14/2.35              = (k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.14/2.35                 (k15_lattice3 @ X0 @ k1_xboole_0))))),
% 2.14/2.35      inference('simplify', [status(thm)], ['43'])).
% 2.14/2.35  thf('45', plain,
% 2.14/2.35      (![X20 : $i, X21 : $i]:
% 2.14/2.35         (~ (l3_lattices @ X20)
% 2.14/2.35          | (v2_struct_0 @ X20)
% 2.14/2.35          | (m1_subset_1 @ (k15_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 2.14/2.35      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.14/2.35  thf('46', plain,
% 2.14/2.35      (![X14 : $i, X15 : $i]:
% 2.14/2.35         (((k2_lattices @ X15 @ (sk_C_1 @ X14 @ X15) @ X14) != (X14))
% 2.14/2.35          | ((k2_lattices @ X15 @ X14 @ (sk_C_1 @ X14 @ X15)) != (X14))
% 2.14/2.35          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 2.14/2.35          | (v13_lattices @ X15)
% 2.14/2.35          | ~ (l1_lattices @ X15)
% 2.14/2.35          | (v2_struct_0 @ X15))),
% 2.14/2.35      inference('cnf', [status(esa)], [d13_lattices])).
% 2.14/2.35  thf('47', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i]:
% 2.14/2.35         ((v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | (v13_lattices @ X0)
% 2.14/2.35          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.14/2.35              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.14/2.35              != (k15_lattice3 @ X0 @ X1))
% 2.14/2.35          | ((k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.14/2.35              (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1)))),
% 2.14/2.35      inference('sup-', [status(thm)], ['45', '46'])).
% 2.14/2.35  thf('48', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i]:
% 2.14/2.35         (((k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.14/2.35            (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1))
% 2.14/2.35          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.14/2.35              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.14/2.35              != (k15_lattice3 @ X0 @ X1))
% 2.14/2.35          | (v13_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['47'])).
% 2.14/2.35  thf('49', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.14/2.35            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | (v13_lattices @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v9_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | (v13_lattices @ X0)
% 2.14/2.35          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.14/2.35              (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 2.14/2.35              != (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.14/2.35      inference('sup-', [status(thm)], ['44', '48'])).
% 2.14/2.35  thf('50', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.14/2.35            (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 2.14/2.35            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.14/2.35          | ~ (v9_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | (v13_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['49'])).
% 2.14/2.35  thf('51', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.14/2.35            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | (v13_lattices @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v9_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | (v13_lattices @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v9_lattices @ X0))),
% 2.14/2.35      inference('sup-', [status(thm)], ['31', '50'])).
% 2.14/2.35  thf('52', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         (~ (v9_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | (v13_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['51'])).
% 2.14/2.35  thf(t50_lattice3, conjecture,
% 2.14/2.35    (![A:$i]:
% 2.14/2.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.14/2.35         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.14/2.35       ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.14/2.35         ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 2.14/2.35         ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ))).
% 2.14/2.35  thf(zf_stmt_0, negated_conjecture,
% 2.14/2.35    (~( ![A:$i]:
% 2.14/2.35        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.14/2.35            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.14/2.35          ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.14/2.35            ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 2.14/2.35            ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ) )),
% 2.14/2.35    inference('cnf.neg', [status(esa)], [t50_lattice3])).
% 2.14/2.35  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('54', plain,
% 2.14/2.35      ((~ (l3_lattices @ sk_A)
% 2.14/2.35        | ~ (l1_lattices @ sk_A)
% 2.14/2.35        | (v13_lattices @ sk_A)
% 2.14/2.35        | ~ (v10_lattices @ sk_A)
% 2.14/2.35        | ~ (v4_lattice3 @ sk_A)
% 2.14/2.35        | ~ (v6_lattices @ sk_A)
% 2.14/2.35        | ~ (v8_lattices @ sk_A)
% 2.14/2.35        | ~ (v9_lattices @ sk_A))),
% 2.14/2.35      inference('sup-', [status(thm)], ['52', '53'])).
% 2.14/2.35  thf('55', plain, ((l3_lattices @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('56', plain, ((l3_lattices @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf(dt_l3_lattices, axiom,
% 2.14/2.35    (![A:$i]:
% 2.14/2.35     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 2.14/2.35  thf('57', plain, (![X7 : $i]: ((l1_lattices @ X7) | ~ (l3_lattices @ X7))),
% 2.14/2.35      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 2.14/2.35  thf('58', plain, ((l1_lattices @ sk_A)),
% 2.14/2.35      inference('sup-', [status(thm)], ['56', '57'])).
% 2.14/2.35  thf('59', plain, ((v10_lattices @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('60', plain, ((v4_lattice3 @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf(cc1_lattices, axiom,
% 2.14/2.35    (![A:$i]:
% 2.14/2.35     ( ( l3_lattices @ A ) =>
% 2.14/2.35       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 2.14/2.35         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 2.14/2.35           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 2.14/2.35           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 2.14/2.35  thf('61', plain,
% 2.14/2.35      (![X3 : $i]:
% 2.14/2.35         ((v2_struct_0 @ X3)
% 2.14/2.35          | ~ (v10_lattices @ X3)
% 2.14/2.35          | (v6_lattices @ X3)
% 2.14/2.35          | ~ (l3_lattices @ X3))),
% 2.14/2.35      inference('cnf', [status(esa)], [cc1_lattices])).
% 2.14/2.35  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('63', plain,
% 2.14/2.35      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 2.14/2.35      inference('sup-', [status(thm)], ['61', '62'])).
% 2.14/2.35  thf('64', plain, ((l3_lattices @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('65', plain, ((v10_lattices @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('66', plain, ((v6_lattices @ sk_A)),
% 2.14/2.35      inference('demod', [status(thm)], ['63', '64', '65'])).
% 2.14/2.35  thf('67', plain,
% 2.14/2.35      (![X3 : $i]:
% 2.14/2.35         ((v2_struct_0 @ X3)
% 2.14/2.35          | ~ (v10_lattices @ X3)
% 2.14/2.35          | (v8_lattices @ X3)
% 2.14/2.35          | ~ (l3_lattices @ X3))),
% 2.14/2.35      inference('cnf', [status(esa)], [cc1_lattices])).
% 2.14/2.35  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('69', plain,
% 2.14/2.35      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 2.14/2.35      inference('sup-', [status(thm)], ['67', '68'])).
% 2.14/2.35  thf('70', plain, ((l3_lattices @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('71', plain, ((v10_lattices @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('72', plain, ((v8_lattices @ sk_A)),
% 2.14/2.35      inference('demod', [status(thm)], ['69', '70', '71'])).
% 2.14/2.35  thf('73', plain,
% 2.14/2.35      (![X3 : $i]:
% 2.14/2.35         ((v2_struct_0 @ X3)
% 2.14/2.35          | ~ (v10_lattices @ X3)
% 2.14/2.35          | (v9_lattices @ X3)
% 2.14/2.35          | ~ (l3_lattices @ X3))),
% 2.14/2.35      inference('cnf', [status(esa)], [cc1_lattices])).
% 2.14/2.35  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('75', plain,
% 2.14/2.35      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 2.14/2.35      inference('sup-', [status(thm)], ['73', '74'])).
% 2.14/2.35  thf('76', plain, ((l3_lattices @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('77', plain, ((v10_lattices @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('78', plain, ((v9_lattices @ sk_A)),
% 2.14/2.35      inference('demod', [status(thm)], ['75', '76', '77'])).
% 2.14/2.35  thf('79', plain, ((v13_lattices @ sk_A)),
% 2.14/2.35      inference('demod', [status(thm)],
% 2.14/2.35                ['54', '55', '58', '59', '60', '66', '72', '78'])).
% 2.14/2.35  thf('80', plain,
% 2.14/2.35      (![X20 : $i, X21 : $i]:
% 2.14/2.35         (~ (l3_lattices @ X20)
% 2.14/2.35          | (v2_struct_0 @ X20)
% 2.14/2.35          | (m1_subset_1 @ (k15_lattice3 @ X20 @ X21) @ (u1_struct_0 @ X20)))),
% 2.14/2.35      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.14/2.35  thf('81', plain,
% 2.14/2.35      (![X15 : $i, X16 : $i]:
% 2.14/2.35         (~ (v13_lattices @ X15)
% 2.14/2.35          | ((k2_lattices @ X15 @ X16 @ (sk_B @ X15)) = (sk_B @ X15))
% 2.14/2.35          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 2.14/2.35          | ~ (l1_lattices @ X15)
% 2.14/2.35          | (v2_struct_0 @ X15))),
% 2.14/2.35      inference('cnf', [status(esa)], [d13_lattices])).
% 2.14/2.35  thf('82', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i]:
% 2.14/2.35         ((v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (sk_B @ X0))
% 2.14/2.35              = (sk_B @ X0))
% 2.14/2.35          | ~ (v13_lattices @ X0))),
% 2.14/2.35      inference('sup-', [status(thm)], ['80', '81'])).
% 2.14/2.35  thf('83', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i]:
% 2.14/2.35         (~ (v13_lattices @ X0)
% 2.14/2.35          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (sk_B @ X0))
% 2.14/2.35              = (sk_B @ X0))
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['82'])).
% 2.14/2.35  thf('84', plain,
% 2.14/2.35      (![X15 : $i]:
% 2.14/2.35         (~ (v13_lattices @ X15)
% 2.14/2.35          | (m1_subset_1 @ (sk_B @ X15) @ (u1_struct_0 @ X15))
% 2.14/2.35          | ~ (l1_lattices @ X15)
% 2.14/2.35          | (v2_struct_0 @ X15))),
% 2.14/2.35      inference('cnf', [status(esa)], [d13_lattices])).
% 2.14/2.35  thf('85', plain,
% 2.14/2.35      (![X22 : $i, X23 : $i]:
% 2.14/2.35         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 2.14/2.35          | ((X22) = (k15_lattice3 @ X23 @ (a_2_3_lattice3 @ X23 @ X22)))
% 2.14/2.35          | ~ (l3_lattices @ X23)
% 2.14/2.35          | ~ (v4_lattice3 @ X23)
% 2.14/2.35          | ~ (v10_lattices @ X23)
% 2.14/2.35          | (v2_struct_0 @ X23))),
% 2.14/2.35      inference('cnf', [status(esa)], [t45_lattice3])).
% 2.14/2.35  thf('86', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         ((v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ((sk_B @ X0)
% 2.14/2.35              = (k15_lattice3 @ X0 @ (a_2_3_lattice3 @ X0 @ (sk_B @ X0)))))),
% 2.14/2.35      inference('sup-', [status(thm)], ['84', '85'])).
% 2.14/2.35  thf('87', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         (((sk_B @ X0)
% 2.14/2.35            = (k15_lattice3 @ X0 @ (a_2_3_lattice3 @ X0 @ (sk_B @ X0))))
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['86'])).
% 2.14/2.35  thf('88', plain,
% 2.14/2.35      (![X0 : $i, X1 : $i]:
% 2.14/2.35         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.14/2.35            (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.14/2.35          | ~ (v9_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['28'])).
% 2.14/2.35  thf('89', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ (sk_B @ X0))
% 2.14/2.35            = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v9_lattices @ X0))),
% 2.14/2.35      inference('sup+', [status(thm)], ['87', '88'])).
% 2.14/2.35  thf('90', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         (~ (v9_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.14/2.35              (sk_B @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.14/2.35      inference('simplify', [status(thm)], ['89'])).
% 2.14/2.35  thf('91', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         (((sk_B @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v9_lattices @ X0))),
% 2.14/2.35      inference('sup+', [status(thm)], ['83', '90'])).
% 2.14/2.35  thf('92', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         (~ (v9_lattices @ X0)
% 2.14/2.35          | ~ (v8_lattices @ X0)
% 2.14/2.35          | ~ (v6_lattices @ X0)
% 2.14/2.35          | ~ (v4_lattice3 @ X0)
% 2.14/2.35          | ~ (v10_lattices @ X0)
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (l3_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ((sk_B @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.14/2.35      inference('simplify', [status(thm)], ['91'])).
% 2.14/2.35  thf('93', plain,
% 2.14/2.35      (((v2_struct_0 @ sk_A)
% 2.14/2.35        | ~ (v10_lattices @ sk_A)
% 2.14/2.35        | ~ (v13_lattices @ sk_A)
% 2.14/2.35        | ~ (l3_lattices @ sk_A)
% 2.14/2.35        | ((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('94', plain,
% 2.14/2.35      ((((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))
% 2.14/2.35         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.14/2.35      inference('split', [status(esa)], ['93'])).
% 2.14/2.35  thf('95', plain,
% 2.14/2.35      (((((k5_lattices @ sk_A) != (sk_B @ sk_A))
% 2.14/2.35         | (v2_struct_0 @ sk_A)
% 2.14/2.35         | ~ (l3_lattices @ sk_A)
% 2.14/2.35         | ~ (l1_lattices @ sk_A)
% 2.14/2.35         | ~ (v13_lattices @ sk_A)
% 2.14/2.35         | ~ (v10_lattices @ sk_A)
% 2.14/2.35         | ~ (v4_lattice3 @ sk_A)
% 2.14/2.35         | ~ (v6_lattices @ sk_A)
% 2.14/2.35         | ~ (v8_lattices @ sk_A)
% 2.14/2.35         | ~ (v9_lattices @ sk_A)))
% 2.14/2.35         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.14/2.35      inference('sup-', [status(thm)], ['92', '94'])).
% 2.14/2.35  thf('96', plain, ((l3_lattices @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('97', plain, ((l1_lattices @ sk_A)),
% 2.14/2.35      inference('sup-', [status(thm)], ['56', '57'])).
% 2.14/2.35  thf('98', plain, ((v10_lattices @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('99', plain, ((v4_lattice3 @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('100', plain, ((v6_lattices @ sk_A)),
% 2.14/2.35      inference('demod', [status(thm)], ['63', '64', '65'])).
% 2.14/2.35  thf('101', plain, ((v8_lattices @ sk_A)),
% 2.14/2.35      inference('demod', [status(thm)], ['69', '70', '71'])).
% 2.14/2.35  thf('102', plain, ((v9_lattices @ sk_A)),
% 2.14/2.35      inference('demod', [status(thm)], ['75', '76', '77'])).
% 2.14/2.35  thf('103', plain,
% 2.14/2.35      (((((k5_lattices @ sk_A) != (sk_B @ sk_A))
% 2.14/2.35         | (v2_struct_0 @ sk_A)
% 2.14/2.35         | ~ (v13_lattices @ sk_A)))
% 2.14/2.35         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.14/2.35      inference('demod', [status(thm)],
% 2.14/2.35                ['95', '96', '97', '98', '99', '100', '101', '102'])).
% 2.14/2.35  thf('104', plain,
% 2.14/2.35      (![X15 : $i]:
% 2.14/2.35         (~ (v13_lattices @ X15)
% 2.14/2.35          | (m1_subset_1 @ (sk_B @ X15) @ (u1_struct_0 @ X15))
% 2.14/2.35          | ~ (l1_lattices @ X15)
% 2.14/2.35          | (v2_struct_0 @ X15))),
% 2.14/2.35      inference('cnf', [status(esa)], [d13_lattices])).
% 2.14/2.35  thf(d16_lattices, axiom,
% 2.14/2.35    (![A:$i]:
% 2.14/2.35     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 2.14/2.35       ( ( v13_lattices @ A ) =>
% 2.14/2.35         ( ![B:$i]:
% 2.14/2.35           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.14/2.35             ( ( ( B ) = ( k5_lattices @ A ) ) <=>
% 2.14/2.35               ( ![C:$i]:
% 2.14/2.35                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.14/2.35                   ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 2.14/2.35                     ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 2.14/2.35  thf('105', plain,
% 2.14/2.35      (![X4 : $i, X5 : $i]:
% 2.14/2.35         (~ (v13_lattices @ X4)
% 2.14/2.35          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 2.14/2.35          | (m1_subset_1 @ (sk_C @ X5 @ X4) @ (u1_struct_0 @ X4))
% 2.14/2.35          | ((X5) = (k5_lattices @ X4))
% 2.14/2.35          | ~ (l1_lattices @ X4)
% 2.14/2.35          | (v2_struct_0 @ X4))),
% 2.14/2.35      inference('cnf', [status(esa)], [d16_lattices])).
% 2.14/2.35  thf('106', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         ((v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ((sk_B @ X0) = (k5_lattices @ X0))
% 2.14/2.35          | (m1_subset_1 @ (sk_C @ (sk_B @ X0) @ X0) @ (u1_struct_0 @ X0))
% 2.14/2.35          | ~ (v13_lattices @ X0))),
% 2.14/2.35      inference('sup-', [status(thm)], ['104', '105'])).
% 2.14/2.35  thf('107', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         ((m1_subset_1 @ (sk_C @ (sk_B @ X0) @ X0) @ (u1_struct_0 @ X0))
% 2.14/2.35          | ((sk_B @ X0) = (k5_lattices @ X0))
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['106'])).
% 2.14/2.35  thf('108', plain,
% 2.14/2.35      (![X15 : $i, X16 : $i]:
% 2.14/2.35         (~ (v13_lattices @ X15)
% 2.14/2.35          | ((k2_lattices @ X15 @ (sk_B @ X15) @ X16) = (sk_B @ X15))
% 2.14/2.35          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 2.14/2.35          | ~ (l1_lattices @ X15)
% 2.14/2.35          | (v2_struct_0 @ X15))),
% 2.14/2.35      inference('cnf', [status(esa)], [d13_lattices])).
% 2.14/2.35  thf('109', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         ((v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | ((sk_B @ X0) = (k5_lattices @ X0))
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ((k2_lattices @ X0 @ (sk_B @ X0) @ (sk_C @ (sk_B @ X0) @ X0))
% 2.14/2.35              = (sk_B @ X0))
% 2.14/2.35          | ~ (v13_lattices @ X0))),
% 2.14/2.35      inference('sup-', [status(thm)], ['107', '108'])).
% 2.14/2.35  thf('110', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         (((k2_lattices @ X0 @ (sk_B @ X0) @ (sk_C @ (sk_B @ X0) @ X0))
% 2.14/2.35            = (sk_B @ X0))
% 2.14/2.35          | ((sk_B @ X0) = (k5_lattices @ X0))
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['109'])).
% 2.14/2.35  thf('111', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         ((m1_subset_1 @ (sk_C @ (sk_B @ X0) @ X0) @ (u1_struct_0 @ X0))
% 2.14/2.35          | ((sk_B @ X0) = (k5_lattices @ X0))
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['106'])).
% 2.14/2.35  thf('112', plain,
% 2.14/2.35      (![X15 : $i, X16 : $i]:
% 2.14/2.35         (~ (v13_lattices @ X15)
% 2.14/2.35          | ((k2_lattices @ X15 @ X16 @ (sk_B @ X15)) = (sk_B @ X15))
% 2.14/2.35          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 2.14/2.35          | ~ (l1_lattices @ X15)
% 2.14/2.35          | (v2_struct_0 @ X15))),
% 2.14/2.35      inference('cnf', [status(esa)], [d13_lattices])).
% 2.14/2.35  thf('113', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         ((v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | ((sk_B @ X0) = (k5_lattices @ X0))
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ((k2_lattices @ X0 @ (sk_C @ (sk_B @ X0) @ X0) @ (sk_B @ X0))
% 2.14/2.35              = (sk_B @ X0))
% 2.14/2.35          | ~ (v13_lattices @ X0))),
% 2.14/2.35      inference('sup-', [status(thm)], ['111', '112'])).
% 2.14/2.35  thf('114', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         (((k2_lattices @ X0 @ (sk_C @ (sk_B @ X0) @ X0) @ (sk_B @ X0))
% 2.14/2.35            = (sk_B @ X0))
% 2.14/2.35          | ((sk_B @ X0) = (k5_lattices @ X0))
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['113'])).
% 2.14/2.35  thf('115', plain,
% 2.14/2.35      (![X15 : $i]:
% 2.14/2.35         (~ (v13_lattices @ X15)
% 2.14/2.35          | (m1_subset_1 @ (sk_B @ X15) @ (u1_struct_0 @ X15))
% 2.14/2.35          | ~ (l1_lattices @ X15)
% 2.14/2.35          | (v2_struct_0 @ X15))),
% 2.14/2.35      inference('cnf', [status(esa)], [d13_lattices])).
% 2.14/2.35  thf('116', plain,
% 2.14/2.35      (![X4 : $i, X5 : $i]:
% 2.14/2.35         (~ (v13_lattices @ X4)
% 2.14/2.35          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 2.14/2.35          | ((k2_lattices @ X4 @ (sk_C @ X5 @ X4) @ X5) != (X5))
% 2.14/2.35          | ((k2_lattices @ X4 @ X5 @ (sk_C @ X5 @ X4)) != (X5))
% 2.14/2.35          | ((X5) = (k5_lattices @ X4))
% 2.14/2.35          | ~ (l1_lattices @ X4)
% 2.14/2.35          | (v2_struct_0 @ X4))),
% 2.14/2.35      inference('cnf', [status(esa)], [d16_lattices])).
% 2.14/2.35  thf('117', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         ((v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ((sk_B @ X0) = (k5_lattices @ X0))
% 2.14/2.35          | ((k2_lattices @ X0 @ (sk_B @ X0) @ (sk_C @ (sk_B @ X0) @ X0))
% 2.14/2.35              != (sk_B @ X0))
% 2.14/2.35          | ((k2_lattices @ X0 @ (sk_C @ (sk_B @ X0) @ X0) @ (sk_B @ X0))
% 2.14/2.35              != (sk_B @ X0))
% 2.14/2.35          | ~ (v13_lattices @ X0))),
% 2.14/2.35      inference('sup-', [status(thm)], ['115', '116'])).
% 2.14/2.35  thf('118', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         (((k2_lattices @ X0 @ (sk_C @ (sk_B @ X0) @ X0) @ (sk_B @ X0))
% 2.14/2.35            != (sk_B @ X0))
% 2.14/2.35          | ((k2_lattices @ X0 @ (sk_B @ X0) @ (sk_C @ (sk_B @ X0) @ X0))
% 2.14/2.35              != (sk_B @ X0))
% 2.14/2.35          | ((sk_B @ X0) = (k5_lattices @ X0))
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['117'])).
% 2.14/2.35  thf('119', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         (((sk_B @ X0) != (sk_B @ X0))
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | ((sk_B @ X0) = (k5_lattices @ X0))
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | ((sk_B @ X0) = (k5_lattices @ X0))
% 2.14/2.35          | ((k2_lattices @ X0 @ (sk_B @ X0) @ (sk_C @ (sk_B @ X0) @ X0))
% 2.14/2.35              != (sk_B @ X0)))),
% 2.14/2.35      inference('sup-', [status(thm)], ['114', '118'])).
% 2.14/2.35  thf('120', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         (((k2_lattices @ X0 @ (sk_B @ X0) @ (sk_C @ (sk_B @ X0) @ X0))
% 2.14/2.35            != (sk_B @ X0))
% 2.14/2.35          | ((sk_B @ X0) = (k5_lattices @ X0))
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['119'])).
% 2.14/2.35  thf('121', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         (((sk_B @ X0) != (sk_B @ X0))
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | ((sk_B @ X0) = (k5_lattices @ X0))
% 2.14/2.35          | (v2_struct_0 @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | ((sk_B @ X0) = (k5_lattices @ X0)))),
% 2.14/2.35      inference('sup-', [status(thm)], ['110', '120'])).
% 2.14/2.35  thf('122', plain,
% 2.14/2.35      (![X0 : $i]:
% 2.14/2.35         (((sk_B @ X0) = (k5_lattices @ X0))
% 2.14/2.35          | ~ (v13_lattices @ X0)
% 2.14/2.35          | ~ (l1_lattices @ X0)
% 2.14/2.35          | (v2_struct_0 @ X0))),
% 2.14/2.35      inference('simplify', [status(thm)], ['121'])).
% 2.14/2.35  thf('123', plain, (~ (v2_struct_0 @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('124', plain,
% 2.14/2.35      ((~ (l1_lattices @ sk_A)
% 2.14/2.35        | ~ (v13_lattices @ sk_A)
% 2.14/2.35        | ((sk_B @ sk_A) = (k5_lattices @ sk_A)))),
% 2.14/2.35      inference('sup-', [status(thm)], ['122', '123'])).
% 2.14/2.35  thf('125', plain, ((l1_lattices @ sk_A)),
% 2.14/2.35      inference('sup-', [status(thm)], ['56', '57'])).
% 2.14/2.35  thf('126', plain,
% 2.14/2.35      ((~ (v13_lattices @ sk_A) | ((sk_B @ sk_A) = (k5_lattices @ sk_A)))),
% 2.14/2.35      inference('demod', [status(thm)], ['124', '125'])).
% 2.14/2.35  thf('127', plain,
% 2.14/2.35      (((~ (v13_lattices @ sk_A) | (v2_struct_0 @ sk_A)))
% 2.14/2.35         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.14/2.35      inference('clc', [status(thm)], ['103', '126'])).
% 2.14/2.35  thf('128', plain, (~ (v2_struct_0 @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('129', plain,
% 2.14/2.35      ((~ (v13_lattices @ sk_A))
% 2.14/2.35         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.14/2.35      inference('clc', [status(thm)], ['127', '128'])).
% 2.14/2.35  thf('130', plain,
% 2.14/2.35      (($false)
% 2.14/2.35         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.14/2.35      inference('sup-', [status(thm)], ['79', '129'])).
% 2.14/2.35  thf('131', plain, (((v2_struct_0 @ sk_A)) <= (((v2_struct_0 @ sk_A)))),
% 2.14/2.35      inference('split', [status(esa)], ['93'])).
% 2.14/2.35  thf('132', plain, (~ (v2_struct_0 @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('133', plain, (~ ((v2_struct_0 @ sk_A))),
% 2.14/2.35      inference('sup-', [status(thm)], ['131', '132'])).
% 2.14/2.35  thf('134', plain, ((l3_lattices @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('135', plain, ((~ (l3_lattices @ sk_A)) <= (~ ((l3_lattices @ sk_A)))),
% 2.14/2.35      inference('split', [status(esa)], ['93'])).
% 2.14/2.35  thf('136', plain, (((l3_lattices @ sk_A))),
% 2.14/2.35      inference('sup-', [status(thm)], ['134', '135'])).
% 2.14/2.35  thf('137', plain, ((v10_lattices @ sk_A)),
% 2.14/2.35      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.14/2.35  thf('138', plain, ((~ (v10_lattices @ sk_A)) <= (~ ((v10_lattices @ sk_A)))),
% 2.14/2.35      inference('split', [status(esa)], ['93'])).
% 2.14/2.35  thf('139', plain, (((v10_lattices @ sk_A))),
% 2.14/2.35      inference('sup-', [status(thm)], ['137', '138'])).
% 2.14/2.35  thf('140', plain, ((v13_lattices @ sk_A)),
% 2.14/2.35      inference('demod', [status(thm)],
% 2.14/2.35                ['54', '55', '58', '59', '60', '66', '72', '78'])).
% 2.14/2.35  thf('141', plain, ((~ (v13_lattices @ sk_A)) <= (~ ((v13_lattices @ sk_A)))),
% 2.14/2.35      inference('split', [status(esa)], ['93'])).
% 2.14/2.35  thf('142', plain, (((v13_lattices @ sk_A))),
% 2.14/2.35      inference('sup-', [status(thm)], ['140', '141'])).
% 2.14/2.35  thf('143', plain,
% 2.14/2.35      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))) | 
% 2.14/2.35       ~ ((v13_lattices @ sk_A)) | ~ ((v10_lattices @ sk_A)) | 
% 2.14/2.35       ~ ((l3_lattices @ sk_A)) | ((v2_struct_0 @ sk_A))),
% 2.14/2.35      inference('split', [status(esa)], ['93'])).
% 2.14/2.35  thf('144', plain,
% 2.14/2.35      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 2.14/2.35      inference('sat_resolution*', [status(thm)],
% 2.14/2.35                ['133', '136', '139', '142', '143'])).
% 2.14/2.35  thf('145', plain, ($false),
% 2.14/2.35      inference('simpl_trail', [status(thm)], ['130', '144'])).
% 2.14/2.35  
% 2.14/2.35  % SZS output end Refutation
% 2.14/2.35  
% 2.14/2.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
