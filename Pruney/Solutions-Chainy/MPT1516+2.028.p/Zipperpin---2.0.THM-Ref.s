%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oR0WT3YlCY

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:38 EST 2020

% Result     : Theorem 2.78s
% Output     : Refutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 504 expanded)
%              Number of leaves         :   40 ( 157 expanded)
%              Depth                    :   24
%              Number of atoms          : 2447 (8500 expanded)
%              Number of equality atoms :   73 ( 252 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(a_2_4_lattice3_type,type,(
    a_2_4_lattice3: $i > $i > $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(a_2_3_lattice3_type,type,(
    a_2_3_lattice3: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l3_lattices @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ X13 @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( v13_lattices @ X14 )
      | ~ ( l1_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( X21
        = ( k15_lattice3 @ X22 @ ( a_2_3_lattice3 @ X22 @ X21 ) ) )
      | ~ ( l3_lattices @ X22 )
      | ~ ( v4_lattice3 @ X22 )
      | ~ ( v10_lattices @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ~ ( l3_lattices @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
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

thf('9',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ X23 @ X24 )
      | ( r3_lattices @ X25 @ ( k15_lattice3 @ X25 @ X23 ) @ ( k15_lattice3 @ X25 @ X24 ) )
      | ~ ( l3_lattices @ X25 )
      | ~ ( v4_lattice3 @ X25 )
      | ~ ( v10_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t46_lattice3])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l3_lattices @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l3_lattices @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
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

thf('13',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l3_lattices @ X8 )
      | ~ ( v9_lattices @ X8 )
      | ~ ( v8_lattices @ X8 )
      | ~ ( v6_lattices @ X8 )
      | ( v2_struct_0 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ( r1_lattices @ X8 @ X7 @ X9 )
      | ~ ( r3_lattices @ X8 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('14',plain,(
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
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
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
    inference('sup-',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
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
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X1 )
      | ~ ( v8_lattices @ X1 )
      | ~ ( v6_lattices @ X1 )
      | ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l3_lattices @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
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

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_lattices @ X11 @ X10 @ X12 )
      | ( ( k2_lattices @ X11 @ X10 @ X12 )
        = X10 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l3_lattices @ X11 )
      | ~ ( v9_lattices @ X11 )
      | ~ ( v8_lattices @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('22',plain,(
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
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
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
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
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
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
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
    inference('sup-',[status(thm)],['7','25'])).

thf('27',plain,(
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
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
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
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','27'])).

thf('29',plain,(
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
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
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

thf('31',plain,(
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
    inference(simplify,[status(thm)],['26'])).

thf('32',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l3_lattices @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('33',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l3_lattices @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
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

thf('34',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( v6_lattices @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( ( k2_lattices @ X16 @ X18 @ X17 )
        = ( k2_lattices @ X16 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l1_lattices @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d6_lattices])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ X2 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) ) )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ X2 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) ) )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
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
    inference('sup+',[status(thm)],['31','38'])).

thf('40',plain,(
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
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
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
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','40'])).

thf('42',plain,(
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
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l3_lattices @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_lattices @ X14 @ ( sk_C_1 @ X13 @ X14 ) @ X13 )
       != X13 )
      | ( ( k2_lattices @ X14 @ X13 @ ( sk_C_1 @ X13 @ X14 ) )
       != X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ( v13_lattices @ X14 )
      | ~ ( l1_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d13_lattices])).

thf('45',plain,(
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
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
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
    inference('sup-',[status(thm)],['42','46'])).

thf('48',plain,(
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
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','48'])).

thf('50',plain,(
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
    inference(simplify,[status(thm)],['49'])).

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

thf('51',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( v13_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('55',plain,(
    ! [X6: $i] :
      ( ( l1_lattices @ X6 )
      | ~ ( l3_lattices @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('56',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
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

thf('59',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v6_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v8_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v9_lattices @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['52','53','56','57','58','64','70','76'])).

thf('78',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l3_lattices @ X19 )
      | ( v2_struct_0 @ X19 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X19 @ X20 ) @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(dt_k5_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('79',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
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

thf('80',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( v13_lattices @ X2 )
      | ~ ( m1_subset_1 @ X3 @ ( u1_struct_0 @ X2 ) )
      | ( X3
       != ( k5_lattices @ X2 ) )
      | ( ( k2_lattices @ X2 @ X4 @ X3 )
        = X3 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_lattices @ X2 )
      | ( v2_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d16_lattices])).

thf('81',plain,(
    ! [X2: $i,X4: $i] :
      ( ( v2_struct_0 @ X2 )
      | ~ ( l1_lattices @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X2 ) )
      | ( ( k2_lattices @ X2 @ X4 @ ( k5_lattices @ X2 ) )
        = ( k5_lattices @ X2 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X2 ) @ ( u1_struct_0 @ X2 ) )
      | ~ ( v13_lattices @ X2 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('87',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('88',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X22 ) )
      | ( X21
        = ( k15_lattice3 @ X22 @ ( a_2_3_lattice3 @ X22 @ X21 ) ) )
      | ~ ( l3_lattices @ X22 )
      | ~ ( v4_lattice3 @ X22 )
      | ~ ( v10_lattices @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t45_lattice3])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ ( a_2_3_lattice3 @ X0 @ ( k5_lattices @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ ( a_2_3_lattice3 @ X0 @ ( k5_lattices @ X0 ) ) ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('92',plain,(
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
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X5 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('96',plain,(
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
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
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
    inference('sup-',[status(thm)],['93','97'])).

thf('99',plain,(
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
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('101',plain,(
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
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
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
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
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
    inference('sup-',[status(thm)],['86','102'])).

thf('104',plain,(
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
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
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
    inference('sup+',[status(thm)],['85','104'])).

thf('106',plain,(
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
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['107'])).

thf('109',plain,
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
    inference('sup-',[status(thm)],['106','108'])).

thf('110',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['54','55'])).

thf('112',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('115',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('116',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('117',plain,
    ( ( ( ( k5_lattices @ sk_A )
       != ( k5_lattices @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v13_lattices @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['109','110','111','112','113','114','115','116'])).

thf('118',plain,
    ( ( ~ ( v13_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,
    ( $false
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['77','120'])).

thf('122',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['107'])).

thf('123',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ~ ( l3_lattices @ sk_A )
   <= ~ ( l3_lattices @ sk_A ) ),
    inference(split,[status(esa)],['107'])).

thf('127',plain,(
    l3_lattices @ sk_A ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ~ ( v10_lattices @ sk_A )
   <= ~ ( v10_lattices @ sk_A ) ),
    inference(split,[status(esa)],['107'])).

thf('130',plain,(
    v10_lattices @ sk_A ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['52','53','56','57','58','64','70','76'])).

thf('132',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ~ ( v13_lattices @ sk_A ) ),
    inference(split,[status(esa)],['107'])).

thf('133',plain,(
    v13_lattices @ sk_A ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['107'])).

thf('135',plain,(
    ( k5_lattices @ sk_A )
 != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ),
    inference('sat_resolution*',[status(thm)],['124','127','130','133','134'])).

thf('136',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['121','135'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oR0WT3YlCY
% 0.14/0.37  % Computer   : n008.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 11:48:00 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 2.78/2.97  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.78/2.97  % Solved by: fo/fo7.sh
% 2.78/2.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.78/2.97  % done 1940 iterations in 2.479s
% 2.78/2.97  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.78/2.97  % SZS output start Refutation
% 2.78/2.97  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.78/2.97  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 2.78/2.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.78/2.97  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 2.78/2.97  thf(a_2_4_lattice3_type, type, a_2_4_lattice3: $i > $i > $i).
% 2.78/2.97  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 2.78/2.97  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 2.78/2.97  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 2.78/2.97  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 2.78/2.97  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.78/2.97  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 2.78/2.97  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 2.78/2.97  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 2.78/2.97  thf(a_2_3_lattice3_type, type, a_2_3_lattice3: $i > $i > $i).
% 2.78/2.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.78/2.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.78/2.97  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 2.78/2.97  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 2.78/2.97  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 2.78/2.97  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 2.78/2.97  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.78/2.97  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 2.78/2.97  thf(sk_A_type, type, sk_A: $i).
% 2.78/2.97  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 2.78/2.97  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 2.78/2.97  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 2.78/2.97  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 2.78/2.97  thf(dt_k15_lattice3, axiom,
% 2.78/2.97    (![A:$i,B:$i]:
% 2.78/2.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 2.78/2.97       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 2.78/2.97  thf('0', plain,
% 2.78/2.97      (![X19 : $i, X20 : $i]:
% 2.78/2.97         (~ (l3_lattices @ X19)
% 2.78/2.97          | (v2_struct_0 @ X19)
% 2.78/2.97          | (m1_subset_1 @ (k15_lattice3 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 2.78/2.97      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.78/2.97  thf(d13_lattices, axiom,
% 2.78/2.97    (![A:$i]:
% 2.78/2.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 2.78/2.97       ( ( v13_lattices @ A ) <=>
% 2.78/2.97         ( ?[B:$i]:
% 2.78/2.97           ( ( ![C:$i]:
% 2.78/2.97               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.78/2.97                 ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 2.78/2.97                   ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) & 
% 2.78/2.97             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 2.78/2.97  thf('1', plain,
% 2.78/2.97      (![X13 : $i, X14 : $i]:
% 2.78/2.97         ((m1_subset_1 @ (sk_C_1 @ X13 @ X14) @ (u1_struct_0 @ X14))
% 2.78/2.97          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 2.78/2.97          | (v13_lattices @ X14)
% 2.78/2.97          | ~ (l1_lattices @ X14)
% 2.78/2.97          | (v2_struct_0 @ X14))),
% 2.78/2.97      inference('cnf', [status(esa)], [d13_lattices])).
% 2.78/2.97  thf('2', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         ((v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | (v13_lattices @ X0)
% 2.78/2.97          | (m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.78/2.97             (u1_struct_0 @ X0)))),
% 2.78/2.97      inference('sup-', [status(thm)], ['0', '1'])).
% 2.78/2.97  thf('3', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         ((m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.78/2.97           (u1_struct_0 @ X0))
% 2.78/2.97          | (v13_lattices @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0))),
% 2.78/2.97      inference('simplify', [status(thm)], ['2'])).
% 2.78/2.97  thf(t45_lattice3, axiom,
% 2.78/2.97    (![A:$i]:
% 2.78/2.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.78/2.97         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.78/2.97       ( ![B:$i]:
% 2.78/2.97         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.78/2.97           ( ( ( B ) = ( k15_lattice3 @ A @ ( a_2_3_lattice3 @ A @ B ) ) ) & 
% 2.78/2.97             ( ( B ) = ( k16_lattice3 @ A @ ( a_2_4_lattice3 @ A @ B ) ) ) ) ) ) ))).
% 2.78/2.97  thf('4', plain,
% 2.78/2.97      (![X21 : $i, X22 : $i]:
% 2.78/2.97         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 2.78/2.97          | ((X21) = (k15_lattice3 @ X22 @ (a_2_3_lattice3 @ X22 @ X21)))
% 2.78/2.97          | ~ (l3_lattices @ X22)
% 2.78/2.97          | ~ (v4_lattice3 @ X22)
% 2.78/2.97          | ~ (v10_lattices @ X22)
% 2.78/2.97          | (v2_struct_0 @ X22))),
% 2.78/2.97      inference('cnf', [status(esa)], [t45_lattice3])).
% 2.78/2.97  thf('5', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         ((v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | (v13_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ~ (v10_lattices @ X0)
% 2.78/2.97          | ~ (v4_lattice3 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | ((sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)
% 2.78/2.97              = (k15_lattice3 @ X0 @ 
% 2.78/2.97                 (a_2_3_lattice3 @ X0 @ 
% 2.78/2.97                  (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)))))),
% 2.78/2.97      inference('sup-', [status(thm)], ['3', '4'])).
% 2.78/2.97  thf('6', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         (((sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)
% 2.78/2.97            = (k15_lattice3 @ X0 @ 
% 2.78/2.97               (a_2_3_lattice3 @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))))
% 2.78/2.97          | ~ (v4_lattice3 @ X0)
% 2.78/2.97          | ~ (v10_lattices @ X0)
% 2.78/2.97          | (v13_lattices @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0))),
% 2.78/2.97      inference('simplify', [status(thm)], ['5'])).
% 2.78/2.97  thf('7', plain,
% 2.78/2.97      (![X19 : $i, X20 : $i]:
% 2.78/2.97         (~ (l3_lattices @ X19)
% 2.78/2.97          | (v2_struct_0 @ X19)
% 2.78/2.97          | (m1_subset_1 @ (k15_lattice3 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 2.78/2.97      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.78/2.97  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.78/2.97  thf('8', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.78/2.97      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.78/2.97  thf(t46_lattice3, axiom,
% 2.78/2.97    (![A:$i]:
% 2.78/2.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.78/2.97         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.78/2.97       ( ![B:$i,C:$i]:
% 2.78/2.97         ( ( r1_tarski @ B @ C ) =>
% 2.78/2.97           ( ( r3_lattices @
% 2.78/2.97               A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) & 
% 2.78/2.97             ( r3_lattices @
% 2.78/2.97               A @ ( k16_lattice3 @ A @ C ) @ ( k16_lattice3 @ A @ B ) ) ) ) ) ))).
% 2.78/2.97  thf('9', plain,
% 2.78/2.97      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.78/2.97         (~ (r1_tarski @ X23 @ X24)
% 2.78/2.97          | (r3_lattices @ X25 @ (k15_lattice3 @ X25 @ X23) @ 
% 2.78/2.97             (k15_lattice3 @ X25 @ X24))
% 2.78/2.97          | ~ (l3_lattices @ X25)
% 2.78/2.97          | ~ (v4_lattice3 @ X25)
% 2.78/2.97          | ~ (v10_lattices @ X25)
% 2.78/2.97          | (v2_struct_0 @ X25))),
% 2.78/2.97      inference('cnf', [status(esa)], [t46_lattice3])).
% 2.78/2.97  thf('10', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         ((v2_struct_0 @ X1)
% 2.78/2.97          | ~ (v10_lattices @ X1)
% 2.78/2.97          | ~ (v4_lattice3 @ X1)
% 2.78/2.97          | ~ (l3_lattices @ X1)
% 2.78/2.97          | (r3_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 2.78/2.97             (k15_lattice3 @ X1 @ X0)))),
% 2.78/2.97      inference('sup-', [status(thm)], ['8', '9'])).
% 2.78/2.97  thf('11', plain,
% 2.78/2.97      (![X19 : $i, X20 : $i]:
% 2.78/2.97         (~ (l3_lattices @ X19)
% 2.78/2.97          | (v2_struct_0 @ X19)
% 2.78/2.97          | (m1_subset_1 @ (k15_lattice3 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 2.78/2.97      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.78/2.97  thf('12', plain,
% 2.78/2.97      (![X19 : $i, X20 : $i]:
% 2.78/2.97         (~ (l3_lattices @ X19)
% 2.78/2.97          | (v2_struct_0 @ X19)
% 2.78/2.97          | (m1_subset_1 @ (k15_lattice3 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 2.78/2.97      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.78/2.97  thf(redefinition_r3_lattices, axiom,
% 2.78/2.97    (![A:$i,B:$i,C:$i]:
% 2.78/2.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 2.78/2.97         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 2.78/2.97         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 2.78/2.97         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 2.78/2.97       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 2.78/2.97  thf('13', plain,
% 2.78/2.97      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.78/2.97         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 2.78/2.97          | ~ (l3_lattices @ X8)
% 2.78/2.97          | ~ (v9_lattices @ X8)
% 2.78/2.97          | ~ (v8_lattices @ X8)
% 2.78/2.97          | ~ (v6_lattices @ X8)
% 2.78/2.97          | (v2_struct_0 @ X8)
% 2.78/2.97          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 2.78/2.97          | (r1_lattices @ X8 @ X7 @ X9)
% 2.78/2.97          | ~ (r3_lattices @ X8 @ X7 @ X9))),
% 2.78/2.97      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 2.78/2.97  thf('14', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.78/2.97         ((v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.78/2.97          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.78/2.97          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ~ (v6_lattices @ X0)
% 2.78/2.97          | ~ (v8_lattices @ X0)
% 2.78/2.97          | ~ (v9_lattices @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0))),
% 2.78/2.97      inference('sup-', [status(thm)], ['12', '13'])).
% 2.78/2.97  thf('15', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.78/2.97         (~ (v9_lattices @ X0)
% 2.78/2.97          | ~ (v8_lattices @ X0)
% 2.78/2.97          | ~ (v6_lattices @ X0)
% 2.78/2.97          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.78/2.97          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.78/2.97          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0))),
% 2.78/2.97      inference('simplify', [status(thm)], ['14'])).
% 2.78/2.97  thf('16', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.78/2.97         ((v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.78/2.97               (k15_lattice3 @ X0 @ X1))
% 2.78/2.97          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.78/2.97             (k15_lattice3 @ X0 @ X1))
% 2.78/2.97          | ~ (v6_lattices @ X0)
% 2.78/2.97          | ~ (v8_lattices @ X0)
% 2.78/2.97          | ~ (v9_lattices @ X0))),
% 2.78/2.97      inference('sup-', [status(thm)], ['11', '15'])).
% 2.78/2.97  thf('17', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.78/2.97         (~ (v9_lattices @ X0)
% 2.78/2.97          | ~ (v8_lattices @ X0)
% 2.78/2.97          | ~ (v6_lattices @ X0)
% 2.78/2.97          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.78/2.97             (k15_lattice3 @ X0 @ X1))
% 2.78/2.97          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.78/2.97               (k15_lattice3 @ X0 @ X1))
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0))),
% 2.78/2.97      inference('simplify', [status(thm)], ['16'])).
% 2.78/2.97  thf('18', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         (~ (l3_lattices @ X1)
% 2.78/2.97          | ~ (v4_lattice3 @ X1)
% 2.78/2.97          | ~ (v10_lattices @ X1)
% 2.78/2.97          | (v2_struct_0 @ X1)
% 2.78/2.97          | (v2_struct_0 @ X1)
% 2.78/2.97          | ~ (l3_lattices @ X1)
% 2.78/2.97          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 2.78/2.97             (k15_lattice3 @ X1 @ X0))
% 2.78/2.97          | ~ (v6_lattices @ X1)
% 2.78/2.97          | ~ (v8_lattices @ X1)
% 2.78/2.97          | ~ (v9_lattices @ X1))),
% 2.78/2.97      inference('sup-', [status(thm)], ['10', '17'])).
% 2.78/2.97  thf('19', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         (~ (v9_lattices @ X1)
% 2.78/2.97          | ~ (v8_lattices @ X1)
% 2.78/2.97          | ~ (v6_lattices @ X1)
% 2.78/2.97          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 2.78/2.97             (k15_lattice3 @ X1 @ X0))
% 2.78/2.97          | (v2_struct_0 @ X1)
% 2.78/2.97          | ~ (v10_lattices @ X1)
% 2.78/2.97          | ~ (v4_lattice3 @ X1)
% 2.78/2.97          | ~ (l3_lattices @ X1))),
% 2.78/2.97      inference('simplify', [status(thm)], ['18'])).
% 2.78/2.97  thf('20', plain,
% 2.78/2.97      (![X19 : $i, X20 : $i]:
% 2.78/2.97         (~ (l3_lattices @ X19)
% 2.78/2.97          | (v2_struct_0 @ X19)
% 2.78/2.97          | (m1_subset_1 @ (k15_lattice3 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 2.78/2.97      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.78/2.97  thf(t21_lattices, axiom,
% 2.78/2.97    (![A:$i]:
% 2.78/2.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 2.78/2.97         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 2.78/2.97       ( ![B:$i]:
% 2.78/2.97         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.78/2.97           ( ![C:$i]:
% 2.78/2.97             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.78/2.97               ( ( r1_lattices @ A @ B @ C ) <=>
% 2.78/2.97                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 2.78/2.97  thf('21', plain,
% 2.78/2.97      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.78/2.97         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 2.78/2.97          | ~ (r1_lattices @ X11 @ X10 @ X12)
% 2.78/2.97          | ((k2_lattices @ X11 @ X10 @ X12) = (X10))
% 2.78/2.97          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 2.78/2.97          | ~ (l3_lattices @ X11)
% 2.78/2.97          | ~ (v9_lattices @ X11)
% 2.78/2.97          | ~ (v8_lattices @ X11)
% 2.78/2.97          | (v2_struct_0 @ X11))),
% 2.78/2.97      inference('cnf', [status(esa)], [t21_lattices])).
% 2.78/2.97  thf('22', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.78/2.97         ((v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ~ (v8_lattices @ X0)
% 2.78/2.97          | ~ (v9_lattices @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.78/2.97          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.78/2.97              = (k15_lattice3 @ X0 @ X1))
% 2.78/2.97          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 2.78/2.97      inference('sup-', [status(thm)], ['20', '21'])).
% 2.78/2.97  thf('23', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.78/2.97         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.78/2.97          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.78/2.97              = (k15_lattice3 @ X0 @ X1))
% 2.78/2.97          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.78/2.97          | ~ (v9_lattices @ X0)
% 2.78/2.97          | ~ (v8_lattices @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0))),
% 2.78/2.97      inference('simplify', [status(thm)], ['22'])).
% 2.78/2.97  thf('24', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         (~ (l3_lattices @ X1)
% 2.78/2.97          | ~ (v4_lattice3 @ X1)
% 2.78/2.97          | ~ (v10_lattices @ X1)
% 2.78/2.97          | (v2_struct_0 @ X1)
% 2.78/2.97          | ~ (v6_lattices @ X1)
% 2.78/2.97          | ~ (v8_lattices @ X1)
% 2.78/2.97          | ~ (v9_lattices @ X1)
% 2.78/2.97          | (v2_struct_0 @ X1)
% 2.78/2.97          | ~ (l3_lattices @ X1)
% 2.78/2.97          | ~ (v8_lattices @ X1)
% 2.78/2.97          | ~ (v9_lattices @ X1)
% 2.78/2.97          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 2.78/2.97          | ((k2_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 2.78/2.97              (k15_lattice3 @ X1 @ X0)) = (k15_lattice3 @ X1 @ k1_xboole_0)))),
% 2.78/2.97      inference('sup-', [status(thm)], ['19', '23'])).
% 2.78/2.97  thf('25', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         (((k2_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 2.78/2.97            (k15_lattice3 @ X1 @ X0)) = (k15_lattice3 @ X1 @ k1_xboole_0))
% 2.78/2.97          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 2.78/2.97          | ~ (v9_lattices @ X1)
% 2.78/2.97          | ~ (v8_lattices @ X1)
% 2.78/2.97          | ~ (v6_lattices @ X1)
% 2.78/2.97          | (v2_struct_0 @ X1)
% 2.78/2.97          | ~ (v10_lattices @ X1)
% 2.78/2.97          | ~ (v4_lattice3 @ X1)
% 2.78/2.97          | ~ (l3_lattices @ X1))),
% 2.78/2.97      inference('simplify', [status(thm)], ['24'])).
% 2.78/2.97  thf('26', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         ((v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | ~ (v4_lattice3 @ X0)
% 2.78/2.97          | ~ (v10_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ~ (v6_lattices @ X0)
% 2.78/2.97          | ~ (v8_lattices @ X0)
% 2.78/2.97          | ~ (v9_lattices @ X0)
% 2.78/2.97          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.78/2.97              (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.78/2.97      inference('sup-', [status(thm)], ['7', '25'])).
% 2.78/2.97  thf('27', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.78/2.97            (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.78/2.97          | ~ (v9_lattices @ X0)
% 2.78/2.97          | ~ (v8_lattices @ X0)
% 2.78/2.97          | ~ (v6_lattices @ X0)
% 2.78/2.97          | ~ (v10_lattices @ X0)
% 2.78/2.97          | ~ (v4_lattice3 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0))),
% 2.78/2.97      inference('simplify', [status(thm)], ['26'])).
% 2.78/2.97  thf('28', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.78/2.97            (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.78/2.97            = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | (v13_lattices @ X0)
% 2.78/2.97          | ~ (v10_lattices @ X0)
% 2.78/2.97          | ~ (v4_lattice3 @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | ~ (v4_lattice3 @ X0)
% 2.78/2.97          | ~ (v10_lattices @ X0)
% 2.78/2.97          | ~ (v6_lattices @ X0)
% 2.78/2.97          | ~ (v8_lattices @ X0)
% 2.78/2.97          | ~ (v9_lattices @ X0))),
% 2.78/2.97      inference('sup+', [status(thm)], ['6', '27'])).
% 2.78/2.97  thf('29', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         (~ (v9_lattices @ X0)
% 2.78/2.97          | ~ (v8_lattices @ X0)
% 2.78/2.97          | ~ (v6_lattices @ X0)
% 2.78/2.97          | ~ (v4_lattice3 @ X0)
% 2.78/2.97          | ~ (v10_lattices @ X0)
% 2.78/2.97          | (v13_lattices @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.78/2.97              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.78/2.97              = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.78/2.97      inference('simplify', [status(thm)], ['28'])).
% 2.78/2.97  thf('30', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         (((sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)
% 2.78/2.97            = (k15_lattice3 @ X0 @ 
% 2.78/2.97               (a_2_3_lattice3 @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))))
% 2.78/2.97          | ~ (v4_lattice3 @ X0)
% 2.78/2.97          | ~ (v10_lattices @ X0)
% 2.78/2.97          | (v13_lattices @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0))),
% 2.78/2.97      inference('simplify', [status(thm)], ['5'])).
% 2.78/2.97  thf('31', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.78/2.97            (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.78/2.97          | ~ (v9_lattices @ X0)
% 2.78/2.97          | ~ (v8_lattices @ X0)
% 2.78/2.97          | ~ (v6_lattices @ X0)
% 2.78/2.97          | ~ (v10_lattices @ X0)
% 2.78/2.97          | ~ (v4_lattice3 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0))),
% 2.78/2.97      inference('simplify', [status(thm)], ['26'])).
% 2.78/2.97  thf('32', plain,
% 2.78/2.97      (![X19 : $i, X20 : $i]:
% 2.78/2.97         (~ (l3_lattices @ X19)
% 2.78/2.97          | (v2_struct_0 @ X19)
% 2.78/2.97          | (m1_subset_1 @ (k15_lattice3 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 2.78/2.97      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.78/2.97  thf('33', plain,
% 2.78/2.97      (![X19 : $i, X20 : $i]:
% 2.78/2.97         (~ (l3_lattices @ X19)
% 2.78/2.97          | (v2_struct_0 @ X19)
% 2.78/2.97          | (m1_subset_1 @ (k15_lattice3 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 2.78/2.97      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.78/2.97  thf(d6_lattices, axiom,
% 2.78/2.97    (![A:$i]:
% 2.78/2.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 2.78/2.97       ( ( v6_lattices @ A ) <=>
% 2.78/2.97         ( ![B:$i]:
% 2.78/2.97           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.78/2.97             ( ![C:$i]:
% 2.78/2.97               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.78/2.97                 ( ( k2_lattices @ A @ B @ C ) = ( k2_lattices @ A @ C @ B ) ) ) ) ) ) ) ))).
% 2.78/2.97  thf('34', plain,
% 2.78/2.97      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.78/2.97         (~ (v6_lattices @ X16)
% 2.78/2.97          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 2.78/2.97          | ((k2_lattices @ X16 @ X18 @ X17) = (k2_lattices @ X16 @ X17 @ X18))
% 2.78/2.97          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X16))
% 2.78/2.97          | ~ (l1_lattices @ X16)
% 2.78/2.97          | (v2_struct_0 @ X16))),
% 2.78/2.97      inference('cnf', [status(esa)], [d6_lattices])).
% 2.78/2.97  thf('35', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.78/2.97         ((v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.78/2.97          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 2.78/2.97              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 2.78/2.97          | ~ (v6_lattices @ X0))),
% 2.78/2.97      inference('sup-', [status(thm)], ['33', '34'])).
% 2.78/2.97  thf('36', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.78/2.97         (~ (v6_lattices @ X0)
% 2.78/2.97          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 2.78/2.97              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 2.78/2.97          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0))),
% 2.78/2.97      inference('simplify', [status(thm)], ['35'])).
% 2.78/2.97  thf('37', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.78/2.97         ((v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.78/2.97              (k15_lattice3 @ X0 @ X2))
% 2.78/2.97              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.78/2.97                 (k15_lattice3 @ X0 @ X1)))
% 2.78/2.97          | ~ (v6_lattices @ X0))),
% 2.78/2.97      inference('sup-', [status(thm)], ['32', '36'])).
% 2.78/2.97  thf('38', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.78/2.97         (~ (v6_lattices @ X0)
% 2.78/2.97          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.78/2.97              (k15_lattice3 @ X0 @ X2))
% 2.78/2.97              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.78/2.97                 (k15_lattice3 @ X0 @ X1)))
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0))),
% 2.78/2.97      inference('simplify', [status(thm)], ['37'])).
% 2.78/2.97  thf('39', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.78/2.97            = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.78/2.97               (k15_lattice3 @ X0 @ k1_xboole_0)))
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | ~ (v4_lattice3 @ X0)
% 2.78/2.97          | ~ (v10_lattices @ X0)
% 2.78/2.97          | ~ (v6_lattices @ X0)
% 2.78/2.97          | ~ (v8_lattices @ X0)
% 2.78/2.97          | ~ (v9_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | ~ (v6_lattices @ X0))),
% 2.78/2.97      inference('sup+', [status(thm)], ['31', '38'])).
% 2.78/2.97  thf('40', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         (~ (l1_lattices @ X0)
% 2.78/2.97          | ~ (v9_lattices @ X0)
% 2.78/2.97          | ~ (v8_lattices @ X0)
% 2.78/2.97          | ~ (v6_lattices @ X0)
% 2.78/2.97          | ~ (v10_lattices @ X0)
% 2.78/2.97          | ~ (v4_lattice3 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.78/2.97              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.78/2.97                 (k15_lattice3 @ X0 @ k1_xboole_0))))),
% 2.78/2.97      inference('simplify', [status(thm)], ['39'])).
% 2.78/2.97  thf('41', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.78/2.97            = (k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.78/2.97               (k15_lattice3 @ X0 @ k1_xboole_0)))
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | (v13_lattices @ X0)
% 2.78/2.97          | ~ (v10_lattices @ X0)
% 2.78/2.97          | ~ (v4_lattice3 @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | ~ (v4_lattice3 @ X0)
% 2.78/2.97          | ~ (v10_lattices @ X0)
% 2.78/2.97          | ~ (v6_lattices @ X0)
% 2.78/2.97          | ~ (v8_lattices @ X0)
% 2.78/2.97          | ~ (v9_lattices @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0))),
% 2.78/2.97      inference('sup+', [status(thm)], ['30', '40'])).
% 2.78/2.97  thf('42', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         (~ (v9_lattices @ X0)
% 2.78/2.97          | ~ (v8_lattices @ X0)
% 2.78/2.97          | ~ (v6_lattices @ X0)
% 2.78/2.97          | ~ (v4_lattice3 @ X0)
% 2.78/2.97          | ~ (v10_lattices @ X0)
% 2.78/2.97          | (v13_lattices @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.78/2.97              = (k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.78/2.97                 (k15_lattice3 @ X0 @ k1_xboole_0))))),
% 2.78/2.97      inference('simplify', [status(thm)], ['41'])).
% 2.78/2.97  thf('43', plain,
% 2.78/2.97      (![X19 : $i, X20 : $i]:
% 2.78/2.97         (~ (l3_lattices @ X19)
% 2.78/2.97          | (v2_struct_0 @ X19)
% 2.78/2.97          | (m1_subset_1 @ (k15_lattice3 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 2.78/2.97      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.78/2.97  thf('44', plain,
% 2.78/2.97      (![X13 : $i, X14 : $i]:
% 2.78/2.97         (((k2_lattices @ X14 @ (sk_C_1 @ X13 @ X14) @ X13) != (X13))
% 2.78/2.97          | ((k2_lattices @ X14 @ X13 @ (sk_C_1 @ X13 @ X14)) != (X13))
% 2.78/2.97          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 2.78/2.97          | (v13_lattices @ X14)
% 2.78/2.97          | ~ (l1_lattices @ X14)
% 2.78/2.97          | (v2_struct_0 @ X14))),
% 2.78/2.97      inference('cnf', [status(esa)], [d13_lattices])).
% 2.78/2.97  thf('45', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         ((v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | (v13_lattices @ X0)
% 2.78/2.97          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.78/2.97              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.78/2.97              != (k15_lattice3 @ X0 @ X1))
% 2.78/2.97          | ((k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.78/2.97              (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1)))),
% 2.78/2.97      inference('sup-', [status(thm)], ['43', '44'])).
% 2.78/2.97  thf('46', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         (((k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.78/2.97            (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1))
% 2.78/2.97          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.78/2.97              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.78/2.97              != (k15_lattice3 @ X0 @ X1))
% 2.78/2.97          | (v13_lattices @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0))),
% 2.78/2.97      inference('simplify', [status(thm)], ['45'])).
% 2.78/2.97  thf('47', plain,
% 2.78/2.97      (![X0 : $i]:
% 2.78/2.97         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.78/2.97            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | (v13_lattices @ X0)
% 2.78/2.97          | ~ (v10_lattices @ X0)
% 2.78/2.97          | ~ (v4_lattice3 @ X0)
% 2.78/2.97          | ~ (v6_lattices @ X0)
% 2.78/2.97          | ~ (v8_lattices @ X0)
% 2.78/2.97          | ~ (v9_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | (v13_lattices @ X0)
% 2.78/2.97          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.78/2.97              (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 2.78/2.97              != (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.78/2.97      inference('sup-', [status(thm)], ['42', '46'])).
% 2.78/2.97  thf('48', plain,
% 2.78/2.97      (![X0 : $i]:
% 2.78/2.97         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.78/2.97            (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 2.78/2.97            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.78/2.97          | ~ (v9_lattices @ X0)
% 2.78/2.97          | ~ (v8_lattices @ X0)
% 2.78/2.97          | ~ (v6_lattices @ X0)
% 2.78/2.97          | ~ (v4_lattice3 @ X0)
% 2.78/2.97          | ~ (v10_lattices @ X0)
% 2.78/2.97          | (v13_lattices @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0))),
% 2.78/2.97      inference('simplify', [status(thm)], ['47'])).
% 2.78/2.97  thf('49', plain,
% 2.78/2.97      (![X0 : $i]:
% 2.78/2.97         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.78/2.97            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | (v13_lattices @ X0)
% 2.78/2.97          | ~ (v10_lattices @ X0)
% 2.78/2.97          | ~ (v4_lattice3 @ X0)
% 2.78/2.97          | ~ (v6_lattices @ X0)
% 2.78/2.97          | ~ (v8_lattices @ X0)
% 2.78/2.97          | ~ (v9_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | (v13_lattices @ X0)
% 2.78/2.97          | ~ (v10_lattices @ X0)
% 2.78/2.97          | ~ (v4_lattice3 @ X0)
% 2.78/2.97          | ~ (v6_lattices @ X0)
% 2.78/2.97          | ~ (v8_lattices @ X0)
% 2.78/2.97          | ~ (v9_lattices @ X0))),
% 2.78/2.97      inference('sup-', [status(thm)], ['29', '48'])).
% 2.78/2.97  thf('50', plain,
% 2.78/2.97      (![X0 : $i]:
% 2.78/2.97         (~ (v9_lattices @ X0)
% 2.78/2.97          | ~ (v8_lattices @ X0)
% 2.78/2.97          | ~ (v6_lattices @ X0)
% 2.78/2.97          | ~ (v4_lattice3 @ X0)
% 2.78/2.97          | ~ (v10_lattices @ X0)
% 2.78/2.97          | (v13_lattices @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0))),
% 2.78/2.97      inference('simplify', [status(thm)], ['49'])).
% 2.78/2.97  thf(t50_lattice3, conjecture,
% 2.78/2.97    (![A:$i]:
% 2.78/2.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.78/2.97         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.78/2.97       ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.78/2.97         ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 2.78/2.97         ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ))).
% 2.78/2.97  thf(zf_stmt_0, negated_conjecture,
% 2.78/2.97    (~( ![A:$i]:
% 2.78/2.97        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.78/2.97            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.78/2.97          ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.78/2.97            ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 2.78/2.97            ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ) )),
% 2.78/2.97    inference('cnf.neg', [status(esa)], [t50_lattice3])).
% 2.78/2.97  thf('51', plain, (~ (v2_struct_0 @ sk_A)),
% 2.78/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.97  thf('52', plain,
% 2.78/2.97      ((~ (l3_lattices @ sk_A)
% 2.78/2.97        | ~ (l1_lattices @ sk_A)
% 2.78/2.97        | (v13_lattices @ sk_A)
% 2.78/2.97        | ~ (v10_lattices @ sk_A)
% 2.78/2.97        | ~ (v4_lattice3 @ sk_A)
% 2.78/2.97        | ~ (v6_lattices @ sk_A)
% 2.78/2.97        | ~ (v8_lattices @ sk_A)
% 2.78/2.97        | ~ (v9_lattices @ sk_A))),
% 2.78/2.97      inference('sup-', [status(thm)], ['50', '51'])).
% 2.78/2.97  thf('53', plain, ((l3_lattices @ sk_A)),
% 2.78/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.97  thf('54', plain, ((l3_lattices @ sk_A)),
% 2.78/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.97  thf(dt_l3_lattices, axiom,
% 2.78/2.97    (![A:$i]:
% 2.78/2.97     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 2.78/2.97  thf('55', plain, (![X6 : $i]: ((l1_lattices @ X6) | ~ (l3_lattices @ X6))),
% 2.78/2.97      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 2.78/2.97  thf('56', plain, ((l1_lattices @ sk_A)),
% 2.78/2.97      inference('sup-', [status(thm)], ['54', '55'])).
% 2.78/2.97  thf('57', plain, ((v10_lattices @ sk_A)),
% 2.78/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.97  thf('58', plain, ((v4_lattice3 @ sk_A)),
% 2.78/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.97  thf(cc1_lattices, axiom,
% 2.78/2.97    (![A:$i]:
% 2.78/2.97     ( ( l3_lattices @ A ) =>
% 2.78/2.97       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 2.78/2.97         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 2.78/2.97           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 2.78/2.97           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 2.78/2.97  thf('59', plain,
% 2.78/2.97      (![X1 : $i]:
% 2.78/2.97         ((v2_struct_0 @ X1)
% 2.78/2.97          | ~ (v10_lattices @ X1)
% 2.78/2.97          | (v6_lattices @ X1)
% 2.78/2.97          | ~ (l3_lattices @ X1))),
% 2.78/2.97      inference('cnf', [status(esa)], [cc1_lattices])).
% 2.78/2.97  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 2.78/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.97  thf('61', plain,
% 2.78/2.97      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 2.78/2.97      inference('sup-', [status(thm)], ['59', '60'])).
% 2.78/2.97  thf('62', plain, ((l3_lattices @ sk_A)),
% 2.78/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.97  thf('63', plain, ((v10_lattices @ sk_A)),
% 2.78/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.97  thf('64', plain, ((v6_lattices @ sk_A)),
% 2.78/2.97      inference('demod', [status(thm)], ['61', '62', '63'])).
% 2.78/2.97  thf('65', plain,
% 2.78/2.97      (![X1 : $i]:
% 2.78/2.97         ((v2_struct_0 @ X1)
% 2.78/2.97          | ~ (v10_lattices @ X1)
% 2.78/2.97          | (v8_lattices @ X1)
% 2.78/2.97          | ~ (l3_lattices @ X1))),
% 2.78/2.97      inference('cnf', [status(esa)], [cc1_lattices])).
% 2.78/2.97  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 2.78/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.97  thf('67', plain,
% 2.78/2.97      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 2.78/2.97      inference('sup-', [status(thm)], ['65', '66'])).
% 2.78/2.97  thf('68', plain, ((l3_lattices @ sk_A)),
% 2.78/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.97  thf('69', plain, ((v10_lattices @ sk_A)),
% 2.78/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.97  thf('70', plain, ((v8_lattices @ sk_A)),
% 2.78/2.97      inference('demod', [status(thm)], ['67', '68', '69'])).
% 2.78/2.97  thf('71', plain,
% 2.78/2.97      (![X1 : $i]:
% 2.78/2.97         ((v2_struct_0 @ X1)
% 2.78/2.97          | ~ (v10_lattices @ X1)
% 2.78/2.97          | (v9_lattices @ X1)
% 2.78/2.97          | ~ (l3_lattices @ X1))),
% 2.78/2.97      inference('cnf', [status(esa)], [cc1_lattices])).
% 2.78/2.97  thf('72', plain, (~ (v2_struct_0 @ sk_A)),
% 2.78/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.97  thf('73', plain,
% 2.78/2.97      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 2.78/2.97      inference('sup-', [status(thm)], ['71', '72'])).
% 2.78/2.97  thf('74', plain, ((l3_lattices @ sk_A)),
% 2.78/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.97  thf('75', plain, ((v10_lattices @ sk_A)),
% 2.78/2.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.97  thf('76', plain, ((v9_lattices @ sk_A)),
% 2.78/2.97      inference('demod', [status(thm)], ['73', '74', '75'])).
% 2.78/2.97  thf('77', plain, ((v13_lattices @ sk_A)),
% 2.78/2.97      inference('demod', [status(thm)],
% 2.78/2.97                ['52', '53', '56', '57', '58', '64', '70', '76'])).
% 2.78/2.97  thf('78', plain,
% 2.78/2.97      (![X19 : $i, X20 : $i]:
% 2.78/2.97         (~ (l3_lattices @ X19)
% 2.78/2.97          | (v2_struct_0 @ X19)
% 2.78/2.97          | (m1_subset_1 @ (k15_lattice3 @ X19 @ X20) @ (u1_struct_0 @ X19)))),
% 2.78/2.97      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.78/2.97  thf(dt_k5_lattices, axiom,
% 2.78/2.97    (![A:$i]:
% 2.78/2.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 2.78/2.97       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 2.78/2.97  thf('79', plain,
% 2.78/2.97      (![X5 : $i]:
% 2.78/2.97         ((m1_subset_1 @ (k5_lattices @ X5) @ (u1_struct_0 @ X5))
% 2.78/2.97          | ~ (l1_lattices @ X5)
% 2.78/2.97          | (v2_struct_0 @ X5))),
% 2.78/2.97      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 2.78/2.97  thf(d16_lattices, axiom,
% 2.78/2.97    (![A:$i]:
% 2.78/2.97     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 2.78/2.97       ( ( v13_lattices @ A ) =>
% 2.78/2.97         ( ![B:$i]:
% 2.78/2.97           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.78/2.97             ( ( ( B ) = ( k5_lattices @ A ) ) <=>
% 2.78/2.97               ( ![C:$i]:
% 2.78/2.97                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.78/2.97                   ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 2.78/2.97                     ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 2.78/2.97  thf('80', plain,
% 2.78/2.97      (![X2 : $i, X3 : $i, X4 : $i]:
% 2.78/2.97         (~ (v13_lattices @ X2)
% 2.78/2.97          | ~ (m1_subset_1 @ X3 @ (u1_struct_0 @ X2))
% 2.78/2.97          | ((X3) != (k5_lattices @ X2))
% 2.78/2.97          | ((k2_lattices @ X2 @ X4 @ X3) = (X3))
% 2.78/2.97          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 2.78/2.97          | ~ (l1_lattices @ X2)
% 2.78/2.97          | (v2_struct_0 @ X2))),
% 2.78/2.97      inference('cnf', [status(esa)], [d16_lattices])).
% 2.78/2.97  thf('81', plain,
% 2.78/2.97      (![X2 : $i, X4 : $i]:
% 2.78/2.97         ((v2_struct_0 @ X2)
% 2.78/2.97          | ~ (l1_lattices @ X2)
% 2.78/2.97          | ~ (m1_subset_1 @ X4 @ (u1_struct_0 @ X2))
% 2.78/2.97          | ((k2_lattices @ X2 @ X4 @ (k5_lattices @ X2)) = (k5_lattices @ X2))
% 2.78/2.97          | ~ (m1_subset_1 @ (k5_lattices @ X2) @ (u1_struct_0 @ X2))
% 2.78/2.97          | ~ (v13_lattices @ X2))),
% 2.78/2.97      inference('simplify', [status(thm)], ['80'])).
% 2.78/2.97  thf('82', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         ((v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | ~ (v13_lattices @ X0)
% 2.78/2.97          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 2.78/2.97          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0))),
% 2.78/2.97      inference('sup-', [status(thm)], ['79', '81'])).
% 2.78/2.97  thf('83', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 2.78/2.97          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 2.78/2.97          | ~ (v13_lattices @ X0)
% 2.78/2.97          | ~ (l1_lattices @ X0)
% 2.78/2.97          | (v2_struct_0 @ X0))),
% 2.78/2.97      inference('simplify', [status(thm)], ['82'])).
% 2.78/2.97  thf('84', plain,
% 2.78/2.97      (![X0 : $i, X1 : $i]:
% 2.78/2.97         ((v2_struct_0 @ X0)
% 2.78/2.97          | ~ (l3_lattices @ X0)
% 2.78/2.98          | (v2_struct_0 @ X0)
% 2.78/2.98          | ~ (l1_lattices @ X0)
% 2.78/2.98          | ~ (v13_lattices @ X0)
% 2.78/2.98          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.78/2.98              = (k5_lattices @ X0)))),
% 2.78/2.98      inference('sup-', [status(thm)], ['78', '83'])).
% 2.78/2.98  thf('85', plain,
% 2.78/2.98      (![X0 : $i, X1 : $i]:
% 2.78/2.98         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.78/2.98            = (k5_lattices @ X0))
% 2.78/2.98          | ~ (v13_lattices @ X0)
% 2.78/2.98          | ~ (l1_lattices @ X0)
% 2.78/2.98          | ~ (l3_lattices @ X0)
% 2.78/2.98          | (v2_struct_0 @ X0))),
% 2.78/2.98      inference('simplify', [status(thm)], ['84'])).
% 2.78/2.98  thf('86', plain,
% 2.78/2.98      (![X5 : $i]:
% 2.78/2.98         ((m1_subset_1 @ (k5_lattices @ X5) @ (u1_struct_0 @ X5))
% 2.78/2.98          | ~ (l1_lattices @ X5)
% 2.78/2.98          | (v2_struct_0 @ X5))),
% 2.78/2.98      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 2.78/2.98  thf('87', plain,
% 2.78/2.98      (![X5 : $i]:
% 2.78/2.98         ((m1_subset_1 @ (k5_lattices @ X5) @ (u1_struct_0 @ X5))
% 2.78/2.98          | ~ (l1_lattices @ X5)
% 2.78/2.98          | (v2_struct_0 @ X5))),
% 2.78/2.98      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 2.78/2.98  thf('88', plain,
% 2.78/2.98      (![X21 : $i, X22 : $i]:
% 2.78/2.98         (~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X22))
% 2.78/2.98          | ((X21) = (k15_lattice3 @ X22 @ (a_2_3_lattice3 @ X22 @ X21)))
% 2.78/2.98          | ~ (l3_lattices @ X22)
% 2.78/2.98          | ~ (v4_lattice3 @ X22)
% 2.78/2.98          | ~ (v10_lattices @ X22)
% 2.78/2.98          | (v2_struct_0 @ X22))),
% 2.78/2.98      inference('cnf', [status(esa)], [t45_lattice3])).
% 2.78/2.98  thf('89', plain,
% 2.78/2.98      (![X0 : $i]:
% 2.78/2.98         ((v2_struct_0 @ X0)
% 2.78/2.98          | ~ (l1_lattices @ X0)
% 2.78/2.98          | (v2_struct_0 @ X0)
% 2.78/2.98          | ~ (v10_lattices @ X0)
% 2.78/2.98          | ~ (v4_lattice3 @ X0)
% 2.78/2.98          | ~ (l3_lattices @ X0)
% 2.78/2.98          | ((k5_lattices @ X0)
% 2.78/2.98              = (k15_lattice3 @ X0 @ (a_2_3_lattice3 @ X0 @ (k5_lattices @ X0)))))),
% 2.78/2.98      inference('sup-', [status(thm)], ['87', '88'])).
% 2.78/2.98  thf('90', plain,
% 2.78/2.98      (![X0 : $i]:
% 2.78/2.98         (((k5_lattices @ X0)
% 2.78/2.98            = (k15_lattice3 @ X0 @ (a_2_3_lattice3 @ X0 @ (k5_lattices @ X0))))
% 2.78/2.98          | ~ (l3_lattices @ X0)
% 2.78/2.98          | ~ (v4_lattice3 @ X0)
% 2.78/2.98          | ~ (v10_lattices @ X0)
% 2.78/2.98          | ~ (l1_lattices @ X0)
% 2.78/2.98          | (v2_struct_0 @ X0))),
% 2.78/2.98      inference('simplify', [status(thm)], ['89'])).
% 2.78/2.98  thf('91', plain,
% 2.78/2.98      (![X0 : $i, X1 : $i]:
% 2.78/2.98         ((v2_struct_0 @ X1)
% 2.78/2.98          | ~ (v10_lattices @ X1)
% 2.78/2.98          | ~ (v4_lattice3 @ X1)
% 2.78/2.98          | ~ (l3_lattices @ X1)
% 2.78/2.98          | (r3_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 2.78/2.98             (k15_lattice3 @ X1 @ X0)))),
% 2.78/2.98      inference('sup-', [status(thm)], ['8', '9'])).
% 2.78/2.98  thf('92', plain,
% 2.78/2.98      (![X0 : $i]:
% 2.78/2.98         ((r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.78/2.98           (k5_lattices @ X0))
% 2.78/2.98          | (v2_struct_0 @ X0)
% 2.78/2.98          | ~ (l1_lattices @ X0)
% 2.78/2.98          | ~ (v10_lattices @ X0)
% 2.78/2.98          | ~ (v4_lattice3 @ X0)
% 2.78/2.98          | ~ (l3_lattices @ X0)
% 2.78/2.98          | ~ (l3_lattices @ X0)
% 2.78/2.98          | ~ (v4_lattice3 @ X0)
% 2.78/2.98          | ~ (v10_lattices @ X0)
% 2.78/2.98          | (v2_struct_0 @ X0))),
% 2.78/2.98      inference('sup+', [status(thm)], ['90', '91'])).
% 2.78/2.98  thf('93', plain,
% 2.78/2.98      (![X0 : $i]:
% 2.78/2.98         (~ (l3_lattices @ X0)
% 2.78/2.98          | ~ (v4_lattice3 @ X0)
% 2.78/2.98          | ~ (v10_lattices @ X0)
% 2.78/2.98          | ~ (l1_lattices @ X0)
% 2.78/2.98          | (v2_struct_0 @ X0)
% 2.78/2.98          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.78/2.98             (k5_lattices @ X0)))),
% 2.78/2.98      inference('simplify', [status(thm)], ['92'])).
% 2.78/2.98  thf('94', plain,
% 2.78/2.98      (![X5 : $i]:
% 2.78/2.98         ((m1_subset_1 @ (k5_lattices @ X5) @ (u1_struct_0 @ X5))
% 2.78/2.98          | ~ (l1_lattices @ X5)
% 2.78/2.98          | (v2_struct_0 @ X5))),
% 2.78/2.98      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 2.78/2.98  thf('95', plain,
% 2.78/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.78/2.98         (~ (v9_lattices @ X0)
% 2.78/2.98          | ~ (v8_lattices @ X0)
% 2.78/2.98          | ~ (v6_lattices @ X0)
% 2.78/2.98          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.78/2.98          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.78/2.98          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.78/2.98          | ~ (l3_lattices @ X0)
% 2.78/2.98          | (v2_struct_0 @ X0))),
% 2.78/2.98      inference('simplify', [status(thm)], ['14'])).
% 2.78/2.98  thf('96', plain,
% 2.78/2.98      (![X0 : $i, X1 : $i]:
% 2.78/2.98         ((v2_struct_0 @ X0)
% 2.78/2.98          | ~ (l1_lattices @ X0)
% 2.78/2.98          | (v2_struct_0 @ X0)
% 2.78/2.98          | ~ (l3_lattices @ X0)
% 2.78/2.98          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.78/2.98          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.78/2.98          | ~ (v6_lattices @ X0)
% 2.78/2.98          | ~ (v8_lattices @ X0)
% 2.78/2.98          | ~ (v9_lattices @ X0))),
% 2.78/2.98      inference('sup-', [status(thm)], ['94', '95'])).
% 2.78/2.98  thf('97', plain,
% 2.78/2.98      (![X0 : $i, X1 : $i]:
% 2.78/2.98         (~ (v9_lattices @ X0)
% 2.78/2.98          | ~ (v8_lattices @ X0)
% 2.78/2.98          | ~ (v6_lattices @ X0)
% 2.78/2.98          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.78/2.98          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.78/2.98          | ~ (l3_lattices @ X0)
% 2.78/2.98          | ~ (l1_lattices @ X0)
% 2.78/2.98          | (v2_struct_0 @ X0))),
% 2.78/2.98      inference('simplify', [status(thm)], ['96'])).
% 2.78/2.98  thf('98', plain,
% 2.78/2.98      (![X0 : $i]:
% 2.78/2.98         ((v2_struct_0 @ X0)
% 2.78/2.98          | ~ (l1_lattices @ X0)
% 2.78/2.98          | ~ (v10_lattices @ X0)
% 2.78/2.98          | ~ (v4_lattice3 @ X0)
% 2.78/2.98          | ~ (l3_lattices @ X0)
% 2.78/2.98          | (v2_struct_0 @ X0)
% 2.78/2.98          | ~ (l1_lattices @ X0)
% 2.78/2.98          | ~ (l3_lattices @ X0)
% 2.78/2.98          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.78/2.98             (k5_lattices @ X0))
% 2.78/2.98          | ~ (v6_lattices @ X0)
% 2.78/2.98          | ~ (v8_lattices @ X0)
% 2.78/2.98          | ~ (v9_lattices @ X0))),
% 2.78/2.98      inference('sup-', [status(thm)], ['93', '97'])).
% 2.78/2.98  thf('99', plain,
% 2.78/2.98      (![X0 : $i]:
% 2.78/2.98         (~ (v9_lattices @ X0)
% 2.78/2.98          | ~ (v8_lattices @ X0)
% 2.78/2.98          | ~ (v6_lattices @ X0)
% 2.78/2.98          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.78/2.98             (k5_lattices @ X0))
% 2.78/2.98          | ~ (l3_lattices @ X0)
% 2.78/2.98          | ~ (v4_lattice3 @ X0)
% 2.78/2.98          | ~ (v10_lattices @ X0)
% 2.78/2.98          | ~ (l1_lattices @ X0)
% 2.78/2.98          | (v2_struct_0 @ X0))),
% 2.78/2.98      inference('simplify', [status(thm)], ['98'])).
% 2.78/2.98  thf('100', plain,
% 2.78/2.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.78/2.98         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.78/2.98          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.78/2.98              = (k15_lattice3 @ X0 @ X1))
% 2.78/2.98          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.78/2.98          | ~ (v9_lattices @ X0)
% 2.78/2.98          | ~ (v8_lattices @ X0)
% 2.78/2.98          | ~ (l3_lattices @ X0)
% 2.78/2.98          | (v2_struct_0 @ X0))),
% 2.78/2.98      inference('simplify', [status(thm)], ['22'])).
% 2.78/2.98  thf('101', plain,
% 2.78/2.98      (![X0 : $i]:
% 2.78/2.98         ((v2_struct_0 @ X0)
% 2.78/2.98          | ~ (l1_lattices @ X0)
% 2.78/2.98          | ~ (v10_lattices @ X0)
% 2.78/2.98          | ~ (v4_lattice3 @ X0)
% 2.78/2.98          | ~ (l3_lattices @ X0)
% 2.78/2.98          | ~ (v6_lattices @ X0)
% 2.78/2.98          | ~ (v8_lattices @ X0)
% 2.78/2.98          | ~ (v9_lattices @ X0)
% 2.78/2.98          | (v2_struct_0 @ X0)
% 2.78/2.98          | ~ (l3_lattices @ X0)
% 2.78/2.98          | ~ (v8_lattices @ X0)
% 2.78/2.98          | ~ (v9_lattices @ X0)
% 2.78/2.98          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 2.78/2.98          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.78/2.98              (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.78/2.98      inference('sup-', [status(thm)], ['99', '100'])).
% 2.78/2.98  thf('102', plain,
% 2.78/2.98      (![X0 : $i]:
% 2.78/2.98         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.78/2.98            (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.78/2.98          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 2.78/2.98          | ~ (v9_lattices @ X0)
% 2.78/2.98          | ~ (v8_lattices @ X0)
% 2.78/2.98          | ~ (v6_lattices @ X0)
% 2.78/2.98          | ~ (l3_lattices @ X0)
% 2.78/2.98          | ~ (v4_lattice3 @ X0)
% 2.78/2.98          | ~ (v10_lattices @ X0)
% 2.78/2.98          | ~ (l1_lattices @ X0)
% 2.78/2.98          | (v2_struct_0 @ X0))),
% 2.78/2.98      inference('simplify', [status(thm)], ['101'])).
% 2.78/2.98  thf('103', plain,
% 2.78/2.98      (![X0 : $i]:
% 2.78/2.98         ((v2_struct_0 @ X0)
% 2.78/2.98          | ~ (l1_lattices @ X0)
% 2.78/2.98          | (v2_struct_0 @ X0)
% 2.78/2.98          | ~ (l1_lattices @ X0)
% 2.78/2.98          | ~ (v10_lattices @ X0)
% 2.78/2.98          | ~ (v4_lattice3 @ X0)
% 2.78/2.98          | ~ (l3_lattices @ X0)
% 2.78/2.98          | ~ (v6_lattices @ X0)
% 2.78/2.98          | ~ (v8_lattices @ X0)
% 2.78/2.98          | ~ (v9_lattices @ X0)
% 2.78/2.98          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.78/2.98              (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.78/2.98      inference('sup-', [status(thm)], ['86', '102'])).
% 2.78/2.98  thf('104', plain,
% 2.78/2.98      (![X0 : $i]:
% 2.78/2.98         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.78/2.98            (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.78/2.98          | ~ (v9_lattices @ X0)
% 2.78/2.98          | ~ (v8_lattices @ X0)
% 2.78/2.98          | ~ (v6_lattices @ X0)
% 2.78/2.98          | ~ (l3_lattices @ X0)
% 2.78/2.98          | ~ (v4_lattice3 @ X0)
% 2.78/2.98          | ~ (v10_lattices @ X0)
% 2.78/2.98          | ~ (l1_lattices @ X0)
% 2.78/2.98          | (v2_struct_0 @ X0))),
% 2.78/2.98      inference('simplify', [status(thm)], ['103'])).
% 2.78/2.98  thf('105', plain,
% 2.78/2.98      (![X0 : $i]:
% 2.78/2.98         (((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.78/2.98          | (v2_struct_0 @ X0)
% 2.78/2.98          | ~ (l3_lattices @ X0)
% 2.78/2.98          | ~ (l1_lattices @ X0)
% 2.78/2.98          | ~ (v13_lattices @ X0)
% 2.78/2.98          | (v2_struct_0 @ X0)
% 2.78/2.98          | ~ (l1_lattices @ X0)
% 2.78/2.98          | ~ (v10_lattices @ X0)
% 2.78/2.98          | ~ (v4_lattice3 @ X0)
% 2.78/2.98          | ~ (l3_lattices @ X0)
% 2.78/2.98          | ~ (v6_lattices @ X0)
% 2.78/2.98          | ~ (v8_lattices @ X0)
% 2.78/2.98          | ~ (v9_lattices @ X0))),
% 2.78/2.98      inference('sup+', [status(thm)], ['85', '104'])).
% 2.78/2.98  thf('106', plain,
% 2.78/2.98      (![X0 : $i]:
% 2.78/2.98         (~ (v9_lattices @ X0)
% 2.78/2.98          | ~ (v8_lattices @ X0)
% 2.78/2.98          | ~ (v6_lattices @ X0)
% 2.78/2.98          | ~ (v4_lattice3 @ X0)
% 2.78/2.98          | ~ (v10_lattices @ X0)
% 2.78/2.98          | ~ (v13_lattices @ X0)
% 2.78/2.98          | ~ (l1_lattices @ X0)
% 2.78/2.98          | ~ (l3_lattices @ X0)
% 2.78/2.98          | (v2_struct_0 @ X0)
% 2.78/2.98          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.78/2.98      inference('simplify', [status(thm)], ['105'])).
% 2.78/2.98  thf('107', plain,
% 2.78/2.98      (((v2_struct_0 @ sk_A)
% 2.78/2.98        | ~ (v10_lattices @ sk_A)
% 2.78/2.98        | ~ (v13_lattices @ sk_A)
% 2.78/2.98        | ~ (l3_lattices @ sk_A)
% 2.78/2.98        | ((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 2.78/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.98  thf('108', plain,
% 2.78/2.98      ((((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))
% 2.78/2.98         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.78/2.98      inference('split', [status(esa)], ['107'])).
% 2.78/2.98  thf('109', plain,
% 2.78/2.98      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 2.78/2.98         | (v2_struct_0 @ sk_A)
% 2.78/2.98         | ~ (l3_lattices @ sk_A)
% 2.78/2.98         | ~ (l1_lattices @ sk_A)
% 2.78/2.98         | ~ (v13_lattices @ sk_A)
% 2.78/2.98         | ~ (v10_lattices @ sk_A)
% 2.78/2.98         | ~ (v4_lattice3 @ sk_A)
% 2.78/2.98         | ~ (v6_lattices @ sk_A)
% 2.78/2.98         | ~ (v8_lattices @ sk_A)
% 2.78/2.98         | ~ (v9_lattices @ sk_A)))
% 2.78/2.98         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.78/2.98      inference('sup-', [status(thm)], ['106', '108'])).
% 2.78/2.98  thf('110', plain, ((l3_lattices @ sk_A)),
% 2.78/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.98  thf('111', plain, ((l1_lattices @ sk_A)),
% 2.78/2.98      inference('sup-', [status(thm)], ['54', '55'])).
% 2.78/2.98  thf('112', plain, ((v10_lattices @ sk_A)),
% 2.78/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.98  thf('113', plain, ((v4_lattice3 @ sk_A)),
% 2.78/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.98  thf('114', plain, ((v6_lattices @ sk_A)),
% 2.78/2.98      inference('demod', [status(thm)], ['61', '62', '63'])).
% 2.78/2.98  thf('115', plain, ((v8_lattices @ sk_A)),
% 2.78/2.98      inference('demod', [status(thm)], ['67', '68', '69'])).
% 2.78/2.98  thf('116', plain, ((v9_lattices @ sk_A)),
% 2.78/2.98      inference('demod', [status(thm)], ['73', '74', '75'])).
% 2.78/2.98  thf('117', plain,
% 2.78/2.98      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 2.78/2.98         | (v2_struct_0 @ sk_A)
% 2.78/2.98         | ~ (v13_lattices @ sk_A)))
% 2.78/2.98         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.78/2.98      inference('demod', [status(thm)],
% 2.78/2.98                ['109', '110', '111', '112', '113', '114', '115', '116'])).
% 2.78/2.98  thf('118', plain,
% 2.78/2.98      (((~ (v13_lattices @ sk_A) | (v2_struct_0 @ sk_A)))
% 2.78/2.98         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.78/2.98      inference('simplify', [status(thm)], ['117'])).
% 2.78/2.98  thf('119', plain, (~ (v2_struct_0 @ sk_A)),
% 2.78/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.98  thf('120', plain,
% 2.78/2.98      ((~ (v13_lattices @ sk_A))
% 2.78/2.98         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.78/2.98      inference('clc', [status(thm)], ['118', '119'])).
% 2.78/2.98  thf('121', plain,
% 2.78/2.98      (($false)
% 2.78/2.98         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.78/2.98      inference('sup-', [status(thm)], ['77', '120'])).
% 2.78/2.98  thf('122', plain, (((v2_struct_0 @ sk_A)) <= (((v2_struct_0 @ sk_A)))),
% 2.78/2.98      inference('split', [status(esa)], ['107'])).
% 2.78/2.98  thf('123', plain, (~ (v2_struct_0 @ sk_A)),
% 2.78/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.98  thf('124', plain, (~ ((v2_struct_0 @ sk_A))),
% 2.78/2.98      inference('sup-', [status(thm)], ['122', '123'])).
% 2.78/2.98  thf('125', plain, ((l3_lattices @ sk_A)),
% 2.78/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.98  thf('126', plain, ((~ (l3_lattices @ sk_A)) <= (~ ((l3_lattices @ sk_A)))),
% 2.78/2.98      inference('split', [status(esa)], ['107'])).
% 2.78/2.98  thf('127', plain, (((l3_lattices @ sk_A))),
% 2.78/2.98      inference('sup-', [status(thm)], ['125', '126'])).
% 2.78/2.98  thf('128', plain, ((v10_lattices @ sk_A)),
% 2.78/2.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.78/2.98  thf('129', plain, ((~ (v10_lattices @ sk_A)) <= (~ ((v10_lattices @ sk_A)))),
% 2.78/2.98      inference('split', [status(esa)], ['107'])).
% 2.78/2.98  thf('130', plain, (((v10_lattices @ sk_A))),
% 2.78/2.98      inference('sup-', [status(thm)], ['128', '129'])).
% 2.78/2.98  thf('131', plain, ((v13_lattices @ sk_A)),
% 2.78/2.98      inference('demod', [status(thm)],
% 2.78/2.98                ['52', '53', '56', '57', '58', '64', '70', '76'])).
% 2.78/2.98  thf('132', plain, ((~ (v13_lattices @ sk_A)) <= (~ ((v13_lattices @ sk_A)))),
% 2.78/2.98      inference('split', [status(esa)], ['107'])).
% 2.78/2.98  thf('133', plain, (((v13_lattices @ sk_A))),
% 2.78/2.98      inference('sup-', [status(thm)], ['131', '132'])).
% 2.78/2.98  thf('134', plain,
% 2.78/2.98      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))) | 
% 2.78/2.98       ~ ((v13_lattices @ sk_A)) | ~ ((v10_lattices @ sk_A)) | 
% 2.78/2.98       ~ ((l3_lattices @ sk_A)) | ((v2_struct_0 @ sk_A))),
% 2.78/2.98      inference('split', [status(esa)], ['107'])).
% 2.78/2.98  thf('135', plain,
% 2.78/2.98      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 2.78/2.98      inference('sat_resolution*', [status(thm)],
% 2.78/2.98                ['124', '127', '130', '133', '134'])).
% 2.78/2.98  thf('136', plain, ($false),
% 2.78/2.98      inference('simpl_trail', [status(thm)], ['121', '135'])).
% 2.78/2.98  
% 2.78/2.98  % SZS output end Refutation
% 2.78/2.98  
% 2.78/2.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
