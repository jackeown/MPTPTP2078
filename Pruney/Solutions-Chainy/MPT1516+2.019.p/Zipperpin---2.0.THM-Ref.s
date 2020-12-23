%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ygswaMr6aq

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:37 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 428 expanded)
%              Number of leaves         :   39 ( 136 expanded)
%              Depth                    :   20
%              Number of atoms          : 2188 (6801 expanded)
%              Number of equality atoms :   59 ( 207 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l3_lattices @ X27 )
      | ( v2_struct_0 @ X27 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X27 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ X12 @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( v13_lattices @ X13 )
      | ~ ( l1_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf(d17_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r4_lattice3 @ A @ B @ C )
            <=> ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ D @ C )
                   => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X19 @ X15 @ X16 ) @ X19 )
      | ( r4_lattice3 @ X16 @ X15 @ X19 )
      | ~ ( l3_lattices @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l1_lattices @ X1 )
      | ( v13_lattices @ X1 )
      | ( r4_lattice3 @ X1 @ ( sk_C_1 @ ( k15_lattice3 @ X1 @ X2 ) @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_D @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X1 @ X2 ) @ X1 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ k1_xboole_0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('13',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l3_lattices @ X27 )
      | ( v2_struct_0 @ X27 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X27 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(d21_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i,C: $i] :
            ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
           => ( ( C
                = ( k15_lattice3 @ A @ B ) )
            <=> ( ( r4_lattice3 @ A @ C @ B )
                & ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                   => ( ( r4_lattice3 @ A @ D @ B )
                     => ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( v2_struct_0 @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ~ ( v4_lattice3 @ X20 )
      | ~ ( l3_lattices @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( X21
       != ( k15_lattice3 @ X20 @ X22 ) )
      | ~ ( r4_lattice3 @ X20 @ X23 @ X22 )
      | ( r1_lattices @ X20 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('15',plain,(
    ! [X20: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X20 ) )
      | ( r1_lattices @ X20 @ ( k15_lattice3 @ X20 @ X22 ) @ X23 )
      | ~ ( r4_lattice3 @ X20 @ X23 @ X22 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X20 @ X22 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v4_lattice3 @ X20 )
      | ~ ( v10_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l3_lattices @ X27 )
      | ( v2_struct_0 @ X27 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X27 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r1_lattices @ X10 @ X9 @ X11 )
      | ( ( k2_lattices @ X10 @ X9 @ X11 )
        = X9 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v9_lattices @ X10 )
      | ~ ( v8_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
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
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['21','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['3','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('31',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l3_lattices @ X27 )
      | ( v2_struct_0 @ X27 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X27 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) ),
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

thf('32',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v6_lattices @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X24 ) )
      | ( ( k2_lattices @ X24 @ X26 @ X25 )
        = ( k2_lattices @ X24 @ X25 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ~ ( l1_lattices @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d6_lattices])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X2 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X2 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l3_lattices @ X27 )
      | ( v2_struct_0 @ X27 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X27 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_lattices @ X13 @ ( sk_C_1 @ X12 @ X13 ) @ X12 )
       != X12 )
      | ( ( k2_lattices @ X13 @ X12 @ ( sk_C_1 @ X12 @ X13 ) )
       != X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ( v13_lattices @ X13 )
      | ~ ( l1_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d13_lattices])).

thf('39',plain,(
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
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
       != ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

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

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( v13_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( v6_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('49',plain,(
    ! [X8: $i] :
      ( ( l1_lattices @ X8 )
      | ~ ( l3_lattices @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('50',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
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

thf('53',plain,(
    ! [X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v8_lattices @ X3 )
      | ~ ( l3_lattices @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v9_lattices @ X3 )
      | ~ ( l3_lattices @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ! [X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v6_lattices @ X3 )
      | ~ ( l3_lattices @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('66',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['46','47','50','51','52','58','64','70'])).

thf('72',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l3_lattices @ X27 )
      | ( v2_struct_0 @ X27 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X27 @ X28 ) @ ( u1_struct_0 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(dt_k5_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('73',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
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

thf('74',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( v13_lattices @ X4 )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X4 ) )
      | ( X5
       != ( k5_lattices @ X4 ) )
      | ( ( k2_lattices @ X4 @ X6 @ X5 )
        = X5 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_lattices @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d16_lattices])).

thf('75',plain,(
    ! [X4: $i,X6: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l1_lattices @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ( ( k2_lattices @ X4 @ X6 @ ( k5_lattices @ X4 ) )
        = ( k5_lattices @ X4 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v13_lattices @ X4 ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('81',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('82',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('83',plain,(
    ! [X15: $i,X16: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X19 @ X15 @ X16 ) @ X19 )
      | ( r4_lattice3 @ X16 @ X15 @ X19 )
      | ~ ( l3_lattices @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k5_lattices @ X0 ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k5_lattices @ X0 ) @ X0 ) @ X1 )
      | ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l1_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r4_lattice3 @ X1 @ ( k5_lattices @ X1 ) @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_D @ X0 @ ( k5_lattices @ X1 ) @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ k1_xboole_0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','87'])).

thf('89',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['88','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
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

thf('96',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['80','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['79','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['102'])).

thf('104',plain,
    ( ( ( ( k5_lattices @ sk_A )
       != ( k5_lattices @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( l1_lattices @ sk_A )
      | ~ ( v13_lattices @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['101','103'])).

thf('105',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['48','49'])).

thf('107',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('110',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('111',plain,
    ( ( ( ( k5_lattices @ sk_A )
       != ( k5_lattices @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v13_lattices @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['104','105','106','107','108','109','110'])).

thf('112',plain,
    ( ( ~ ( v13_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,
    ( $false
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['71','114'])).

thf('116',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['102'])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,
    ( ~ ( l3_lattices @ sk_A )
   <= ~ ( l3_lattices @ sk_A ) ),
    inference(split,[status(esa)],['102'])).

thf('121',plain,(
    l3_lattices @ sk_A ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ~ ( v10_lattices @ sk_A )
   <= ~ ( v10_lattices @ sk_A ) ),
    inference(split,[status(esa)],['102'])).

thf('124',plain,(
    v10_lattices @ sk_A ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['46','47','50','51','52','58','64','70'])).

thf('126',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ~ ( v13_lattices @ sk_A ) ),
    inference(split,[status(esa)],['102'])).

thf('127',plain,(
    v13_lattices @ sk_A ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['102'])).

thf('129',plain,(
    ( k5_lattices @ sk_A )
 != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ),
    inference('sat_resolution*',[status(thm)],['118','121','124','127','128'])).

thf('130',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['115','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ygswaMr6aq
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.12/2.32  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.12/2.32  % Solved by: fo/fo7.sh
% 2.12/2.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.12/2.32  % done 1389 iterations in 1.862s
% 2.12/2.32  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.12/2.32  % SZS output start Refutation
% 2.12/2.32  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.12/2.32  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 2.12/2.32  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.12/2.32  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 2.12/2.32  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 2.12/2.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.12/2.32  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 2.12/2.32  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 2.12/2.32  thf(sk_A_type, type, sk_A: $i).
% 2.12/2.32  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 2.12/2.32  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.12/2.32  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 2.12/2.32  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 2.12/2.32  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.12/2.32  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 2.12/2.32  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 2.12/2.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.12/2.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.12/2.32  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 2.12/2.32  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.12/2.32  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 2.12/2.32  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 2.12/2.32  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 2.12/2.32  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 2.12/2.32  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 2.12/2.32  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 2.12/2.32  thf(dt_k15_lattice3, axiom,
% 2.12/2.32    (![A:$i,B:$i]:
% 2.12/2.32     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 2.12/2.32       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 2.12/2.32  thf('0', plain,
% 2.12/2.32      (![X27 : $i, X28 : $i]:
% 2.12/2.32         (~ (l3_lattices @ X27)
% 2.12/2.32          | (v2_struct_0 @ X27)
% 2.12/2.32          | (m1_subset_1 @ (k15_lattice3 @ X27 @ X28) @ (u1_struct_0 @ X27)))),
% 2.12/2.32      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.12/2.32  thf(d13_lattices, axiom,
% 2.12/2.32    (![A:$i]:
% 2.12/2.32     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 2.12/2.32       ( ( v13_lattices @ A ) <=>
% 2.12/2.32         ( ?[B:$i]:
% 2.12/2.32           ( ( ![C:$i]:
% 2.12/2.32               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.32                 ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 2.12/2.32                   ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) & 
% 2.12/2.32             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 2.12/2.32  thf('1', plain,
% 2.12/2.32      (![X12 : $i, X13 : $i]:
% 2.12/2.32         ((m1_subset_1 @ (sk_C_1 @ X12 @ X13) @ (u1_struct_0 @ X13))
% 2.12/2.32          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 2.12/2.32          | (v13_lattices @ X13)
% 2.12/2.32          | ~ (l1_lattices @ X13)
% 2.12/2.32          | (v2_struct_0 @ X13))),
% 2.12/2.32      inference('cnf', [status(esa)], [d13_lattices])).
% 2.12/2.32  thf('2', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | (m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.12/2.32             (u1_struct_0 @ X0)))),
% 2.12/2.32      inference('sup-', [status(thm)], ['0', '1'])).
% 2.12/2.32  thf('3', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         ((m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.12/2.32           (u1_struct_0 @ X0))
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['2'])).
% 2.12/2.32  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.12/2.32  thf('4', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.12/2.32      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.12/2.32  thf('5', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         ((m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.12/2.32           (u1_struct_0 @ X0))
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['2'])).
% 2.12/2.32  thf(d17_lattice3, axiom,
% 2.12/2.32    (![A:$i]:
% 2.12/2.32     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 2.12/2.32       ( ![B:$i]:
% 2.12/2.32         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.32           ( ![C:$i]:
% 2.12/2.32             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 2.12/2.32               ( ![D:$i]:
% 2.12/2.32                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.32                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 2.12/2.32  thf('6', plain,
% 2.12/2.32      (![X15 : $i, X16 : $i, X19 : $i]:
% 2.12/2.32         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 2.12/2.32          | (r2_hidden @ (sk_D @ X19 @ X15 @ X16) @ X19)
% 2.12/2.32          | (r4_lattice3 @ X16 @ X15 @ X19)
% 2.12/2.32          | ~ (l3_lattices @ X16)
% 2.12/2.32          | (v2_struct_0 @ X16))),
% 2.12/2.32      inference('cnf', [status(esa)], [d17_lattice3])).
% 2.12/2.32  thf('7', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (r4_lattice3 @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 2.12/2.32          | (r2_hidden @ 
% 2.12/2.32             (sk_D @ X2 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X0) @ X2))),
% 2.12/2.32      inference('sup-', [status(thm)], ['5', '6'])).
% 2.12/2.32  thf('8', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.32         ((r2_hidden @ 
% 2.12/2.32           (sk_D @ X2 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X0) @ X2)
% 2.12/2.32          | (r4_lattice3 @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['7'])).
% 2.12/2.32  thf(t7_ordinal1, axiom,
% 2.12/2.32    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.12/2.32  thf('9', plain,
% 2.12/2.32      (![X1 : $i, X2 : $i]: (~ (r2_hidden @ X1 @ X2) | ~ (r1_tarski @ X2 @ X1))),
% 2.12/2.32      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.12/2.32  thf('10', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X1)
% 2.12/2.32          | ~ (l3_lattices @ X1)
% 2.12/2.32          | ~ (l1_lattices @ X1)
% 2.12/2.32          | (v13_lattices @ X1)
% 2.12/2.32          | (r4_lattice3 @ X1 @ (sk_C_1 @ (k15_lattice3 @ X1 @ X2) @ X1) @ X0)
% 2.12/2.32          | ~ (r1_tarski @ X0 @ 
% 2.12/2.32               (sk_D @ X0 @ (sk_C_1 @ (k15_lattice3 @ X1 @ X2) @ X1) @ X1)))),
% 2.12/2.32      inference('sup-', [status(thm)], ['8', '9'])).
% 2.12/2.32  thf('11', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         ((r4_lattice3 @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.12/2.32           k1_xboole_0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('sup-', [status(thm)], ['4', '10'])).
% 2.12/2.32  thf('12', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         ((m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.12/2.32           (u1_struct_0 @ X0))
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['2'])).
% 2.12/2.32  thf('13', plain,
% 2.12/2.32      (![X27 : $i, X28 : $i]:
% 2.12/2.32         (~ (l3_lattices @ X27)
% 2.12/2.32          | (v2_struct_0 @ X27)
% 2.12/2.32          | (m1_subset_1 @ (k15_lattice3 @ X27 @ X28) @ (u1_struct_0 @ X27)))),
% 2.12/2.32      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.12/2.32  thf(d21_lattice3, axiom,
% 2.12/2.32    (![A:$i]:
% 2.12/2.32     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 2.12/2.32       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.12/2.32           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.12/2.32         ( ![B:$i,C:$i]:
% 2.12/2.32           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.32             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 2.12/2.32               ( ( r4_lattice3 @ A @ C @ B ) & 
% 2.12/2.32                 ( ![D:$i]:
% 2.12/2.32                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.32                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 2.12/2.32                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 2.12/2.32  thf('14', plain,
% 2.12/2.32      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X20)
% 2.12/2.32          | ~ (v10_lattices @ X20)
% 2.12/2.32          | ~ (v4_lattice3 @ X20)
% 2.12/2.32          | ~ (l3_lattices @ X20)
% 2.12/2.32          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 2.12/2.32          | ((X21) != (k15_lattice3 @ X20 @ X22))
% 2.12/2.32          | ~ (r4_lattice3 @ X20 @ X23 @ X22)
% 2.12/2.32          | (r1_lattices @ X20 @ X21 @ X23)
% 2.12/2.32          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X20))
% 2.12/2.32          | ~ (l3_lattices @ X20)
% 2.12/2.32          | (v2_struct_0 @ X20))),
% 2.12/2.32      inference('cnf', [status(esa)], [d21_lattice3])).
% 2.12/2.32  thf('15', plain,
% 2.12/2.32      (![X20 : $i, X22 : $i, X23 : $i]:
% 2.12/2.32         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X20))
% 2.12/2.32          | (r1_lattices @ X20 @ (k15_lattice3 @ X20 @ X22) @ X23)
% 2.12/2.32          | ~ (r4_lattice3 @ X20 @ X23 @ X22)
% 2.12/2.32          | ~ (m1_subset_1 @ (k15_lattice3 @ X20 @ X22) @ (u1_struct_0 @ X20))
% 2.12/2.32          | ~ (l3_lattices @ X20)
% 2.12/2.32          | ~ (v4_lattice3 @ X20)
% 2.12/2.32          | ~ (v10_lattices @ X20)
% 2.12/2.32          | (v2_struct_0 @ X20))),
% 2.12/2.32      inference('simplify', [status(thm)], ['14'])).
% 2.12/2.32  thf('16', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 2.12/2.32          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.12/2.32          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 2.12/2.32      inference('sup-', [status(thm)], ['13', '15'])).
% 2.12/2.32  thf('17', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.32         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.12/2.32          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.12/2.32          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['16'])).
% 2.12/2.32  thf('18', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | ~ (r4_lattice3 @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 2.12/2.32          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.12/2.32             (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)))),
% 2.12/2.32      inference('sup-', [status(thm)], ['12', '17'])).
% 2.12/2.32  thf('19', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.32         ((r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.12/2.32           (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.12/2.32          | ~ (r4_lattice3 @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['18'])).
% 2.12/2.32  thf('20', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.32             (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)))),
% 2.12/2.32      inference('sup-', [status(thm)], ['11', '19'])).
% 2.12/2.32  thf('21', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         ((r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.32           (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['20'])).
% 2.12/2.32  thf('22', plain,
% 2.12/2.32      (![X27 : $i, X28 : $i]:
% 2.12/2.32         (~ (l3_lattices @ X27)
% 2.12/2.32          | (v2_struct_0 @ X27)
% 2.12/2.32          | (m1_subset_1 @ (k15_lattice3 @ X27 @ X28) @ (u1_struct_0 @ X27)))),
% 2.12/2.32      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.12/2.32  thf(t21_lattices, axiom,
% 2.12/2.32    (![A:$i]:
% 2.12/2.32     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 2.12/2.32         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 2.12/2.32       ( ![B:$i]:
% 2.12/2.32         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.32           ( ![C:$i]:
% 2.12/2.32             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.32               ( ( r1_lattices @ A @ B @ C ) <=>
% 2.12/2.32                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 2.12/2.32  thf('23', plain,
% 2.12/2.32      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.12/2.32         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 2.12/2.32          | ~ (r1_lattices @ X10 @ X9 @ X11)
% 2.12/2.32          | ((k2_lattices @ X10 @ X9 @ X11) = (X9))
% 2.12/2.32          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 2.12/2.32          | ~ (l3_lattices @ X10)
% 2.12/2.32          | ~ (v9_lattices @ X10)
% 2.12/2.32          | ~ (v8_lattices @ X10)
% 2.12/2.32          | (v2_struct_0 @ X10))),
% 2.12/2.32      inference('cnf', [status(esa)], [t21_lattices])).
% 2.12/2.32  thf('24', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (v8_lattices @ X0)
% 2.12/2.32          | ~ (v9_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.12/2.32          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.12/2.32              = (k15_lattice3 @ X0 @ X1))
% 2.12/2.32          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 2.12/2.32      inference('sup-', [status(thm)], ['22', '23'])).
% 2.12/2.32  thf('25', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.32         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.12/2.32          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.12/2.32              = (k15_lattice3 @ X0 @ X1))
% 2.12/2.32          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.12/2.32          | ~ (v9_lattices @ X0)
% 2.12/2.32          | ~ (v8_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['24'])).
% 2.12/2.32  thf('26', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (v8_lattices @ X0)
% 2.12/2.32          | ~ (v9_lattices @ X0)
% 2.12/2.32          | ~ (m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.12/2.32               (u1_struct_0 @ X0))
% 2.12/2.32          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.32              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.12/2.32              = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.12/2.32      inference('sup-', [status(thm)], ['21', '25'])).
% 2.12/2.32  thf('27', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.32            (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.12/2.32            = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.12/2.32          | ~ (m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.12/2.32               (u1_struct_0 @ X0))
% 2.12/2.32          | ~ (v9_lattices @ X0)
% 2.12/2.32          | ~ (v8_lattices @ X0)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['26'])).
% 2.12/2.32  thf('28', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | ~ (v8_lattices @ X0)
% 2.12/2.32          | ~ (v9_lattices @ X0)
% 2.12/2.32          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.32              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.12/2.32              = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.12/2.32      inference('sup-', [status(thm)], ['3', '27'])).
% 2.12/2.32  thf('29', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.32            (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.12/2.32            = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.12/2.32          | ~ (v9_lattices @ X0)
% 2.12/2.32          | ~ (v8_lattices @ X0)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['28'])).
% 2.12/2.32  thf('30', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         ((m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.12/2.32           (u1_struct_0 @ X0))
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['2'])).
% 2.12/2.32  thf('31', plain,
% 2.12/2.32      (![X27 : $i, X28 : $i]:
% 2.12/2.32         (~ (l3_lattices @ X27)
% 2.12/2.32          | (v2_struct_0 @ X27)
% 2.12/2.32          | (m1_subset_1 @ (k15_lattice3 @ X27 @ X28) @ (u1_struct_0 @ X27)))),
% 2.12/2.32      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.12/2.32  thf(d6_lattices, axiom,
% 2.12/2.32    (![A:$i]:
% 2.12/2.32     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 2.12/2.32       ( ( v6_lattices @ A ) <=>
% 2.12/2.32         ( ![B:$i]:
% 2.12/2.32           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.32             ( ![C:$i]:
% 2.12/2.32               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.32                 ( ( k2_lattices @ A @ B @ C ) = ( k2_lattices @ A @ C @ B ) ) ) ) ) ) ) ))).
% 2.12/2.32  thf('32', plain,
% 2.12/2.32      (![X24 : $i, X25 : $i, X26 : $i]:
% 2.12/2.32         (~ (v6_lattices @ X24)
% 2.12/2.32          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X24))
% 2.12/2.32          | ((k2_lattices @ X24 @ X26 @ X25) = (k2_lattices @ X24 @ X25 @ X26))
% 2.12/2.32          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 2.12/2.32          | ~ (l1_lattices @ X24)
% 2.12/2.32          | (v2_struct_0 @ X24))),
% 2.12/2.32      inference('cnf', [status(esa)], [d6_lattices])).
% 2.12/2.32  thf('33', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.12/2.32          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 2.12/2.32              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 2.12/2.32          | ~ (v6_lattices @ X0))),
% 2.12/2.32      inference('sup-', [status(thm)], ['31', '32'])).
% 2.12/2.32  thf('34', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.32         (~ (v6_lattices @ X0)
% 2.12/2.32          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 2.12/2.32              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 2.12/2.32          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['33'])).
% 2.12/2.32  thf('35', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ((k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.12/2.32              (k15_lattice3 @ X0 @ X2))
% 2.12/2.32              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.12/2.32                 (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 2.12/2.32          | ~ (v6_lattices @ X0))),
% 2.12/2.32      inference('sup-', [status(thm)], ['30', '34'])).
% 2.12/2.32  thf('36', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.32         (~ (v6_lattices @ X0)
% 2.12/2.32          | ((k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.12/2.32              (k15_lattice3 @ X0 @ X2))
% 2.12/2.32              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.12/2.32                 (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['35'])).
% 2.12/2.32  thf('37', plain,
% 2.12/2.32      (![X27 : $i, X28 : $i]:
% 2.12/2.32         (~ (l3_lattices @ X27)
% 2.12/2.32          | (v2_struct_0 @ X27)
% 2.12/2.32          | (m1_subset_1 @ (k15_lattice3 @ X27 @ X28) @ (u1_struct_0 @ X27)))),
% 2.12/2.32      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.12/2.32  thf('38', plain,
% 2.12/2.32      (![X12 : $i, X13 : $i]:
% 2.12/2.32         (((k2_lattices @ X13 @ (sk_C_1 @ X12 @ X13) @ X12) != (X12))
% 2.12/2.32          | ((k2_lattices @ X13 @ X12 @ (sk_C_1 @ X12 @ X13)) != (X12))
% 2.12/2.32          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 2.12/2.32          | (v13_lattices @ X13)
% 2.12/2.32          | ~ (l1_lattices @ X13)
% 2.12/2.32          | (v2_struct_0 @ X13))),
% 2.12/2.32      inference('cnf', [status(esa)], [d13_lattices])).
% 2.12/2.32  thf('39', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.12/2.32              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.12/2.32              != (k15_lattice3 @ X0 @ X1))
% 2.12/2.32          | ((k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.12/2.32              (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1)))),
% 2.12/2.32      inference('sup-', [status(thm)], ['37', '38'])).
% 2.12/2.32  thf('40', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         (((k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.12/2.32            (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1))
% 2.12/2.32          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.12/2.32              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.12/2.32              != (k15_lattice3 @ X0 @ X1))
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['39'])).
% 2.12/2.32  thf('41', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.12/2.32            (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.12/2.32            != (k15_lattice3 @ X0 @ X1))
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ~ (v6_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.12/2.32              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.12/2.32              != (k15_lattice3 @ X0 @ X1)))),
% 2.12/2.32      inference('sup-', [status(thm)], ['36', '40'])).
% 2.12/2.32  thf('42', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         (~ (v6_lattices @ X0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.12/2.32              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.12/2.32              != (k15_lattice3 @ X0 @ X1)))),
% 2.12/2.32      inference('simplify', [status(thm)], ['41'])).
% 2.12/2.32  thf('43', plain,
% 2.12/2.32      (![X0 : $i]:
% 2.12/2.32         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.12/2.32            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | ~ (v8_lattices @ X0)
% 2.12/2.32          | ~ (v9_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ~ (v6_lattices @ X0))),
% 2.12/2.32      inference('sup-', [status(thm)], ['29', '42'])).
% 2.12/2.32  thf('44', plain,
% 2.12/2.32      (![X0 : $i]:
% 2.12/2.32         (~ (v6_lattices @ X0)
% 2.12/2.32          | ~ (v9_lattices @ X0)
% 2.12/2.32          | ~ (v8_lattices @ X0)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | (v13_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['43'])).
% 2.12/2.32  thf(t50_lattice3, conjecture,
% 2.12/2.32    (![A:$i]:
% 2.12/2.32     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.12/2.32         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.12/2.32       ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.12/2.32         ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 2.12/2.32         ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ))).
% 2.12/2.32  thf(zf_stmt_0, negated_conjecture,
% 2.12/2.32    (~( ![A:$i]:
% 2.12/2.32        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.12/2.32            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.12/2.32          ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.12/2.32            ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 2.12/2.32            ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ) )),
% 2.12/2.32    inference('cnf.neg', [status(esa)], [t50_lattice3])).
% 2.12/2.32  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf('46', plain,
% 2.12/2.32      ((~ (l3_lattices @ sk_A)
% 2.12/2.32        | ~ (l1_lattices @ sk_A)
% 2.12/2.32        | (v13_lattices @ sk_A)
% 2.12/2.32        | ~ (v10_lattices @ sk_A)
% 2.12/2.32        | ~ (v4_lattice3 @ sk_A)
% 2.12/2.32        | ~ (v8_lattices @ sk_A)
% 2.12/2.32        | ~ (v9_lattices @ sk_A)
% 2.12/2.32        | ~ (v6_lattices @ sk_A))),
% 2.12/2.32      inference('sup-', [status(thm)], ['44', '45'])).
% 2.12/2.32  thf('47', plain, ((l3_lattices @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf('48', plain, ((l3_lattices @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf(dt_l3_lattices, axiom,
% 2.12/2.32    (![A:$i]:
% 2.12/2.32     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 2.12/2.32  thf('49', plain, (![X8 : $i]: ((l1_lattices @ X8) | ~ (l3_lattices @ X8))),
% 2.12/2.32      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 2.12/2.32  thf('50', plain, ((l1_lattices @ sk_A)),
% 2.12/2.32      inference('sup-', [status(thm)], ['48', '49'])).
% 2.12/2.32  thf('51', plain, ((v10_lattices @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf('52', plain, ((v4_lattice3 @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf(cc1_lattices, axiom,
% 2.12/2.32    (![A:$i]:
% 2.12/2.32     ( ( l3_lattices @ A ) =>
% 2.12/2.32       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 2.12/2.32         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 2.12/2.32           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 2.12/2.32           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 2.12/2.32  thf('53', plain,
% 2.12/2.32      (![X3 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X3)
% 2.12/2.32          | ~ (v10_lattices @ X3)
% 2.12/2.32          | (v8_lattices @ X3)
% 2.12/2.32          | ~ (l3_lattices @ X3))),
% 2.12/2.32      inference('cnf', [status(esa)], [cc1_lattices])).
% 2.12/2.32  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf('55', plain,
% 2.12/2.32      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 2.12/2.32      inference('sup-', [status(thm)], ['53', '54'])).
% 2.12/2.32  thf('56', plain, ((l3_lattices @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf('57', plain, ((v10_lattices @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf('58', plain, ((v8_lattices @ sk_A)),
% 2.12/2.32      inference('demod', [status(thm)], ['55', '56', '57'])).
% 2.12/2.32  thf('59', plain,
% 2.12/2.32      (![X3 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X3)
% 2.12/2.32          | ~ (v10_lattices @ X3)
% 2.12/2.32          | (v9_lattices @ X3)
% 2.12/2.32          | ~ (l3_lattices @ X3))),
% 2.12/2.32      inference('cnf', [status(esa)], [cc1_lattices])).
% 2.12/2.32  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf('61', plain,
% 2.12/2.32      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 2.12/2.32      inference('sup-', [status(thm)], ['59', '60'])).
% 2.12/2.32  thf('62', plain, ((l3_lattices @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf('63', plain, ((v10_lattices @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf('64', plain, ((v9_lattices @ sk_A)),
% 2.12/2.32      inference('demod', [status(thm)], ['61', '62', '63'])).
% 2.12/2.32  thf('65', plain,
% 2.12/2.32      (![X3 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X3)
% 2.12/2.32          | ~ (v10_lattices @ X3)
% 2.12/2.32          | (v6_lattices @ X3)
% 2.12/2.32          | ~ (l3_lattices @ X3))),
% 2.12/2.32      inference('cnf', [status(esa)], [cc1_lattices])).
% 2.12/2.32  thf('66', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf('67', plain,
% 2.12/2.32      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 2.12/2.32      inference('sup-', [status(thm)], ['65', '66'])).
% 2.12/2.32  thf('68', plain, ((l3_lattices @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf('69', plain, ((v10_lattices @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf('70', plain, ((v6_lattices @ sk_A)),
% 2.12/2.32      inference('demod', [status(thm)], ['67', '68', '69'])).
% 2.12/2.32  thf('71', plain, ((v13_lattices @ sk_A)),
% 2.12/2.32      inference('demod', [status(thm)],
% 2.12/2.32                ['46', '47', '50', '51', '52', '58', '64', '70'])).
% 2.12/2.32  thf('72', plain,
% 2.12/2.32      (![X27 : $i, X28 : $i]:
% 2.12/2.32         (~ (l3_lattices @ X27)
% 2.12/2.32          | (v2_struct_0 @ X27)
% 2.12/2.32          | (m1_subset_1 @ (k15_lattice3 @ X27 @ X28) @ (u1_struct_0 @ X27)))),
% 2.12/2.32      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.12/2.32  thf(dt_k5_lattices, axiom,
% 2.12/2.32    (![A:$i]:
% 2.12/2.32     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 2.12/2.32       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 2.12/2.32  thf('73', plain,
% 2.12/2.32      (![X7 : $i]:
% 2.12/2.32         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 2.12/2.32          | ~ (l1_lattices @ X7)
% 2.12/2.32          | (v2_struct_0 @ X7))),
% 2.12/2.32      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 2.12/2.32  thf(d16_lattices, axiom,
% 2.12/2.32    (![A:$i]:
% 2.12/2.32     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 2.12/2.32       ( ( v13_lattices @ A ) =>
% 2.12/2.32         ( ![B:$i]:
% 2.12/2.32           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.32             ( ( ( B ) = ( k5_lattices @ A ) ) <=>
% 2.12/2.32               ( ![C:$i]:
% 2.12/2.32                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.32                   ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 2.12/2.32                     ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 2.12/2.32  thf('74', plain,
% 2.12/2.32      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.12/2.32         (~ (v13_lattices @ X4)
% 2.12/2.32          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 2.12/2.32          | ((X5) != (k5_lattices @ X4))
% 2.12/2.32          | ((k2_lattices @ X4 @ X6 @ X5) = (X5))
% 2.12/2.32          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 2.12/2.32          | ~ (l1_lattices @ X4)
% 2.12/2.32          | (v2_struct_0 @ X4))),
% 2.12/2.32      inference('cnf', [status(esa)], [d16_lattices])).
% 2.12/2.32  thf('75', plain,
% 2.12/2.32      (![X4 : $i, X6 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X4)
% 2.12/2.32          | ~ (l1_lattices @ X4)
% 2.12/2.32          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 2.12/2.32          | ((k2_lattices @ X4 @ X6 @ (k5_lattices @ X4)) = (k5_lattices @ X4))
% 2.12/2.32          | ~ (m1_subset_1 @ (k5_lattices @ X4) @ (u1_struct_0 @ X4))
% 2.12/2.32          | ~ (v13_lattices @ X4))),
% 2.12/2.32      inference('simplify', [status(thm)], ['74'])).
% 2.12/2.32  thf('76', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (v13_lattices @ X0)
% 2.12/2.32          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 2.12/2.32          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('sup-', [status(thm)], ['73', '75'])).
% 2.12/2.32  thf('77', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 2.12/2.32          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 2.12/2.32          | ~ (v13_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['76'])).
% 2.12/2.32  thf('78', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (v13_lattices @ X0)
% 2.12/2.32          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.12/2.32              = (k5_lattices @ X0)))),
% 2.12/2.32      inference('sup-', [status(thm)], ['72', '77'])).
% 2.12/2.32  thf('79', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.12/2.32            = (k5_lattices @ X0))
% 2.12/2.32          | ~ (v13_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['78'])).
% 2.12/2.32  thf('80', plain,
% 2.12/2.32      (![X7 : $i]:
% 2.12/2.32         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 2.12/2.32          | ~ (l1_lattices @ X7)
% 2.12/2.32          | (v2_struct_0 @ X7))),
% 2.12/2.32      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 2.12/2.32  thf('81', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.12/2.32      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.12/2.32  thf('82', plain,
% 2.12/2.32      (![X7 : $i]:
% 2.12/2.32         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 2.12/2.32          | ~ (l1_lattices @ X7)
% 2.12/2.32          | (v2_struct_0 @ X7))),
% 2.12/2.32      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 2.12/2.32  thf('83', plain,
% 2.12/2.32      (![X15 : $i, X16 : $i, X19 : $i]:
% 2.12/2.32         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 2.12/2.32          | (r2_hidden @ (sk_D @ X19 @ X15 @ X16) @ X19)
% 2.12/2.32          | (r4_lattice3 @ X16 @ X15 @ X19)
% 2.12/2.32          | ~ (l3_lattices @ X16)
% 2.12/2.32          | (v2_struct_0 @ X16))),
% 2.12/2.32      inference('cnf', [status(esa)], [d17_lattice3])).
% 2.12/2.32  thf('84', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ X1)
% 2.12/2.32          | (r2_hidden @ (sk_D @ X1 @ (k5_lattices @ X0) @ X0) @ X1))),
% 2.12/2.32      inference('sup-', [status(thm)], ['82', '83'])).
% 2.12/2.32  thf('85', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         ((r2_hidden @ (sk_D @ X1 @ (k5_lattices @ X0) @ X0) @ X1)
% 2.12/2.32          | (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ X1)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['84'])).
% 2.12/2.32  thf('86', plain,
% 2.12/2.32      (![X1 : $i, X2 : $i]: (~ (r2_hidden @ X1 @ X2) | ~ (r1_tarski @ X2 @ X1))),
% 2.12/2.32      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.12/2.32  thf('87', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X1)
% 2.12/2.32          | ~ (l1_lattices @ X1)
% 2.12/2.32          | ~ (l3_lattices @ X1)
% 2.12/2.32          | (r4_lattice3 @ X1 @ (k5_lattices @ X1) @ X0)
% 2.12/2.32          | ~ (r1_tarski @ X0 @ (sk_D @ X0 @ (k5_lattices @ X1) @ X1)))),
% 2.12/2.32      inference('sup-', [status(thm)], ['85', '86'])).
% 2.12/2.32  thf('88', plain,
% 2.12/2.32      (![X0 : $i]:
% 2.12/2.32         ((r4_lattice3 @ X0 @ (k5_lattices @ X0) @ k1_xboole_0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('sup-', [status(thm)], ['81', '87'])).
% 2.12/2.32  thf('89', plain,
% 2.12/2.32      (![X7 : $i]:
% 2.12/2.32         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 2.12/2.32          | ~ (l1_lattices @ X7)
% 2.12/2.32          | (v2_struct_0 @ X7))),
% 2.12/2.32      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 2.12/2.32  thf('90', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.32         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.12/2.32          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.12/2.32          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['16'])).
% 2.12/2.32  thf('91', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | ~ (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ X1)
% 2.12/2.32          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0)))),
% 2.12/2.32      inference('sup-', [status(thm)], ['89', '90'])).
% 2.12/2.32  thf('92', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i]:
% 2.12/2.32         ((r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.12/2.32          | ~ (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ X1)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['91'])).
% 2.12/2.32  thf('93', plain,
% 2.12/2.32      (![X0 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.32             (k5_lattices @ X0)))),
% 2.12/2.32      inference('sup-', [status(thm)], ['88', '92'])).
% 2.12/2.32  thf('94', plain,
% 2.12/2.32      (![X0 : $i]:
% 2.12/2.32         ((r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.32           (k5_lattices @ X0))
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['93'])).
% 2.12/2.32  thf('95', plain,
% 2.12/2.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.32         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.12/2.32          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.12/2.32              = (k15_lattice3 @ X0 @ X1))
% 2.12/2.32          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.12/2.32          | ~ (v9_lattices @ X0)
% 2.12/2.32          | ~ (v8_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['24'])).
% 2.12/2.32  thf('96', plain,
% 2.12/2.32      (![X0 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (v8_lattices @ X0)
% 2.12/2.32          | ~ (v9_lattices @ X0)
% 2.12/2.32          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 2.12/2.32          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.32              (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.12/2.32      inference('sup-', [status(thm)], ['94', '95'])).
% 2.12/2.32  thf('97', plain,
% 2.12/2.32      (![X0 : $i]:
% 2.12/2.32         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.32            (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.12/2.32          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 2.12/2.32          | ~ (v9_lattices @ X0)
% 2.12/2.32          | ~ (v8_lattices @ X0)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['96'])).
% 2.12/2.32  thf('98', plain,
% 2.12/2.32      (![X0 : $i]:
% 2.12/2.32         ((v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | ~ (v8_lattices @ X0)
% 2.12/2.32          | ~ (v9_lattices @ X0)
% 2.12/2.32          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.32              (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.12/2.32      inference('sup-', [status(thm)], ['80', '97'])).
% 2.12/2.32  thf('99', plain,
% 2.12/2.32      (![X0 : $i]:
% 2.12/2.32         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.32            (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.12/2.32          | ~ (v9_lattices @ X0)
% 2.12/2.32          | ~ (v8_lattices @ X0)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0))),
% 2.12/2.32      inference('simplify', [status(thm)], ['98'])).
% 2.12/2.32  thf('100', plain,
% 2.12/2.32      (![X0 : $i]:
% 2.12/2.32         (((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (v13_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | ~ (v8_lattices @ X0)
% 2.12/2.32          | ~ (v9_lattices @ X0))),
% 2.12/2.32      inference('sup+', [status(thm)], ['79', '99'])).
% 2.12/2.32  thf('101', plain,
% 2.12/2.32      (![X0 : $i]:
% 2.12/2.32         (~ (v9_lattices @ X0)
% 2.12/2.32          | ~ (v8_lattices @ X0)
% 2.12/2.32          | ~ (v4_lattice3 @ X0)
% 2.12/2.32          | ~ (v10_lattices @ X0)
% 2.12/2.32          | ~ (v13_lattices @ X0)
% 2.12/2.32          | ~ (l1_lattices @ X0)
% 2.12/2.32          | ~ (l3_lattices @ X0)
% 2.12/2.32          | (v2_struct_0 @ X0)
% 2.12/2.32          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.12/2.32      inference('simplify', [status(thm)], ['100'])).
% 2.12/2.32  thf('102', plain,
% 2.12/2.32      (((v2_struct_0 @ sk_A)
% 2.12/2.32        | ~ (v10_lattices @ sk_A)
% 2.12/2.32        | ~ (v13_lattices @ sk_A)
% 2.12/2.32        | ~ (l3_lattices @ sk_A)
% 2.12/2.32        | ((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf('103', plain,
% 2.12/2.32      ((((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))
% 2.12/2.32         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.12/2.32      inference('split', [status(esa)], ['102'])).
% 2.12/2.32  thf('104', plain,
% 2.12/2.32      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 2.12/2.32         | (v2_struct_0 @ sk_A)
% 2.12/2.32         | ~ (l3_lattices @ sk_A)
% 2.12/2.32         | ~ (l1_lattices @ sk_A)
% 2.12/2.32         | ~ (v13_lattices @ sk_A)
% 2.12/2.32         | ~ (v10_lattices @ sk_A)
% 2.12/2.32         | ~ (v4_lattice3 @ sk_A)
% 2.12/2.32         | ~ (v8_lattices @ sk_A)
% 2.12/2.32         | ~ (v9_lattices @ sk_A)))
% 2.12/2.32         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.12/2.32      inference('sup-', [status(thm)], ['101', '103'])).
% 2.12/2.32  thf('105', plain, ((l3_lattices @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf('106', plain, ((l1_lattices @ sk_A)),
% 2.12/2.32      inference('sup-', [status(thm)], ['48', '49'])).
% 2.12/2.32  thf('107', plain, ((v10_lattices @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf('108', plain, ((v4_lattice3 @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf('109', plain, ((v8_lattices @ sk_A)),
% 2.12/2.32      inference('demod', [status(thm)], ['55', '56', '57'])).
% 2.12/2.32  thf('110', plain, ((v9_lattices @ sk_A)),
% 2.12/2.32      inference('demod', [status(thm)], ['61', '62', '63'])).
% 2.12/2.32  thf('111', plain,
% 2.12/2.32      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 2.12/2.32         | (v2_struct_0 @ sk_A)
% 2.12/2.32         | ~ (v13_lattices @ sk_A)))
% 2.12/2.32         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.12/2.32      inference('demod', [status(thm)],
% 2.12/2.32                ['104', '105', '106', '107', '108', '109', '110'])).
% 2.12/2.32  thf('112', plain,
% 2.12/2.32      (((~ (v13_lattices @ sk_A) | (v2_struct_0 @ sk_A)))
% 2.12/2.32         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.12/2.32      inference('simplify', [status(thm)], ['111'])).
% 2.12/2.32  thf('113', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf('114', plain,
% 2.12/2.32      ((~ (v13_lattices @ sk_A))
% 2.12/2.32         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.12/2.32      inference('clc', [status(thm)], ['112', '113'])).
% 2.12/2.32  thf('115', plain,
% 2.12/2.32      (($false)
% 2.12/2.32         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.12/2.32      inference('sup-', [status(thm)], ['71', '114'])).
% 2.12/2.32  thf('116', plain, (((v2_struct_0 @ sk_A)) <= (((v2_struct_0 @ sk_A)))),
% 2.12/2.32      inference('split', [status(esa)], ['102'])).
% 2.12/2.32  thf('117', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf('118', plain, (~ ((v2_struct_0 @ sk_A))),
% 2.12/2.32      inference('sup-', [status(thm)], ['116', '117'])).
% 2.12/2.32  thf('119', plain, ((l3_lattices @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf('120', plain, ((~ (l3_lattices @ sk_A)) <= (~ ((l3_lattices @ sk_A)))),
% 2.12/2.32      inference('split', [status(esa)], ['102'])).
% 2.12/2.32  thf('121', plain, (((l3_lattices @ sk_A))),
% 2.12/2.32      inference('sup-', [status(thm)], ['119', '120'])).
% 2.12/2.32  thf('122', plain, ((v10_lattices @ sk_A)),
% 2.12/2.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.32  thf('123', plain, ((~ (v10_lattices @ sk_A)) <= (~ ((v10_lattices @ sk_A)))),
% 2.12/2.32      inference('split', [status(esa)], ['102'])).
% 2.12/2.32  thf('124', plain, (((v10_lattices @ sk_A))),
% 2.12/2.32      inference('sup-', [status(thm)], ['122', '123'])).
% 2.12/2.32  thf('125', plain, ((v13_lattices @ sk_A)),
% 2.12/2.32      inference('demod', [status(thm)],
% 2.12/2.32                ['46', '47', '50', '51', '52', '58', '64', '70'])).
% 2.12/2.32  thf('126', plain, ((~ (v13_lattices @ sk_A)) <= (~ ((v13_lattices @ sk_A)))),
% 2.12/2.32      inference('split', [status(esa)], ['102'])).
% 2.12/2.32  thf('127', plain, (((v13_lattices @ sk_A))),
% 2.12/2.32      inference('sup-', [status(thm)], ['125', '126'])).
% 2.12/2.32  thf('128', plain,
% 2.12/2.32      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))) | 
% 2.12/2.32       ~ ((v13_lattices @ sk_A)) | ~ ((v10_lattices @ sk_A)) | 
% 2.12/2.32       ~ ((l3_lattices @ sk_A)) | ((v2_struct_0 @ sk_A))),
% 2.12/2.32      inference('split', [status(esa)], ['102'])).
% 2.12/2.32  thf('129', plain,
% 2.12/2.32      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 2.12/2.32      inference('sat_resolution*', [status(thm)],
% 2.12/2.32                ['118', '121', '124', '127', '128'])).
% 2.12/2.32  thf('130', plain, ($false),
% 2.12/2.32      inference('simpl_trail', [status(thm)], ['115', '129'])).
% 2.12/2.32  
% 2.12/2.32  % SZS output end Refutation
% 2.12/2.32  
% 2.12/2.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
