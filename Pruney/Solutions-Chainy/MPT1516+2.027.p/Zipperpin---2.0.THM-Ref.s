%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DM11UhOuLV

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:38 EST 2020

% Result     : Theorem 2.12s
% Output     : Refutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 520 expanded)
%              Number of leaves         :   42 ( 163 expanded)
%              Depth                    :   24
%              Number of atoms          : 2500 (8745 expanded)
%              Number of equality atoms :   73 ( 252 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

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

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l3_lattices @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ X15 @ X16 ) @ ( u1_struct_0 @ X16 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( v13_lattices @ X16 )
      | ~ ( l1_lattices @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
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

thf('4',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( ( k15_lattice3 @ X24 @ ( k6_domain_1 @ ( u1_struct_0 @ X24 ) @ X23 ) )
        = X23 )
      | ~ ( l3_lattices @ X24 )
      | ~ ( v4_lattice3 @ X24 )
      | ~ ( v10_lattices @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t43_lattice3])).

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
      | ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) )
        = ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) )
        = ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l3_lattices @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( r2_hidden @ ( sk_D @ X27 @ X28 @ X26 ) @ X28 )
      | ( r3_lattices @ X26 @ ( k15_lattice3 @ X26 @ X28 ) @ ( k15_lattice3 @ X26 @ X27 ) )
      | ~ ( l3_lattices @ X26 )
      | ~ ( v4_lattice3 @ X26 )
      | ~ ( v10_lattices @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( l3_lattices @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l3_lattices @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) ),
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ~ ( v9_lattices @ X10 )
      | ~ ( v8_lattices @ X10 )
      | ~ ( v6_lattices @ X10 )
      | ( v2_struct_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( r1_lattices @ X10 @ X9 @ X11 )
      | ~ ( r3_lattices @ X10 @ X9 @ X11 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( l3_lattices @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r1_lattices @ X13 @ X12 @ X14 )
      | ( ( k2_lattices @ X13 @ X12 @ X14 )
        = X12 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l3_lattices @ X13 )
      | ~ ( v9_lattices @ X13 )
      | ~ ( v8_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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
      ( ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) )
        = ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
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
    ! [X21: $i,X22: $i] :
      ( ~ ( l3_lattices @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('35',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( l3_lattices @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v6_lattices @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ( ( k2_lattices @ X18 @ X20 @ X19 )
        = ( k2_lattices @ X18 @ X19 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l1_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( l3_lattices @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_lattices @ X16 @ ( sk_C_1 @ X15 @ X16 ) @ X15 )
       != X15 )
      | ( ( k2_lattices @ X16 @ X15 @ ( sk_C_1 @ X15 @ X16 ) )
       != X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ( v13_lattices @ X16 )
      | ~ ( l1_lattices @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
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
    ! [X8: $i] :
      ( ( l1_lattices @ X8 )
      | ~ ( l3_lattices @ X8 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ~ ( l3_lattices @ X21 )
      | ( v2_struct_0 @ X21 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X21 @ X22 ) @ ( u1_struct_0 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(dt_k5_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('81',plain,(
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

thf('82',plain,(
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

thf('83',plain,(
    ! [X4: $i,X6: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l1_lattices @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ( ( k2_lattices @ X4 @ X6 @ ( k5_lattices @ X4 ) )
        = ( k5_lattices @ X4 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v13_lattices @ X4 ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['80','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('89',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('90',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X24 ) )
      | ( ( k15_lattice3 @ X24 @ ( k6_domain_1 @ ( u1_struct_0 @ X24 ) @ X23 ) )
        = X23 )
      | ~ ( l3_lattices @ X24 )
      | ~ ( v4_lattice3 @ X24 )
      | ~ ( v10_lattices @ X24 )
      | ( v2_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t43_lattice3])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k5_lattices @ X0 ) ) )
        = ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k5_lattices @ X0 ) ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X7 ) @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_lattices @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('97',plain,(
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

thf('98',plain,(
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
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
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
    inference('sup-',[status(thm)],['95','99'])).

thf('101',plain,(
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
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
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

thf('103',plain,(
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
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
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
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
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
    inference('sup-',[status(thm)],['88','104'])).

thf('106',plain,(
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
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
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
    inference('sup+',[status(thm)],['87','106'])).

thf('108',plain,(
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
    inference(simplify,[status(thm)],['107'])).

thf('109',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['109'])).

thf('111',plain,
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
    inference('sup-',[status(thm)],['108','110'])).

thf('112',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('114',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('117',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('118',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('119',plain,
    ( ( ( ( k5_lattices @ sk_A )
       != ( k5_lattices @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v13_lattices @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['111','112','113','114','115','116','117','118'])).

thf('120',plain,
    ( ( ~ ( v13_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,
    ( $false
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['79','122'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['109'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ~ ( l3_lattices @ sk_A )
   <= ~ ( l3_lattices @ sk_A ) ),
    inference(split,[status(esa)],['109'])).

thf('129',plain,(
    l3_lattices @ sk_A ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,
    ( ~ ( v10_lattices @ sk_A )
   <= ~ ( v10_lattices @ sk_A ) ),
    inference(split,[status(esa)],['109'])).

thf('132',plain,(
    v10_lattices @ sk_A ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['54','55','58','59','60','66','72','78'])).

thf('134',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ~ ( v13_lattices @ sk_A ) ),
    inference(split,[status(esa)],['109'])).

thf('135',plain,(
    v13_lattices @ sk_A ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['109'])).

thf('137',plain,(
    ( k5_lattices @ sk_A )
 != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ),
    inference('sat_resolution*',[status(thm)],['126','129','132','135','136'])).

thf('138',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['123','137'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.DM11UhOuLV
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:58:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.12/2.31  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.12/2.31  % Solved by: fo/fo7.sh
% 2.12/2.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.12/2.31  % done 1256 iterations in 1.816s
% 2.12/2.31  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.12/2.31  % SZS output start Refutation
% 2.12/2.31  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.12/2.31  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 2.12/2.31  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 2.12/2.31  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 2.12/2.31  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 2.12/2.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.12/2.31  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 2.12/2.31  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 2.12/2.31  thf(sk_A_type, type, sk_A: $i).
% 2.12/2.31  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 2.12/2.31  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.12/2.31  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.12/2.31  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 2.12/2.31  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 2.12/2.31  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 2.12/2.31  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 2.12/2.31  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 2.12/2.31  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.12/2.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.12/2.31  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 2.12/2.31  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 2.12/2.31  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 2.12/2.31  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.12/2.31  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 2.12/2.31  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 2.12/2.31  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 2.12/2.31  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 2.12/2.31  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 2.12/2.31  thf(dt_k15_lattice3, axiom,
% 2.12/2.31    (![A:$i,B:$i]:
% 2.12/2.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 2.12/2.31       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 2.12/2.31  thf('0', plain,
% 2.12/2.31      (![X21 : $i, X22 : $i]:
% 2.12/2.31         (~ (l3_lattices @ X21)
% 2.12/2.31          | (v2_struct_0 @ X21)
% 2.12/2.31          | (m1_subset_1 @ (k15_lattice3 @ X21 @ X22) @ (u1_struct_0 @ X21)))),
% 2.12/2.31      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.12/2.31  thf(d13_lattices, axiom,
% 2.12/2.31    (![A:$i]:
% 2.12/2.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 2.12/2.31       ( ( v13_lattices @ A ) <=>
% 2.12/2.31         ( ?[B:$i]:
% 2.12/2.31           ( ( ![C:$i]:
% 2.12/2.31               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.31                 ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 2.12/2.31                   ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) & 
% 2.12/2.31             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 2.12/2.31  thf('1', plain,
% 2.12/2.31      (![X15 : $i, X16 : $i]:
% 2.12/2.31         ((m1_subset_1 @ (sk_C_1 @ X15 @ X16) @ (u1_struct_0 @ X16))
% 2.12/2.31          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 2.12/2.31          | (v13_lattices @ X16)
% 2.12/2.31          | ~ (l1_lattices @ X16)
% 2.12/2.31          | (v2_struct_0 @ X16))),
% 2.12/2.31      inference('cnf', [status(esa)], [d13_lattices])).
% 2.12/2.31  thf('2', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | (v13_lattices @ X0)
% 2.12/2.31          | (m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.12/2.31             (u1_struct_0 @ X0)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['0', '1'])).
% 2.12/2.31  thf('3', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         ((m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.12/2.31           (u1_struct_0 @ X0))
% 2.12/2.31          | (v13_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['2'])).
% 2.12/2.31  thf(t43_lattice3, axiom,
% 2.12/2.31    (![A:$i]:
% 2.12/2.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.12/2.31         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.12/2.31       ( ![B:$i]:
% 2.12/2.31         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.31           ( ( ( k15_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 2.12/2.31               ( B ) ) & 
% 2.12/2.31             ( ( k16_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 2.12/2.31               ( B ) ) ) ) ) ))).
% 2.12/2.31  thf('4', plain,
% 2.12/2.31      (![X23 : $i, X24 : $i]:
% 2.12/2.31         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 2.12/2.31          | ((k15_lattice3 @ X24 @ (k6_domain_1 @ (u1_struct_0 @ X24) @ X23))
% 2.12/2.31              = (X23))
% 2.12/2.31          | ~ (l3_lattices @ X24)
% 2.12/2.31          | ~ (v4_lattice3 @ X24)
% 2.12/2.31          | ~ (v10_lattices @ X24)
% 2.12/2.31          | (v2_struct_0 @ X24))),
% 2.12/2.31      inference('cnf', [status(esa)], [t43_lattice3])).
% 2.12/2.31  thf('5', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | (v13_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ((k15_lattice3 @ X0 @ 
% 2.12/2.31              (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 2.12/2.31               (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 2.12/2.31              = (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['3', '4'])).
% 2.12/2.31  thf('6', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (((k15_lattice3 @ X0 @ 
% 2.12/2.31            (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 2.12/2.31             (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 2.12/2.31            = (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | (v13_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['5'])).
% 2.12/2.31  thf('7', plain,
% 2.12/2.31      (![X21 : $i, X22 : $i]:
% 2.12/2.31         (~ (l3_lattices @ X21)
% 2.12/2.31          | (v2_struct_0 @ X21)
% 2.12/2.31          | (m1_subset_1 @ (k15_lattice3 @ X21 @ X22) @ (u1_struct_0 @ X21)))),
% 2.12/2.31      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.12/2.31  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 2.12/2.31  thf('8', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 2.12/2.31      inference('cnf', [status(esa)], [t2_xboole_1])).
% 2.12/2.31  thf(t48_lattice3, axiom,
% 2.12/2.31    (![A:$i]:
% 2.12/2.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.12/2.31         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.12/2.31       ( ![B:$i,C:$i]:
% 2.12/2.31         ( ( ![D:$i]:
% 2.12/2.31             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.31               ( ~( ( r2_hidden @ D @ B ) & 
% 2.12/2.31                    ( ![E:$i]:
% 2.12/2.31                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.31                        ( ~( ( r3_lattices @ A @ D @ E ) & 
% 2.12/2.31                             ( r2_hidden @ E @ C ) ) ) ) ) ) ) ) ) =>
% 2.12/2.31           ( r3_lattices @
% 2.12/2.31             A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) ) ) ))).
% 2.12/2.31  thf('9', plain,
% 2.12/2.31      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.12/2.31         ((r2_hidden @ (sk_D @ X27 @ X28 @ X26) @ X28)
% 2.12/2.31          | (r3_lattices @ X26 @ (k15_lattice3 @ X26 @ X28) @ 
% 2.12/2.31             (k15_lattice3 @ X26 @ X27))
% 2.12/2.31          | ~ (l3_lattices @ X26)
% 2.12/2.31          | ~ (v4_lattice3 @ X26)
% 2.12/2.31          | ~ (v10_lattices @ X26)
% 2.12/2.31          | (v2_struct_0 @ X26))),
% 2.12/2.31      inference('cnf', [status(esa)], [t48_lattice3])).
% 2.12/2.31  thf(t7_ordinal1, axiom,
% 2.12/2.31    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.12/2.31  thf('10', plain,
% 2.12/2.31      (![X1 : $i, X2 : $i]: (~ (r2_hidden @ X1 @ X2) | ~ (r1_tarski @ X2 @ X1))),
% 2.12/2.31      inference('cnf', [status(esa)], [t7_ordinal1])).
% 2.12/2.31  thf('11', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X1)
% 2.12/2.31          | ~ (v10_lattices @ X1)
% 2.12/2.31          | ~ (v4_lattice3 @ X1)
% 2.12/2.31          | ~ (l3_lattices @ X1)
% 2.12/2.31          | (r3_lattices @ X1 @ (k15_lattice3 @ X1 @ X0) @ 
% 2.12/2.31             (k15_lattice3 @ X1 @ X2))
% 2.12/2.31          | ~ (r1_tarski @ X0 @ (sk_D @ X2 @ X0 @ X1)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['9', '10'])).
% 2.12/2.31  thf('12', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         ((r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.31           (k15_lattice3 @ X0 @ X1))
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['8', '11'])).
% 2.12/2.31  thf('13', plain,
% 2.12/2.31      (![X21 : $i, X22 : $i]:
% 2.12/2.31         (~ (l3_lattices @ X21)
% 2.12/2.31          | (v2_struct_0 @ X21)
% 2.12/2.31          | (m1_subset_1 @ (k15_lattice3 @ X21 @ X22) @ (u1_struct_0 @ X21)))),
% 2.12/2.31      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.12/2.31  thf('14', plain,
% 2.12/2.31      (![X21 : $i, X22 : $i]:
% 2.12/2.31         (~ (l3_lattices @ X21)
% 2.12/2.31          | (v2_struct_0 @ X21)
% 2.12/2.31          | (m1_subset_1 @ (k15_lattice3 @ X21 @ X22) @ (u1_struct_0 @ X21)))),
% 2.12/2.31      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.12/2.31  thf(redefinition_r3_lattices, axiom,
% 2.12/2.31    (![A:$i,B:$i,C:$i]:
% 2.12/2.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 2.12/2.31         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 2.12/2.31         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 2.12/2.31         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 2.12/2.31       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 2.12/2.31  thf('15', plain,
% 2.12/2.31      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.12/2.31         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 2.12/2.31          | ~ (l3_lattices @ X10)
% 2.12/2.31          | ~ (v9_lattices @ X10)
% 2.12/2.31          | ~ (v8_lattices @ X10)
% 2.12/2.31          | ~ (v6_lattices @ X10)
% 2.12/2.31          | (v2_struct_0 @ X10)
% 2.12/2.31          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 2.12/2.31          | (r1_lattices @ X10 @ X9 @ X11)
% 2.12/2.31          | ~ (r3_lattices @ X10 @ X9 @ X11))),
% 2.12/2.31      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 2.12/2.31  thf('16', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.12/2.31          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.12/2.31          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['14', '15'])).
% 2.12/2.31  thf('17', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.31         (~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.12/2.31          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.12/2.31          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['16'])).
% 2.12/2.31  thf('18', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.12/2.31               (k15_lattice3 @ X0 @ X1))
% 2.12/2.31          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.12/2.31             (k15_lattice3 @ X0 @ X1))
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v9_lattices @ X0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['13', '17'])).
% 2.12/2.31  thf('19', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.31         (~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.12/2.31             (k15_lattice3 @ X0 @ X1))
% 2.12/2.31          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.12/2.31               (k15_lattice3 @ X0 @ X1))
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['18'])).
% 2.12/2.31  thf('20', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X1)
% 2.12/2.31          | ~ (v10_lattices @ X1)
% 2.12/2.31          | ~ (v4_lattice3 @ X1)
% 2.12/2.31          | ~ (l3_lattices @ X1)
% 2.12/2.31          | (v2_struct_0 @ X1)
% 2.12/2.31          | ~ (l3_lattices @ X1)
% 2.12/2.31          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 2.12/2.31             (k15_lattice3 @ X1 @ X0))
% 2.12/2.31          | ~ (v6_lattices @ X1)
% 2.12/2.31          | ~ (v8_lattices @ X1)
% 2.12/2.31          | ~ (v9_lattices @ X1))),
% 2.12/2.31      inference('sup-', [status(thm)], ['12', '19'])).
% 2.12/2.31  thf('21', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (~ (v9_lattices @ X1)
% 2.12/2.31          | ~ (v8_lattices @ X1)
% 2.12/2.31          | ~ (v6_lattices @ X1)
% 2.12/2.31          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 2.12/2.31             (k15_lattice3 @ X1 @ X0))
% 2.12/2.31          | ~ (l3_lattices @ X1)
% 2.12/2.31          | ~ (v4_lattice3 @ X1)
% 2.12/2.31          | ~ (v10_lattices @ X1)
% 2.12/2.31          | (v2_struct_0 @ X1))),
% 2.12/2.31      inference('simplify', [status(thm)], ['20'])).
% 2.12/2.31  thf('22', plain,
% 2.12/2.31      (![X21 : $i, X22 : $i]:
% 2.12/2.31         (~ (l3_lattices @ X21)
% 2.12/2.31          | (v2_struct_0 @ X21)
% 2.12/2.31          | (m1_subset_1 @ (k15_lattice3 @ X21 @ X22) @ (u1_struct_0 @ X21)))),
% 2.12/2.31      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.12/2.31  thf(t21_lattices, axiom,
% 2.12/2.31    (![A:$i]:
% 2.12/2.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 2.12/2.31         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 2.12/2.31       ( ![B:$i]:
% 2.12/2.31         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.31           ( ![C:$i]:
% 2.12/2.31             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.31               ( ( r1_lattices @ A @ B @ C ) <=>
% 2.12/2.31                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 2.12/2.31  thf('23', plain,
% 2.12/2.31      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.12/2.31         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 2.12/2.31          | ~ (r1_lattices @ X13 @ X12 @ X14)
% 2.12/2.31          | ((k2_lattices @ X13 @ X12 @ X14) = (X12))
% 2.12/2.31          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 2.12/2.31          | ~ (l3_lattices @ X13)
% 2.12/2.31          | ~ (v9_lattices @ X13)
% 2.12/2.31          | ~ (v8_lattices @ X13)
% 2.12/2.31          | (v2_struct_0 @ X13))),
% 2.12/2.31      inference('cnf', [status(esa)], [t21_lattices])).
% 2.12/2.31  thf('24', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.12/2.31          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.12/2.31              = (k15_lattice3 @ X0 @ X1))
% 2.12/2.31          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 2.12/2.31      inference('sup-', [status(thm)], ['22', '23'])).
% 2.12/2.31  thf('25', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.31         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.12/2.31          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.12/2.31              = (k15_lattice3 @ X0 @ X1))
% 2.12/2.31          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.12/2.31          | ~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['24'])).
% 2.12/2.31  thf('26', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X1)
% 2.12/2.31          | ~ (v10_lattices @ X1)
% 2.12/2.31          | ~ (v4_lattice3 @ X1)
% 2.12/2.31          | ~ (l3_lattices @ X1)
% 2.12/2.31          | ~ (v6_lattices @ X1)
% 2.12/2.31          | ~ (v8_lattices @ X1)
% 2.12/2.31          | ~ (v9_lattices @ X1)
% 2.12/2.31          | (v2_struct_0 @ X1)
% 2.12/2.31          | ~ (l3_lattices @ X1)
% 2.12/2.31          | ~ (v8_lattices @ X1)
% 2.12/2.31          | ~ (v9_lattices @ X1)
% 2.12/2.31          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 2.12/2.31          | ((k2_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 2.12/2.31              (k15_lattice3 @ X1 @ X0)) = (k15_lattice3 @ X1 @ k1_xboole_0)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['21', '25'])).
% 2.12/2.31  thf('27', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (((k2_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 2.12/2.31            (k15_lattice3 @ X1 @ X0)) = (k15_lattice3 @ X1 @ k1_xboole_0))
% 2.12/2.31          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 2.12/2.31          | ~ (v9_lattices @ X1)
% 2.12/2.31          | ~ (v8_lattices @ X1)
% 2.12/2.31          | ~ (v6_lattices @ X1)
% 2.12/2.31          | ~ (l3_lattices @ X1)
% 2.12/2.31          | ~ (v4_lattice3 @ X1)
% 2.12/2.31          | ~ (v10_lattices @ X1)
% 2.12/2.31          | (v2_struct_0 @ X1))),
% 2.12/2.31      inference('simplify', [status(thm)], ['26'])).
% 2.12/2.31  thf('28', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v9_lattices @ X0)
% 2.12/2.31          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.31              (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['7', '27'])).
% 2.12/2.31  thf('29', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.31            (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.12/2.31          | ~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['28'])).
% 2.12/2.31  thf('30', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.31            (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.12/2.31            = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | (v13_lattices @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v9_lattices @ X0))),
% 2.12/2.31      inference('sup+', [status(thm)], ['6', '29'])).
% 2.12/2.31  thf('31', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | (v13_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.31              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.12/2.31              = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.12/2.31      inference('simplify', [status(thm)], ['30'])).
% 2.12/2.31  thf('32', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (((k15_lattice3 @ X0 @ 
% 2.12/2.31            (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 2.12/2.31             (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 2.12/2.31            = (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | (v13_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['5'])).
% 2.12/2.31  thf('33', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.31            (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.12/2.31          | ~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['28'])).
% 2.12/2.31  thf('34', plain,
% 2.12/2.31      (![X21 : $i, X22 : $i]:
% 2.12/2.31         (~ (l3_lattices @ X21)
% 2.12/2.31          | (v2_struct_0 @ X21)
% 2.12/2.31          | (m1_subset_1 @ (k15_lattice3 @ X21 @ X22) @ (u1_struct_0 @ X21)))),
% 2.12/2.31      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.12/2.31  thf('35', plain,
% 2.12/2.31      (![X21 : $i, X22 : $i]:
% 2.12/2.31         (~ (l3_lattices @ X21)
% 2.12/2.31          | (v2_struct_0 @ X21)
% 2.12/2.31          | (m1_subset_1 @ (k15_lattice3 @ X21 @ X22) @ (u1_struct_0 @ X21)))),
% 2.12/2.31      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.12/2.31  thf(d6_lattices, axiom,
% 2.12/2.31    (![A:$i]:
% 2.12/2.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 2.12/2.31       ( ( v6_lattices @ A ) <=>
% 2.12/2.31         ( ![B:$i]:
% 2.12/2.31           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.31             ( ![C:$i]:
% 2.12/2.31               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.31                 ( ( k2_lattices @ A @ B @ C ) = ( k2_lattices @ A @ C @ B ) ) ) ) ) ) ) ))).
% 2.12/2.31  thf('36', plain,
% 2.12/2.31      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.12/2.31         (~ (v6_lattices @ X18)
% 2.12/2.31          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 2.12/2.31          | ((k2_lattices @ X18 @ X20 @ X19) = (k2_lattices @ X18 @ X19 @ X20))
% 2.12/2.31          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 2.12/2.31          | ~ (l1_lattices @ X18)
% 2.12/2.31          | (v2_struct_0 @ X18))),
% 2.12/2.31      inference('cnf', [status(esa)], [d6_lattices])).
% 2.12/2.31  thf('37', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.12/2.31          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 2.12/2.31              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 2.12/2.31          | ~ (v6_lattices @ X0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['35', '36'])).
% 2.12/2.31  thf('38', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.31         (~ (v6_lattices @ X0)
% 2.12/2.31          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 2.12/2.31              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 2.12/2.31          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['37'])).
% 2.12/2.31  thf('39', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.12/2.31              (k15_lattice3 @ X0 @ X2))
% 2.12/2.31              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.12/2.31                 (k15_lattice3 @ X0 @ X1)))
% 2.12/2.31          | ~ (v6_lattices @ X0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['34', '38'])).
% 2.12/2.31  thf('40', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.31         (~ (v6_lattices @ X0)
% 2.12/2.31          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.12/2.31              (k15_lattice3 @ X0 @ X2))
% 2.12/2.31              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.12/2.31                 (k15_lattice3 @ X0 @ X1)))
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['39'])).
% 2.12/2.31  thf('41', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.12/2.31            = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.12/2.31               (k15_lattice3 @ X0 @ k1_xboole_0)))
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v9_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0))),
% 2.12/2.31      inference('sup+', [status(thm)], ['33', '40'])).
% 2.12/2.31  thf('42', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.12/2.31              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.12/2.31                 (k15_lattice3 @ X0 @ k1_xboole_0))))),
% 2.12/2.31      inference('simplify', [status(thm)], ['41'])).
% 2.12/2.31  thf('43', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.12/2.31            = (k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.12/2.31               (k15_lattice3 @ X0 @ k1_xboole_0)))
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | (v13_lattices @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0))),
% 2.12/2.31      inference('sup+', [status(thm)], ['32', '42'])).
% 2.12/2.31  thf('44', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | (v13_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.12/2.31              = (k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.12/2.31                 (k15_lattice3 @ X0 @ k1_xboole_0))))),
% 2.12/2.31      inference('simplify', [status(thm)], ['43'])).
% 2.12/2.31  thf('45', plain,
% 2.12/2.31      (![X21 : $i, X22 : $i]:
% 2.12/2.31         (~ (l3_lattices @ X21)
% 2.12/2.31          | (v2_struct_0 @ X21)
% 2.12/2.31          | (m1_subset_1 @ (k15_lattice3 @ X21 @ X22) @ (u1_struct_0 @ X21)))),
% 2.12/2.31      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.12/2.31  thf('46', plain,
% 2.12/2.31      (![X15 : $i, X16 : $i]:
% 2.12/2.31         (((k2_lattices @ X16 @ (sk_C_1 @ X15 @ X16) @ X15) != (X15))
% 2.12/2.31          | ((k2_lattices @ X16 @ X15 @ (sk_C_1 @ X15 @ X16)) != (X15))
% 2.12/2.31          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 2.12/2.31          | (v13_lattices @ X16)
% 2.12/2.31          | ~ (l1_lattices @ X16)
% 2.12/2.31          | (v2_struct_0 @ X16))),
% 2.12/2.31      inference('cnf', [status(esa)], [d13_lattices])).
% 2.12/2.31  thf('47', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | (v13_lattices @ X0)
% 2.12/2.31          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.12/2.31              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.12/2.31              != (k15_lattice3 @ X0 @ X1))
% 2.12/2.31          | ((k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.12/2.31              (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['45', '46'])).
% 2.12/2.31  thf('48', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (((k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.12/2.31            (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1))
% 2.12/2.31          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.12/2.31              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.12/2.31              != (k15_lattice3 @ X0 @ X1))
% 2.12/2.31          | (v13_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['47'])).
% 2.12/2.31  thf('49', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.12/2.31            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | (v13_lattices @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v9_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | (v13_lattices @ X0)
% 2.12/2.31          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.31              (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 2.12/2.31              != (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['44', '48'])).
% 2.12/2.31  thf('50', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.31            (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 2.12/2.31            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.12/2.31          | ~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | (v13_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['49'])).
% 2.12/2.31  thf('51', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.12/2.31            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | (v13_lattices @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v9_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | (v13_lattices @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v9_lattices @ X0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['31', '50'])).
% 2.12/2.31  thf('52', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         (~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | (v13_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['51'])).
% 2.12/2.31  thf(t50_lattice3, conjecture,
% 2.12/2.31    (![A:$i]:
% 2.12/2.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.12/2.31         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.12/2.31       ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.12/2.31         ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 2.12/2.31         ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ))).
% 2.12/2.31  thf(zf_stmt_0, negated_conjecture,
% 2.12/2.31    (~( ![A:$i]:
% 2.12/2.31        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.12/2.31            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.12/2.31          ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.12/2.31            ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 2.12/2.31            ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ) )),
% 2.12/2.31    inference('cnf.neg', [status(esa)], [t50_lattice3])).
% 2.12/2.31  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('54', plain,
% 2.12/2.31      ((~ (l3_lattices @ sk_A)
% 2.12/2.31        | ~ (l1_lattices @ sk_A)
% 2.12/2.31        | (v13_lattices @ sk_A)
% 2.12/2.31        | ~ (v10_lattices @ sk_A)
% 2.12/2.31        | ~ (v4_lattice3 @ sk_A)
% 2.12/2.31        | ~ (v6_lattices @ sk_A)
% 2.12/2.31        | ~ (v8_lattices @ sk_A)
% 2.12/2.31        | ~ (v9_lattices @ sk_A))),
% 2.12/2.31      inference('sup-', [status(thm)], ['52', '53'])).
% 2.12/2.31  thf('55', plain, ((l3_lattices @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('56', plain, ((l3_lattices @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf(dt_l3_lattices, axiom,
% 2.12/2.31    (![A:$i]:
% 2.12/2.31     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 2.12/2.31  thf('57', plain, (![X8 : $i]: ((l1_lattices @ X8) | ~ (l3_lattices @ X8))),
% 2.12/2.31      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 2.12/2.31  thf('58', plain, ((l1_lattices @ sk_A)),
% 2.12/2.31      inference('sup-', [status(thm)], ['56', '57'])).
% 2.12/2.31  thf('59', plain, ((v10_lattices @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('60', plain, ((v4_lattice3 @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf(cc1_lattices, axiom,
% 2.12/2.31    (![A:$i]:
% 2.12/2.31     ( ( l3_lattices @ A ) =>
% 2.12/2.31       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 2.12/2.31         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 2.12/2.31           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 2.12/2.31           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 2.12/2.31  thf('61', plain,
% 2.12/2.31      (![X3 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X3)
% 2.12/2.31          | ~ (v10_lattices @ X3)
% 2.12/2.31          | (v6_lattices @ X3)
% 2.12/2.31          | ~ (l3_lattices @ X3))),
% 2.12/2.31      inference('cnf', [status(esa)], [cc1_lattices])).
% 2.12/2.31  thf('62', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('63', plain,
% 2.12/2.31      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 2.12/2.31      inference('sup-', [status(thm)], ['61', '62'])).
% 2.12/2.31  thf('64', plain, ((l3_lattices @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('65', plain, ((v10_lattices @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('66', plain, ((v6_lattices @ sk_A)),
% 2.12/2.31      inference('demod', [status(thm)], ['63', '64', '65'])).
% 2.12/2.31  thf('67', plain,
% 2.12/2.31      (![X3 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X3)
% 2.12/2.31          | ~ (v10_lattices @ X3)
% 2.12/2.31          | (v8_lattices @ X3)
% 2.12/2.31          | ~ (l3_lattices @ X3))),
% 2.12/2.31      inference('cnf', [status(esa)], [cc1_lattices])).
% 2.12/2.31  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('69', plain,
% 2.12/2.31      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 2.12/2.31      inference('sup-', [status(thm)], ['67', '68'])).
% 2.12/2.31  thf('70', plain, ((l3_lattices @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('71', plain, ((v10_lattices @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('72', plain, ((v8_lattices @ sk_A)),
% 2.12/2.31      inference('demod', [status(thm)], ['69', '70', '71'])).
% 2.12/2.31  thf('73', plain,
% 2.12/2.31      (![X3 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X3)
% 2.12/2.31          | ~ (v10_lattices @ X3)
% 2.12/2.31          | (v9_lattices @ X3)
% 2.12/2.31          | ~ (l3_lattices @ X3))),
% 2.12/2.31      inference('cnf', [status(esa)], [cc1_lattices])).
% 2.12/2.31  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('75', plain,
% 2.12/2.31      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 2.12/2.31      inference('sup-', [status(thm)], ['73', '74'])).
% 2.12/2.31  thf('76', plain, ((l3_lattices @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('77', plain, ((v10_lattices @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('78', plain, ((v9_lattices @ sk_A)),
% 2.12/2.31      inference('demod', [status(thm)], ['75', '76', '77'])).
% 2.12/2.31  thf('79', plain, ((v13_lattices @ sk_A)),
% 2.12/2.31      inference('demod', [status(thm)],
% 2.12/2.31                ['54', '55', '58', '59', '60', '66', '72', '78'])).
% 2.12/2.31  thf('80', plain,
% 2.12/2.31      (![X21 : $i, X22 : $i]:
% 2.12/2.31         (~ (l3_lattices @ X21)
% 2.12/2.31          | (v2_struct_0 @ X21)
% 2.12/2.31          | (m1_subset_1 @ (k15_lattice3 @ X21 @ X22) @ (u1_struct_0 @ X21)))),
% 2.12/2.31      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.12/2.31  thf(dt_k5_lattices, axiom,
% 2.12/2.31    (![A:$i]:
% 2.12/2.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 2.12/2.31       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 2.12/2.31  thf('81', plain,
% 2.12/2.31      (![X7 : $i]:
% 2.12/2.31         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 2.12/2.31          | ~ (l1_lattices @ X7)
% 2.12/2.31          | (v2_struct_0 @ X7))),
% 2.12/2.31      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 2.12/2.31  thf(d16_lattices, axiom,
% 2.12/2.31    (![A:$i]:
% 2.12/2.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 2.12/2.31       ( ( v13_lattices @ A ) =>
% 2.12/2.31         ( ![B:$i]:
% 2.12/2.31           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.31             ( ( ( B ) = ( k5_lattices @ A ) ) <=>
% 2.12/2.31               ( ![C:$i]:
% 2.12/2.31                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.12/2.31                   ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 2.12/2.31                     ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 2.12/2.31  thf('82', plain,
% 2.12/2.31      (![X4 : $i, X5 : $i, X6 : $i]:
% 2.12/2.31         (~ (v13_lattices @ X4)
% 2.12/2.31          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 2.12/2.31          | ((X5) != (k5_lattices @ X4))
% 2.12/2.31          | ((k2_lattices @ X4 @ X6 @ X5) = (X5))
% 2.12/2.31          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 2.12/2.31          | ~ (l1_lattices @ X4)
% 2.12/2.31          | (v2_struct_0 @ X4))),
% 2.12/2.31      inference('cnf', [status(esa)], [d16_lattices])).
% 2.12/2.31  thf('83', plain,
% 2.12/2.31      (![X4 : $i, X6 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X4)
% 2.12/2.31          | ~ (l1_lattices @ X4)
% 2.12/2.31          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 2.12/2.31          | ((k2_lattices @ X4 @ X6 @ (k5_lattices @ X4)) = (k5_lattices @ X4))
% 2.12/2.31          | ~ (m1_subset_1 @ (k5_lattices @ X4) @ (u1_struct_0 @ X4))
% 2.12/2.31          | ~ (v13_lattices @ X4))),
% 2.12/2.31      inference('simplify', [status(thm)], ['82'])).
% 2.12/2.31  thf('84', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (v13_lattices @ X0)
% 2.12/2.31          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 2.12/2.31          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['81', '83'])).
% 2.12/2.31  thf('85', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 2.12/2.31          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 2.12/2.31          | ~ (v13_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['84'])).
% 2.12/2.31  thf('86', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (v13_lattices @ X0)
% 2.12/2.31          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.12/2.31              = (k5_lattices @ X0)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['80', '85'])).
% 2.12/2.31  thf('87', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.12/2.31            = (k5_lattices @ X0))
% 2.12/2.31          | ~ (v13_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['86'])).
% 2.12/2.31  thf('88', plain,
% 2.12/2.31      (![X7 : $i]:
% 2.12/2.31         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 2.12/2.31          | ~ (l1_lattices @ X7)
% 2.12/2.31          | (v2_struct_0 @ X7))),
% 2.12/2.31      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 2.12/2.31  thf('89', plain,
% 2.12/2.31      (![X7 : $i]:
% 2.12/2.31         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 2.12/2.31          | ~ (l1_lattices @ X7)
% 2.12/2.31          | (v2_struct_0 @ X7))),
% 2.12/2.31      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 2.12/2.31  thf('90', plain,
% 2.12/2.31      (![X23 : $i, X24 : $i]:
% 2.12/2.31         (~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X24))
% 2.12/2.31          | ((k15_lattice3 @ X24 @ (k6_domain_1 @ (u1_struct_0 @ X24) @ X23))
% 2.12/2.31              = (X23))
% 2.12/2.31          | ~ (l3_lattices @ X24)
% 2.12/2.31          | ~ (v4_lattice3 @ X24)
% 2.12/2.31          | ~ (v10_lattices @ X24)
% 2.12/2.31          | (v2_struct_0 @ X24))),
% 2.12/2.31      inference('cnf', [status(esa)], [t43_lattice3])).
% 2.12/2.31  thf('91', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ((k15_lattice3 @ X0 @ 
% 2.12/2.31              (k6_domain_1 @ (u1_struct_0 @ X0) @ (k5_lattices @ X0)))
% 2.12/2.31              = (k5_lattices @ X0)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['89', '90'])).
% 2.12/2.31  thf('92', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         (((k15_lattice3 @ X0 @ 
% 2.12/2.31            (k6_domain_1 @ (u1_struct_0 @ X0) @ (k5_lattices @ X0)))
% 2.12/2.31            = (k5_lattices @ X0))
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['91'])).
% 2.12/2.31  thf('93', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         ((r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.31           (k15_lattice3 @ X0 @ X1))
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['8', '11'])).
% 2.12/2.31  thf('94', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         ((r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.31           (k5_lattices @ X0))
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0))),
% 2.12/2.31      inference('sup+', [status(thm)], ['92', '93'])).
% 2.12/2.31  thf('95', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         (~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.31             (k5_lattices @ X0)))),
% 2.12/2.31      inference('simplify', [status(thm)], ['94'])).
% 2.12/2.31  thf('96', plain,
% 2.12/2.31      (![X7 : $i]:
% 2.12/2.31         ((m1_subset_1 @ (k5_lattices @ X7) @ (u1_struct_0 @ X7))
% 2.12/2.31          | ~ (l1_lattices @ X7)
% 2.12/2.31          | (v2_struct_0 @ X7))),
% 2.12/2.31      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 2.12/2.31  thf('97', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.31         (~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.12/2.31          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.12/2.31          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['16'])).
% 2.12/2.31  thf('98', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.12/2.31          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v9_lattices @ X0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['96', '97'])).
% 2.12/2.31  thf('99', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i]:
% 2.12/2.31         (~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.12/2.31          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['98'])).
% 2.12/2.31  thf('100', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.31             (k5_lattices @ X0))
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v9_lattices @ X0))),
% 2.12/2.31      inference('sup-', [status(thm)], ['95', '99'])).
% 2.12/2.31  thf('101', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         (~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.31             (k5_lattices @ X0))
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['100'])).
% 2.12/2.31  thf('102', plain,
% 2.12/2.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.12/2.31         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.12/2.31          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.12/2.31              = (k15_lattice3 @ X0 @ X1))
% 2.12/2.31          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.12/2.31          | ~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['24'])).
% 2.12/2.31  thf('103', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v9_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 2.12/2.31          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.31              (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['101', '102'])).
% 2.12/2.31  thf('104', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.31            (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.12/2.31          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 2.12/2.31          | ~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['103'])).
% 2.12/2.31  thf('105', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         ((v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v9_lattices @ X0)
% 2.12/2.31          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.31              (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.12/2.31      inference('sup-', [status(thm)], ['88', '104'])).
% 2.12/2.31  thf('106', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.12/2.31            (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.12/2.31          | ~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0))),
% 2.12/2.31      inference('simplify', [status(thm)], ['105'])).
% 2.12/2.31  thf('107', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         (((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (v13_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v9_lattices @ X0))),
% 2.12/2.31      inference('sup+', [status(thm)], ['87', '106'])).
% 2.12/2.31  thf('108', plain,
% 2.12/2.31      (![X0 : $i]:
% 2.12/2.31         (~ (v9_lattices @ X0)
% 2.12/2.31          | ~ (v8_lattices @ X0)
% 2.12/2.31          | ~ (v6_lattices @ X0)
% 2.12/2.31          | ~ (v4_lattice3 @ X0)
% 2.12/2.31          | ~ (v10_lattices @ X0)
% 2.12/2.31          | ~ (v13_lattices @ X0)
% 2.12/2.31          | ~ (l1_lattices @ X0)
% 2.12/2.31          | ~ (l3_lattices @ X0)
% 2.12/2.31          | (v2_struct_0 @ X0)
% 2.12/2.31          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.12/2.31      inference('simplify', [status(thm)], ['107'])).
% 2.12/2.31  thf('109', plain,
% 2.12/2.31      (((v2_struct_0 @ sk_A)
% 2.12/2.31        | ~ (v10_lattices @ sk_A)
% 2.12/2.31        | ~ (v13_lattices @ sk_A)
% 2.12/2.31        | ~ (l3_lattices @ sk_A)
% 2.12/2.31        | ((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('110', plain,
% 2.12/2.31      ((((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))
% 2.12/2.31         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.12/2.31      inference('split', [status(esa)], ['109'])).
% 2.12/2.31  thf('111', plain,
% 2.12/2.31      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 2.12/2.31         | (v2_struct_0 @ sk_A)
% 2.12/2.31         | ~ (l3_lattices @ sk_A)
% 2.12/2.31         | ~ (l1_lattices @ sk_A)
% 2.12/2.31         | ~ (v13_lattices @ sk_A)
% 2.12/2.31         | ~ (v10_lattices @ sk_A)
% 2.12/2.31         | ~ (v4_lattice3 @ sk_A)
% 2.12/2.31         | ~ (v6_lattices @ sk_A)
% 2.12/2.31         | ~ (v8_lattices @ sk_A)
% 2.12/2.31         | ~ (v9_lattices @ sk_A)))
% 2.12/2.31         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.12/2.31      inference('sup-', [status(thm)], ['108', '110'])).
% 2.12/2.31  thf('112', plain, ((l3_lattices @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('113', plain, ((l1_lattices @ sk_A)),
% 2.12/2.31      inference('sup-', [status(thm)], ['56', '57'])).
% 2.12/2.31  thf('114', plain, ((v10_lattices @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('115', plain, ((v4_lattice3 @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('116', plain, ((v6_lattices @ sk_A)),
% 2.12/2.31      inference('demod', [status(thm)], ['63', '64', '65'])).
% 2.12/2.31  thf('117', plain, ((v8_lattices @ sk_A)),
% 2.12/2.31      inference('demod', [status(thm)], ['69', '70', '71'])).
% 2.12/2.31  thf('118', plain, ((v9_lattices @ sk_A)),
% 2.12/2.31      inference('demod', [status(thm)], ['75', '76', '77'])).
% 2.12/2.31  thf('119', plain,
% 2.12/2.31      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 2.12/2.31         | (v2_struct_0 @ sk_A)
% 2.12/2.31         | ~ (v13_lattices @ sk_A)))
% 2.12/2.31         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.12/2.31      inference('demod', [status(thm)],
% 2.12/2.31                ['111', '112', '113', '114', '115', '116', '117', '118'])).
% 2.12/2.31  thf('120', plain,
% 2.12/2.31      (((~ (v13_lattices @ sk_A) | (v2_struct_0 @ sk_A)))
% 2.12/2.31         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.12/2.31      inference('simplify', [status(thm)], ['119'])).
% 2.12/2.31  thf('121', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('122', plain,
% 2.12/2.31      ((~ (v13_lattices @ sk_A))
% 2.12/2.31         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.12/2.31      inference('clc', [status(thm)], ['120', '121'])).
% 2.12/2.31  thf('123', plain,
% 2.12/2.31      (($false)
% 2.12/2.31         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.12/2.31      inference('sup-', [status(thm)], ['79', '122'])).
% 2.12/2.31  thf('124', plain, (((v2_struct_0 @ sk_A)) <= (((v2_struct_0 @ sk_A)))),
% 2.12/2.31      inference('split', [status(esa)], ['109'])).
% 2.12/2.31  thf('125', plain, (~ (v2_struct_0 @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('126', plain, (~ ((v2_struct_0 @ sk_A))),
% 2.12/2.31      inference('sup-', [status(thm)], ['124', '125'])).
% 2.12/2.31  thf('127', plain, ((l3_lattices @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('128', plain, ((~ (l3_lattices @ sk_A)) <= (~ ((l3_lattices @ sk_A)))),
% 2.12/2.31      inference('split', [status(esa)], ['109'])).
% 2.12/2.31  thf('129', plain, (((l3_lattices @ sk_A))),
% 2.12/2.31      inference('sup-', [status(thm)], ['127', '128'])).
% 2.12/2.31  thf('130', plain, ((v10_lattices @ sk_A)),
% 2.12/2.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.12/2.31  thf('131', plain, ((~ (v10_lattices @ sk_A)) <= (~ ((v10_lattices @ sk_A)))),
% 2.12/2.31      inference('split', [status(esa)], ['109'])).
% 2.12/2.31  thf('132', plain, (((v10_lattices @ sk_A))),
% 2.12/2.31      inference('sup-', [status(thm)], ['130', '131'])).
% 2.12/2.31  thf('133', plain, ((v13_lattices @ sk_A)),
% 2.12/2.31      inference('demod', [status(thm)],
% 2.12/2.31                ['54', '55', '58', '59', '60', '66', '72', '78'])).
% 2.12/2.31  thf('134', plain, ((~ (v13_lattices @ sk_A)) <= (~ ((v13_lattices @ sk_A)))),
% 2.12/2.31      inference('split', [status(esa)], ['109'])).
% 2.12/2.31  thf('135', plain, (((v13_lattices @ sk_A))),
% 2.12/2.31      inference('sup-', [status(thm)], ['133', '134'])).
% 2.12/2.31  thf('136', plain,
% 2.12/2.31      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))) | 
% 2.12/2.31       ~ ((v13_lattices @ sk_A)) | ~ ((v10_lattices @ sk_A)) | 
% 2.12/2.31       ~ ((l3_lattices @ sk_A)) | ((v2_struct_0 @ sk_A))),
% 2.12/2.31      inference('split', [status(esa)], ['109'])).
% 2.12/2.31  thf('137', plain,
% 2.12/2.31      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 2.12/2.31      inference('sat_resolution*', [status(thm)],
% 2.12/2.31                ['126', '129', '132', '135', '136'])).
% 2.12/2.31  thf('138', plain, ($false),
% 2.12/2.31      inference('simpl_trail', [status(thm)], ['123', '137'])).
% 2.12/2.31  
% 2.12/2.31  % SZS output end Refutation
% 2.12/2.31  
% 2.12/2.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
