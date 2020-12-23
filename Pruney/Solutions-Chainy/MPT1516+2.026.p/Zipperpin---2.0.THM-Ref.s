%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NR9GOHBGrw

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:38 EST 2020

% Result     : Theorem 3.56s
% Output     : Refutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 526 expanded)
%              Number of leaves         :   43 ( 164 expanded)
%              Depth                    :   24
%              Number of atoms          : 2488 (8705 expanded)
%              Number of equality atoms :   79 ( 282 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(a_2_4_lattice3_type,type,(
    a_2_4_lattice3: $i > $i > $i )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(a_2_3_lattice3_type,type,(
    a_2_3_lattice3: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X23 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ X17 @ X18 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( v13_lattices @ X18 )
      | ~ ( l1_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
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
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( X25
        = ( k15_lattice3 @ X26 @ ( a_2_3_lattice3 @ X26 @ X25 ) ) )
      | ~ ( l3_lattices @ X26 )
      | ~ ( v4_lattice3 @ X26 )
      | ~ ( v10_lattices @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X23 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

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

thf('8',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( r2_hidden @ ( sk_D @ X29 @ X30 @ X28 ) @ X30 )
      | ( r3_lattices @ X28 @ ( k15_lattice3 @ X28 @ X30 ) @ ( k15_lattice3 @ X28 @ X29 ) )
      | ~ ( l3_lattices @ X28 )
      | ~ ( v4_lattice3 @ X28 )
      | ~ ( v10_lattices @ X28 )
      | ( v2_struct_0 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t48_lattice3])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('10',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X23 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('15',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X23 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ),
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

thf('16',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l3_lattices @ X12 )
      | ~ ( v9_lattices @ X12 )
      | ~ ( v8_lattices @ X12 )
      | ~ ( v6_lattices @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ( r1_lattices @ X12 @ X11 @ X13 )
      | ~ ( r3_lattices @ X12 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('17',plain,(
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
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
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
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
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
    inference('sup-',[status(thm)],['13','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X1 )
      | ~ ( v8_lattices @ X1 )
      | ~ ( v6_lattices @ X1 )
      | ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X23 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ),
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

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( r1_lattices @ X15 @ X14 @ X16 )
      | ( ( k2_lattices @ X15 @ X14 @ X16 )
        = X14 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l3_lattices @ X15 )
      | ~ ( v9_lattices @ X15 )
      | ~ ( v8_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('25',plain,(
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
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
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
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
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
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
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
    inference('sup-',[status(thm)],['7','28'])).

thf('30',plain,(
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
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
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
    inference('sup+',[status(thm)],['6','30'])).

thf('32',plain,(
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
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
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

thf('34',plain,(
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
    inference(simplify,[status(thm)],['29'])).

thf('35',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X23 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X23 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ),
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

thf('37',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v6_lattices @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ( ( k2_lattices @ X20 @ X22 @ X21 )
        = ( k2_lattices @ X20 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l1_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d6_lattices])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ X2 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) ) )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ X2 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) ) )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
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
    inference('sup+',[status(thm)],['34','41'])).

thf('43',plain,(
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
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
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
    inference('sup+',[status(thm)],['33','43'])).

thf('45',plain,(
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
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X23 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('47',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k2_lattices @ X18 @ ( sk_C_1 @ X17 @ X18 ) @ X17 )
       != X17 )
      | ( ( k2_lattices @ X18 @ X17 @ ( sk_C_1 @ X17 @ X18 ) )
       != X17 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( v13_lattices @ X18 )
      | ~ ( l1_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d13_lattices])).

thf('48',plain,(
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
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
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
    inference('sup-',[status(thm)],['45','49'])).

thf('51',plain,(
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
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
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
    inference('sup-',[status(thm)],['32','51'])).

thf('53',plain,(
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
    inference(simplify,[status(thm)],['52'])).

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

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( v13_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('58',plain,(
    ! [X10: $i] :
      ( ( l1_lattices @ X10 )
      | ~ ( l3_lattices @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('59',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
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

thf('62',plain,(
    ! [X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v6_lattices @ X5 )
      | ~ ( l3_lattices @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('63',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v8_lattices @ X5 )
      | ~ ( l3_lattices @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('69',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ! [X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v9_lattices @ X5 )
      | ~ ( l3_lattices @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('75',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['55','56','59','60','61','67','73','79'])).

thf('81',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X23 @ X24 ) @ ( u1_struct_0 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(dt_k5_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('82',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
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

thf('83',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v13_lattices @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( X7
       != ( k5_lattices @ X6 ) )
      | ( ( k2_lattices @ X6 @ X8 @ X7 )
        = X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d16_lattices])).

thf('84',plain,(
    ! [X6: $i,X8: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_lattices @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ( ( k2_lattices @ X6 @ X8 @ ( k5_lattices @ X6 ) )
        = ( k5_lattices @ X6 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X6 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v13_lattices @ X6 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('90',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('91',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X26 ) )
      | ( X25
        = ( k15_lattice3 @ X26 @ ( a_2_3_lattice3 @ X26 @ X25 ) ) )
      | ~ ( l3_lattices @ X26 )
      | ~ ( v4_lattice3 @ X26 )
      | ~ ( v10_lattices @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t45_lattice3])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ ( a_2_3_lattice3 @ X0 @ ( k5_lattices @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ ( a_2_3_lattice3 @ X0 @ ( k5_lattices @ X0 ) ) ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('95',plain,(
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
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('99',plain,(
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
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
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
    inference('sup-',[status(thm)],['96','100'])).

thf('102',plain,(
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
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('104',plain,(
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
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
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
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
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
    inference('sup-',[status(thm)],['89','105'])).

thf('107',plain,(
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
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
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
    inference('sup+',[status(thm)],['88','107'])).

thf('109',plain,(
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
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['110'])).

thf('112',plain,
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
    inference('sup-',[status(thm)],['109','111'])).

thf('113',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['57','58'])).

thf('115',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('118',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('119',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('120',plain,
    ( ( ( ( k5_lattices @ sk_A )
       != ( k5_lattices @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v13_lattices @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['112','113','114','115','116','117','118','119'])).

thf('121',plain,
    ( ( ~ ( v13_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,
    ( $false
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','123'])).

thf('125',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['110'])).

thf('126',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ~ ( l3_lattices @ sk_A )
   <= ~ ( l3_lattices @ sk_A ) ),
    inference(split,[status(esa)],['110'])).

thf('130',plain,(
    l3_lattices @ sk_A ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ~ ( v10_lattices @ sk_A )
   <= ~ ( v10_lattices @ sk_A ) ),
    inference(split,[status(esa)],['110'])).

thf('133',plain,(
    v10_lattices @ sk_A ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['55','56','59','60','61','67','73','79'])).

thf('135',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ~ ( v13_lattices @ sk_A ) ),
    inference(split,[status(esa)],['110'])).

thf('136',plain,(
    v13_lattices @ sk_A ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['110'])).

thf('138',plain,(
    ( k5_lattices @ sk_A )
 != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ),
    inference('sat_resolution*',[status(thm)],['127','130','133','136','137'])).

thf('139',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['124','138'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NR9GOHBGrw
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 3.56/3.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.56/3.79  % Solved by: fo/fo7.sh
% 3.56/3.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.56/3.79  % done 1883 iterations in 3.316s
% 3.56/3.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.56/3.79  % SZS output start Refutation
% 3.56/3.79  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 3.56/3.79  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 3.56/3.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.56/3.79  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 3.56/3.79  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 3.56/3.79  thf(a_2_4_lattice3_type, type, a_2_4_lattice3: $i > $i > $i).
% 3.56/3.79  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 3.56/3.79  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 3.56/3.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.56/3.79  thf(a_2_3_lattice3_type, type, a_2_3_lattice3: $i > $i > $i).
% 3.56/3.79  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.56/3.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.56/3.79  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 3.56/3.79  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 3.56/3.79  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 3.56/3.79  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 3.56/3.79  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 3.56/3.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.56/3.79  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 3.56/3.79  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 3.56/3.79  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 3.56/3.79  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 3.56/3.79  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 3.56/3.79  thf(sk_A_type, type, sk_A: $i).
% 3.56/3.79  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 3.56/3.79  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 3.56/3.79  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 3.56/3.79  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 3.56/3.79  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 3.56/3.79  thf(dt_k15_lattice3, axiom,
% 3.56/3.79    (![A:$i,B:$i]:
% 3.56/3.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 3.56/3.79       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 3.56/3.79  thf('0', plain,
% 3.56/3.79      (![X23 : $i, X24 : $i]:
% 3.56/3.79         (~ (l3_lattices @ X23)
% 3.56/3.79          | (v2_struct_0 @ X23)
% 3.56/3.79          | (m1_subset_1 @ (k15_lattice3 @ X23 @ X24) @ (u1_struct_0 @ X23)))),
% 3.56/3.79      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 3.56/3.79  thf(d13_lattices, axiom,
% 3.56/3.79    (![A:$i]:
% 3.56/3.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 3.56/3.79       ( ( v13_lattices @ A ) <=>
% 3.56/3.79         ( ?[B:$i]:
% 3.56/3.79           ( ( ![C:$i]:
% 3.56/3.79               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 3.56/3.79                 ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 3.56/3.79                   ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) & 
% 3.56/3.79             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 3.56/3.79  thf('1', plain,
% 3.56/3.79      (![X17 : $i, X18 : $i]:
% 3.56/3.79         ((m1_subset_1 @ (sk_C_1 @ X17 @ X18) @ (u1_struct_0 @ X18))
% 3.56/3.79          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 3.56/3.79          | (v13_lattices @ X18)
% 3.56/3.79          | ~ (l1_lattices @ X18)
% 3.56/3.79          | (v2_struct_0 @ X18))),
% 3.56/3.79      inference('cnf', [status(esa)], [d13_lattices])).
% 3.56/3.79  thf('2', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | (v13_lattices @ X0)
% 3.56/3.79          | (m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 3.56/3.79             (u1_struct_0 @ X0)))),
% 3.56/3.79      inference('sup-', [status(thm)], ['0', '1'])).
% 3.56/3.79  thf('3', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         ((m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 3.56/3.79           (u1_struct_0 @ X0))
% 3.56/3.79          | (v13_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['2'])).
% 3.56/3.79  thf(t45_lattice3, axiom,
% 3.56/3.79    (![A:$i]:
% 3.56/3.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 3.56/3.79         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 3.56/3.79       ( ![B:$i]:
% 3.56/3.79         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.56/3.79           ( ( ( B ) = ( k15_lattice3 @ A @ ( a_2_3_lattice3 @ A @ B ) ) ) & 
% 3.56/3.79             ( ( B ) = ( k16_lattice3 @ A @ ( a_2_4_lattice3 @ A @ B ) ) ) ) ) ) ))).
% 3.56/3.79  thf('4', plain,
% 3.56/3.79      (![X25 : $i, X26 : $i]:
% 3.56/3.79         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 3.56/3.79          | ((X25) = (k15_lattice3 @ X26 @ (a_2_3_lattice3 @ X26 @ X25)))
% 3.56/3.79          | ~ (l3_lattices @ X26)
% 3.56/3.79          | ~ (v4_lattice3 @ X26)
% 3.56/3.79          | ~ (v10_lattices @ X26)
% 3.56/3.79          | (v2_struct_0 @ X26))),
% 3.56/3.79      inference('cnf', [status(esa)], [t45_lattice3])).
% 3.56/3.79  thf('5', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | (v13_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ((sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)
% 3.56/3.79              = (k15_lattice3 @ X0 @ 
% 3.56/3.79                 (a_2_3_lattice3 @ X0 @ 
% 3.56/3.79                  (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)))))),
% 3.56/3.79      inference('sup-', [status(thm)], ['3', '4'])).
% 3.56/3.79  thf('6', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         (((sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)
% 3.56/3.79            = (k15_lattice3 @ X0 @ 
% 3.56/3.79               (a_2_3_lattice3 @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))))
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | (v13_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['5'])).
% 3.56/3.79  thf('7', plain,
% 3.56/3.79      (![X23 : $i, X24 : $i]:
% 3.56/3.79         (~ (l3_lattices @ X23)
% 3.56/3.79          | (v2_struct_0 @ X23)
% 3.56/3.79          | (m1_subset_1 @ (k15_lattice3 @ X23 @ X24) @ (u1_struct_0 @ X23)))),
% 3.56/3.79      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 3.56/3.79  thf(t48_lattice3, axiom,
% 3.56/3.79    (![A:$i]:
% 3.56/3.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 3.56/3.79         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 3.56/3.79       ( ![B:$i,C:$i]:
% 3.56/3.79         ( ( ![D:$i]:
% 3.56/3.79             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 3.56/3.79               ( ~( ( r2_hidden @ D @ B ) & 
% 3.56/3.79                    ( ![E:$i]:
% 3.56/3.79                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 3.56/3.79                        ( ~( ( r3_lattices @ A @ D @ E ) & 
% 3.56/3.79                             ( r2_hidden @ E @ C ) ) ) ) ) ) ) ) ) =>
% 3.56/3.79           ( r3_lattices @
% 3.56/3.79             A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) ) ) ))).
% 3.56/3.79  thf('8', plain,
% 3.56/3.79      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.56/3.79         ((r2_hidden @ (sk_D @ X29 @ X30 @ X28) @ X30)
% 3.56/3.79          | (r3_lattices @ X28 @ (k15_lattice3 @ X28 @ X30) @ 
% 3.56/3.79             (k15_lattice3 @ X28 @ X29))
% 3.56/3.79          | ~ (l3_lattices @ X28)
% 3.56/3.79          | ~ (v4_lattice3 @ X28)
% 3.56/3.79          | ~ (v10_lattices @ X28)
% 3.56/3.79          | (v2_struct_0 @ X28))),
% 3.56/3.79      inference('cnf', [status(esa)], [t48_lattice3])).
% 3.56/3.79  thf(t113_zfmisc_1, axiom,
% 3.56/3.79    (![A:$i,B:$i]:
% 3.56/3.79     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.56/3.79       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.56/3.79  thf('9', plain,
% 3.56/3.79      (![X1 : $i, X2 : $i]:
% 3.56/3.79         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 3.56/3.79      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.56/3.79  thf('10', plain,
% 3.56/3.79      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['9'])).
% 3.56/3.79  thf(t152_zfmisc_1, axiom,
% 3.56/3.79    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 3.56/3.79  thf('11', plain,
% 3.56/3.79      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 3.56/3.79      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 3.56/3.79  thf('12', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.56/3.79      inference('sup-', [status(thm)], ['10', '11'])).
% 3.56/3.79  thf('13', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 3.56/3.79             (k15_lattice3 @ X0 @ X1)))),
% 3.56/3.79      inference('sup-', [status(thm)], ['8', '12'])).
% 3.56/3.79  thf('14', plain,
% 3.56/3.79      (![X23 : $i, X24 : $i]:
% 3.56/3.79         (~ (l3_lattices @ X23)
% 3.56/3.79          | (v2_struct_0 @ X23)
% 3.56/3.79          | (m1_subset_1 @ (k15_lattice3 @ X23 @ X24) @ (u1_struct_0 @ X23)))),
% 3.56/3.79      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 3.56/3.79  thf('15', plain,
% 3.56/3.79      (![X23 : $i, X24 : $i]:
% 3.56/3.79         (~ (l3_lattices @ X23)
% 3.56/3.79          | (v2_struct_0 @ X23)
% 3.56/3.79          | (m1_subset_1 @ (k15_lattice3 @ X23 @ X24) @ (u1_struct_0 @ X23)))),
% 3.56/3.79      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 3.56/3.79  thf(redefinition_r3_lattices, axiom,
% 3.56/3.79    (![A:$i,B:$i,C:$i]:
% 3.56/3.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 3.56/3.79         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 3.56/3.79         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 3.56/3.79         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 3.56/3.79       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 3.56/3.79  thf('16', plain,
% 3.56/3.79      (![X11 : $i, X12 : $i, X13 : $i]:
% 3.56/3.79         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 3.56/3.79          | ~ (l3_lattices @ X12)
% 3.56/3.79          | ~ (v9_lattices @ X12)
% 3.56/3.79          | ~ (v8_lattices @ X12)
% 3.56/3.79          | ~ (v6_lattices @ X12)
% 3.56/3.79          | (v2_struct_0 @ X12)
% 3.56/3.79          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 3.56/3.79          | (r1_lattices @ X12 @ X11 @ X13)
% 3.56/3.79          | ~ (r3_lattices @ X12 @ X11 @ X13))),
% 3.56/3.79      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 3.56/3.79  thf('17', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 3.56/3.79          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 3.56/3.79          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0))),
% 3.56/3.79      inference('sup-', [status(thm)], ['15', '16'])).
% 3.56/3.79  thf('18', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.56/3.79         (~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 3.56/3.79          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 3.56/3.79          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['17'])).
% 3.56/3.79  thf('19', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 3.56/3.79               (k15_lattice3 @ X0 @ X1))
% 3.56/3.79          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 3.56/3.79             (k15_lattice3 @ X0 @ X1))
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v9_lattices @ X0))),
% 3.56/3.79      inference('sup-', [status(thm)], ['14', '18'])).
% 3.56/3.79  thf('20', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.56/3.79         (~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 3.56/3.79             (k15_lattice3 @ X0 @ X1))
% 3.56/3.79          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 3.56/3.79               (k15_lattice3 @ X0 @ X1))
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['19'])).
% 3.56/3.79  thf('21', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         (~ (l3_lattices @ X1)
% 3.56/3.79          | ~ (v4_lattice3 @ X1)
% 3.56/3.79          | ~ (v10_lattices @ X1)
% 3.56/3.79          | (v2_struct_0 @ X1)
% 3.56/3.79          | (v2_struct_0 @ X1)
% 3.56/3.79          | ~ (l3_lattices @ X1)
% 3.56/3.79          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 3.56/3.79             (k15_lattice3 @ X1 @ X0))
% 3.56/3.79          | ~ (v6_lattices @ X1)
% 3.56/3.79          | ~ (v8_lattices @ X1)
% 3.56/3.79          | ~ (v9_lattices @ X1))),
% 3.56/3.79      inference('sup-', [status(thm)], ['13', '20'])).
% 3.56/3.79  thf('22', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         (~ (v9_lattices @ X1)
% 3.56/3.79          | ~ (v8_lattices @ X1)
% 3.56/3.79          | ~ (v6_lattices @ X1)
% 3.56/3.79          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 3.56/3.79             (k15_lattice3 @ X1 @ X0))
% 3.56/3.79          | (v2_struct_0 @ X1)
% 3.56/3.79          | ~ (v10_lattices @ X1)
% 3.56/3.79          | ~ (v4_lattice3 @ X1)
% 3.56/3.79          | ~ (l3_lattices @ X1))),
% 3.56/3.79      inference('simplify', [status(thm)], ['21'])).
% 3.56/3.79  thf('23', plain,
% 3.56/3.79      (![X23 : $i, X24 : $i]:
% 3.56/3.79         (~ (l3_lattices @ X23)
% 3.56/3.79          | (v2_struct_0 @ X23)
% 3.56/3.79          | (m1_subset_1 @ (k15_lattice3 @ X23 @ X24) @ (u1_struct_0 @ X23)))),
% 3.56/3.79      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 3.56/3.79  thf(t21_lattices, axiom,
% 3.56/3.79    (![A:$i]:
% 3.56/3.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 3.56/3.79         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 3.56/3.79       ( ![B:$i]:
% 3.56/3.79         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.56/3.79           ( ![C:$i]:
% 3.56/3.79             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 3.56/3.79               ( ( r1_lattices @ A @ B @ C ) <=>
% 3.56/3.79                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 3.56/3.79  thf('24', plain,
% 3.56/3.79      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.56/3.79         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 3.56/3.79          | ~ (r1_lattices @ X15 @ X14 @ X16)
% 3.56/3.79          | ((k2_lattices @ X15 @ X14 @ X16) = (X14))
% 3.56/3.79          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 3.56/3.79          | ~ (l3_lattices @ X15)
% 3.56/3.79          | ~ (v9_lattices @ X15)
% 3.56/3.79          | ~ (v8_lattices @ X15)
% 3.56/3.79          | (v2_struct_0 @ X15))),
% 3.56/3.79      inference('cnf', [status(esa)], [t21_lattices])).
% 3.56/3.79  thf('25', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 3.56/3.79          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 3.56/3.79              = (k15_lattice3 @ X0 @ X1))
% 3.56/3.79          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 3.56/3.79      inference('sup-', [status(thm)], ['23', '24'])).
% 3.56/3.79  thf('26', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.56/3.79         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 3.56/3.79          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 3.56/3.79              = (k15_lattice3 @ X0 @ X1))
% 3.56/3.79          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 3.56/3.79          | ~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['25'])).
% 3.56/3.79  thf('27', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         (~ (l3_lattices @ X1)
% 3.56/3.79          | ~ (v4_lattice3 @ X1)
% 3.56/3.79          | ~ (v10_lattices @ X1)
% 3.56/3.79          | (v2_struct_0 @ X1)
% 3.56/3.79          | ~ (v6_lattices @ X1)
% 3.56/3.79          | ~ (v8_lattices @ X1)
% 3.56/3.79          | ~ (v9_lattices @ X1)
% 3.56/3.79          | (v2_struct_0 @ X1)
% 3.56/3.79          | ~ (l3_lattices @ X1)
% 3.56/3.79          | ~ (v8_lattices @ X1)
% 3.56/3.79          | ~ (v9_lattices @ X1)
% 3.56/3.79          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 3.56/3.79          | ((k2_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 3.56/3.79              (k15_lattice3 @ X1 @ X0)) = (k15_lattice3 @ X1 @ k1_xboole_0)))),
% 3.56/3.79      inference('sup-', [status(thm)], ['22', '26'])).
% 3.56/3.79  thf('28', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         (((k2_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 3.56/3.79            (k15_lattice3 @ X1 @ X0)) = (k15_lattice3 @ X1 @ k1_xboole_0))
% 3.56/3.79          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 3.56/3.79          | ~ (v9_lattices @ X1)
% 3.56/3.79          | ~ (v8_lattices @ X1)
% 3.56/3.79          | ~ (v6_lattices @ X1)
% 3.56/3.79          | (v2_struct_0 @ X1)
% 3.56/3.79          | ~ (v10_lattices @ X1)
% 3.56/3.79          | ~ (v4_lattice3 @ X1)
% 3.56/3.79          | ~ (l3_lattices @ X1))),
% 3.56/3.79      inference('simplify', [status(thm)], ['27'])).
% 3.56/3.79  thf('29', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v9_lattices @ X0)
% 3.56/3.79          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 3.56/3.79              (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 3.56/3.79      inference('sup-', [status(thm)], ['7', '28'])).
% 3.56/3.79  thf('30', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 3.56/3.79            (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 3.56/3.79          | ~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['29'])).
% 3.56/3.79  thf('31', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 3.56/3.79            (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 3.56/3.79            = (k15_lattice3 @ X0 @ k1_xboole_0))
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | (v13_lattices @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v9_lattices @ X0))),
% 3.56/3.79      inference('sup+', [status(thm)], ['6', '30'])).
% 3.56/3.79  thf('32', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         (~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | (v13_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 3.56/3.79              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 3.56/3.79              = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 3.56/3.79      inference('simplify', [status(thm)], ['31'])).
% 3.56/3.79  thf('33', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         (((sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)
% 3.56/3.79            = (k15_lattice3 @ X0 @ 
% 3.56/3.79               (a_2_3_lattice3 @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))))
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | (v13_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['5'])).
% 3.56/3.79  thf('34', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 3.56/3.79            (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 3.56/3.79          | ~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['29'])).
% 3.56/3.79  thf('35', plain,
% 3.56/3.79      (![X23 : $i, X24 : $i]:
% 3.56/3.79         (~ (l3_lattices @ X23)
% 3.56/3.79          | (v2_struct_0 @ X23)
% 3.56/3.79          | (m1_subset_1 @ (k15_lattice3 @ X23 @ X24) @ (u1_struct_0 @ X23)))),
% 3.56/3.79      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 3.56/3.79  thf('36', plain,
% 3.56/3.79      (![X23 : $i, X24 : $i]:
% 3.56/3.79         (~ (l3_lattices @ X23)
% 3.56/3.79          | (v2_struct_0 @ X23)
% 3.56/3.79          | (m1_subset_1 @ (k15_lattice3 @ X23 @ X24) @ (u1_struct_0 @ X23)))),
% 3.56/3.79      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 3.56/3.79  thf(d6_lattices, axiom,
% 3.56/3.79    (![A:$i]:
% 3.56/3.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 3.56/3.79       ( ( v6_lattices @ A ) <=>
% 3.56/3.79         ( ![B:$i]:
% 3.56/3.79           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.56/3.79             ( ![C:$i]:
% 3.56/3.79               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 3.56/3.79                 ( ( k2_lattices @ A @ B @ C ) = ( k2_lattices @ A @ C @ B ) ) ) ) ) ) ) ))).
% 3.56/3.79  thf('37', plain,
% 3.56/3.79      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.56/3.79         (~ (v6_lattices @ X20)
% 3.56/3.79          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 3.56/3.79          | ((k2_lattices @ X20 @ X22 @ X21) = (k2_lattices @ X20 @ X21 @ X22))
% 3.56/3.79          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 3.56/3.79          | ~ (l1_lattices @ X20)
% 3.56/3.79          | (v2_struct_0 @ X20))),
% 3.56/3.79      inference('cnf', [status(esa)], [d6_lattices])).
% 3.56/3.79  thf('38', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 3.56/3.79          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 3.56/3.79              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 3.56/3.79          | ~ (v6_lattices @ X0))),
% 3.56/3.79      inference('sup-', [status(thm)], ['36', '37'])).
% 3.56/3.79  thf('39', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.56/3.79         (~ (v6_lattices @ X0)
% 3.56/3.79          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 3.56/3.79              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 3.56/3.79          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['38'])).
% 3.56/3.79  thf('40', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 3.56/3.79              (k15_lattice3 @ X0 @ X2))
% 3.56/3.79              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 3.56/3.79                 (k15_lattice3 @ X0 @ X1)))
% 3.56/3.79          | ~ (v6_lattices @ X0))),
% 3.56/3.79      inference('sup-', [status(thm)], ['35', '39'])).
% 3.56/3.79  thf('41', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.56/3.79         (~ (v6_lattices @ X0)
% 3.56/3.79          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 3.56/3.79              (k15_lattice3 @ X0 @ X2))
% 3.56/3.79              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 3.56/3.79                 (k15_lattice3 @ X0 @ X1)))
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['40'])).
% 3.56/3.79  thf('42', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 3.56/3.79            = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 3.56/3.79               (k15_lattice3 @ X0 @ k1_xboole_0)))
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v9_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0))),
% 3.56/3.79      inference('sup+', [status(thm)], ['34', '41'])).
% 3.56/3.79  thf('43', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         (~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 3.56/3.79              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 3.56/3.79                 (k15_lattice3 @ X0 @ k1_xboole_0))))),
% 3.56/3.79      inference('simplify', [status(thm)], ['42'])).
% 3.56/3.79  thf('44', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 3.56/3.79            = (k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 3.56/3.79               (k15_lattice3 @ X0 @ k1_xboole_0)))
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | (v13_lattices @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0))),
% 3.56/3.79      inference('sup+', [status(thm)], ['33', '43'])).
% 3.56/3.79  thf('45', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         (~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | (v13_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 3.56/3.79              = (k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 3.56/3.79                 (k15_lattice3 @ X0 @ k1_xboole_0))))),
% 3.56/3.79      inference('simplify', [status(thm)], ['44'])).
% 3.56/3.79  thf('46', plain,
% 3.56/3.79      (![X23 : $i, X24 : $i]:
% 3.56/3.79         (~ (l3_lattices @ X23)
% 3.56/3.79          | (v2_struct_0 @ X23)
% 3.56/3.79          | (m1_subset_1 @ (k15_lattice3 @ X23 @ X24) @ (u1_struct_0 @ X23)))),
% 3.56/3.79      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 3.56/3.79  thf('47', plain,
% 3.56/3.79      (![X17 : $i, X18 : $i]:
% 3.56/3.79         (((k2_lattices @ X18 @ (sk_C_1 @ X17 @ X18) @ X17) != (X17))
% 3.56/3.79          | ((k2_lattices @ X18 @ X17 @ (sk_C_1 @ X17 @ X18)) != (X17))
% 3.56/3.79          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 3.56/3.79          | (v13_lattices @ X18)
% 3.56/3.79          | ~ (l1_lattices @ X18)
% 3.56/3.79          | (v2_struct_0 @ X18))),
% 3.56/3.79      inference('cnf', [status(esa)], [d13_lattices])).
% 3.56/3.79  thf('48', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | (v13_lattices @ X0)
% 3.56/3.79          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 3.56/3.79              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 3.56/3.79              != (k15_lattice3 @ X0 @ X1))
% 3.56/3.79          | ((k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 3.56/3.79              (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1)))),
% 3.56/3.79      inference('sup-', [status(thm)], ['46', '47'])).
% 3.56/3.79  thf('49', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         (((k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 3.56/3.79            (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1))
% 3.56/3.79          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 3.56/3.79              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 3.56/3.79              != (k15_lattice3 @ X0 @ X1))
% 3.56/3.79          | (v13_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['48'])).
% 3.56/3.79  thf('50', plain,
% 3.56/3.79      (![X0 : $i]:
% 3.56/3.79         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 3.56/3.79            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | (v13_lattices @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v9_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | (v13_lattices @ X0)
% 3.56/3.79          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 3.56/3.79              (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 3.56/3.79              != (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 3.56/3.79      inference('sup-', [status(thm)], ['45', '49'])).
% 3.56/3.79  thf('51', plain,
% 3.56/3.79      (![X0 : $i]:
% 3.56/3.79         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 3.56/3.79            (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 3.56/3.79            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 3.56/3.79          | ~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | (v13_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['50'])).
% 3.56/3.79  thf('52', plain,
% 3.56/3.79      (![X0 : $i]:
% 3.56/3.79         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 3.56/3.79            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | (v13_lattices @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v9_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | (v13_lattices @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v9_lattices @ X0))),
% 3.56/3.79      inference('sup-', [status(thm)], ['32', '51'])).
% 3.56/3.79  thf('53', plain,
% 3.56/3.79      (![X0 : $i]:
% 3.56/3.79         (~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | (v13_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['52'])).
% 3.56/3.79  thf(t50_lattice3, conjecture,
% 3.56/3.79    (![A:$i]:
% 3.56/3.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 3.56/3.79         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 3.56/3.79       ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 3.56/3.79         ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 3.56/3.79         ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ))).
% 3.56/3.79  thf(zf_stmt_0, negated_conjecture,
% 3.56/3.79    (~( ![A:$i]:
% 3.56/3.79        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 3.56/3.79            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 3.56/3.79          ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 3.56/3.79            ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 3.56/3.79            ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ) )),
% 3.56/3.79    inference('cnf.neg', [status(esa)], [t50_lattice3])).
% 3.56/3.79  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf('55', plain,
% 3.56/3.79      ((~ (l3_lattices @ sk_A)
% 3.56/3.79        | ~ (l1_lattices @ sk_A)
% 3.56/3.79        | (v13_lattices @ sk_A)
% 3.56/3.79        | ~ (v10_lattices @ sk_A)
% 3.56/3.79        | ~ (v4_lattice3 @ sk_A)
% 3.56/3.79        | ~ (v6_lattices @ sk_A)
% 3.56/3.79        | ~ (v8_lattices @ sk_A)
% 3.56/3.79        | ~ (v9_lattices @ sk_A))),
% 3.56/3.79      inference('sup-', [status(thm)], ['53', '54'])).
% 3.56/3.79  thf('56', plain, ((l3_lattices @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf('57', plain, ((l3_lattices @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf(dt_l3_lattices, axiom,
% 3.56/3.79    (![A:$i]:
% 3.56/3.79     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 3.56/3.79  thf('58', plain,
% 3.56/3.79      (![X10 : $i]: ((l1_lattices @ X10) | ~ (l3_lattices @ X10))),
% 3.56/3.79      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 3.56/3.79  thf('59', plain, ((l1_lattices @ sk_A)),
% 3.56/3.79      inference('sup-', [status(thm)], ['57', '58'])).
% 3.56/3.79  thf('60', plain, ((v10_lattices @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf('61', plain, ((v4_lattice3 @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf(cc1_lattices, axiom,
% 3.56/3.79    (![A:$i]:
% 3.56/3.79     ( ( l3_lattices @ A ) =>
% 3.56/3.79       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 3.56/3.79         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 3.56/3.79           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 3.56/3.79           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 3.56/3.79  thf('62', plain,
% 3.56/3.79      (![X5 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X5)
% 3.56/3.79          | ~ (v10_lattices @ X5)
% 3.56/3.79          | (v6_lattices @ X5)
% 3.56/3.79          | ~ (l3_lattices @ X5))),
% 3.56/3.79      inference('cnf', [status(esa)], [cc1_lattices])).
% 3.56/3.79  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf('64', plain,
% 3.56/3.79      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 3.56/3.79      inference('sup-', [status(thm)], ['62', '63'])).
% 3.56/3.79  thf('65', plain, ((l3_lattices @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf('66', plain, ((v10_lattices @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf('67', plain, ((v6_lattices @ sk_A)),
% 3.56/3.79      inference('demod', [status(thm)], ['64', '65', '66'])).
% 3.56/3.79  thf('68', plain,
% 3.56/3.79      (![X5 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X5)
% 3.56/3.79          | ~ (v10_lattices @ X5)
% 3.56/3.79          | (v8_lattices @ X5)
% 3.56/3.79          | ~ (l3_lattices @ X5))),
% 3.56/3.79      inference('cnf', [status(esa)], [cc1_lattices])).
% 3.56/3.79  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf('70', plain,
% 3.56/3.79      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 3.56/3.79      inference('sup-', [status(thm)], ['68', '69'])).
% 3.56/3.79  thf('71', plain, ((l3_lattices @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf('72', plain, ((v10_lattices @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf('73', plain, ((v8_lattices @ sk_A)),
% 3.56/3.79      inference('demod', [status(thm)], ['70', '71', '72'])).
% 3.56/3.79  thf('74', plain,
% 3.56/3.79      (![X5 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X5)
% 3.56/3.79          | ~ (v10_lattices @ X5)
% 3.56/3.79          | (v9_lattices @ X5)
% 3.56/3.79          | ~ (l3_lattices @ X5))),
% 3.56/3.79      inference('cnf', [status(esa)], [cc1_lattices])).
% 3.56/3.79  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf('76', plain,
% 3.56/3.79      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 3.56/3.79      inference('sup-', [status(thm)], ['74', '75'])).
% 3.56/3.79  thf('77', plain, ((l3_lattices @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf('78', plain, ((v10_lattices @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf('79', plain, ((v9_lattices @ sk_A)),
% 3.56/3.79      inference('demod', [status(thm)], ['76', '77', '78'])).
% 3.56/3.79  thf('80', plain, ((v13_lattices @ sk_A)),
% 3.56/3.79      inference('demod', [status(thm)],
% 3.56/3.79                ['55', '56', '59', '60', '61', '67', '73', '79'])).
% 3.56/3.79  thf('81', plain,
% 3.56/3.79      (![X23 : $i, X24 : $i]:
% 3.56/3.79         (~ (l3_lattices @ X23)
% 3.56/3.79          | (v2_struct_0 @ X23)
% 3.56/3.79          | (m1_subset_1 @ (k15_lattice3 @ X23 @ X24) @ (u1_struct_0 @ X23)))),
% 3.56/3.79      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 3.56/3.79  thf(dt_k5_lattices, axiom,
% 3.56/3.79    (![A:$i]:
% 3.56/3.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 3.56/3.79       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 3.56/3.79  thf('82', plain,
% 3.56/3.79      (![X9 : $i]:
% 3.56/3.79         ((m1_subset_1 @ (k5_lattices @ X9) @ (u1_struct_0 @ X9))
% 3.56/3.79          | ~ (l1_lattices @ X9)
% 3.56/3.79          | (v2_struct_0 @ X9))),
% 3.56/3.79      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 3.56/3.79  thf(d16_lattices, axiom,
% 3.56/3.79    (![A:$i]:
% 3.56/3.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 3.56/3.79       ( ( v13_lattices @ A ) =>
% 3.56/3.79         ( ![B:$i]:
% 3.56/3.79           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 3.56/3.79             ( ( ( B ) = ( k5_lattices @ A ) ) <=>
% 3.56/3.79               ( ![C:$i]:
% 3.56/3.79                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 3.56/3.79                   ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 3.56/3.79                     ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 3.56/3.79  thf('83', plain,
% 3.56/3.79      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.56/3.79         (~ (v13_lattices @ X6)
% 3.56/3.79          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 3.56/3.79          | ((X7) != (k5_lattices @ X6))
% 3.56/3.79          | ((k2_lattices @ X6 @ X8 @ X7) = (X7))
% 3.56/3.79          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 3.56/3.79          | ~ (l1_lattices @ X6)
% 3.56/3.79          | (v2_struct_0 @ X6))),
% 3.56/3.79      inference('cnf', [status(esa)], [d16_lattices])).
% 3.56/3.79  thf('84', plain,
% 3.56/3.79      (![X6 : $i, X8 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X6)
% 3.56/3.79          | ~ (l1_lattices @ X6)
% 3.56/3.79          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 3.56/3.79          | ((k2_lattices @ X6 @ X8 @ (k5_lattices @ X6)) = (k5_lattices @ X6))
% 3.56/3.79          | ~ (m1_subset_1 @ (k5_lattices @ X6) @ (u1_struct_0 @ X6))
% 3.56/3.79          | ~ (v13_lattices @ X6))),
% 3.56/3.79      inference('simplify', [status(thm)], ['83'])).
% 3.56/3.79  thf('85', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (v13_lattices @ X0)
% 3.56/3.79          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 3.56/3.79          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('sup-', [status(thm)], ['82', '84'])).
% 3.56/3.79  thf('86', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 3.56/3.79          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 3.56/3.79          | ~ (v13_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['85'])).
% 3.56/3.79  thf('87', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (v13_lattices @ X0)
% 3.56/3.79          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 3.56/3.79              = (k5_lattices @ X0)))),
% 3.56/3.79      inference('sup-', [status(thm)], ['81', '86'])).
% 3.56/3.79  thf('88', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 3.56/3.79            = (k5_lattices @ X0))
% 3.56/3.79          | ~ (v13_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['87'])).
% 3.56/3.79  thf('89', plain,
% 3.56/3.79      (![X9 : $i]:
% 3.56/3.79         ((m1_subset_1 @ (k5_lattices @ X9) @ (u1_struct_0 @ X9))
% 3.56/3.79          | ~ (l1_lattices @ X9)
% 3.56/3.79          | (v2_struct_0 @ X9))),
% 3.56/3.79      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 3.56/3.79  thf('90', plain,
% 3.56/3.79      (![X9 : $i]:
% 3.56/3.79         ((m1_subset_1 @ (k5_lattices @ X9) @ (u1_struct_0 @ X9))
% 3.56/3.79          | ~ (l1_lattices @ X9)
% 3.56/3.79          | (v2_struct_0 @ X9))),
% 3.56/3.79      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 3.56/3.79  thf('91', plain,
% 3.56/3.79      (![X25 : $i, X26 : $i]:
% 3.56/3.79         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X26))
% 3.56/3.79          | ((X25) = (k15_lattice3 @ X26 @ (a_2_3_lattice3 @ X26 @ X25)))
% 3.56/3.79          | ~ (l3_lattices @ X26)
% 3.56/3.79          | ~ (v4_lattice3 @ X26)
% 3.56/3.79          | ~ (v10_lattices @ X26)
% 3.56/3.79          | (v2_struct_0 @ X26))),
% 3.56/3.79      inference('cnf', [status(esa)], [t45_lattice3])).
% 3.56/3.79  thf('92', plain,
% 3.56/3.79      (![X0 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ((k5_lattices @ X0)
% 3.56/3.79              = (k15_lattice3 @ X0 @ (a_2_3_lattice3 @ X0 @ (k5_lattices @ X0)))))),
% 3.56/3.79      inference('sup-', [status(thm)], ['90', '91'])).
% 3.56/3.79  thf('93', plain,
% 3.56/3.79      (![X0 : $i]:
% 3.56/3.79         (((k5_lattices @ X0)
% 3.56/3.79            = (k15_lattice3 @ X0 @ (a_2_3_lattice3 @ X0 @ (k5_lattices @ X0))))
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['92'])).
% 3.56/3.79  thf('94', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 3.56/3.79             (k15_lattice3 @ X0 @ X1)))),
% 3.56/3.79      inference('sup-', [status(thm)], ['8', '12'])).
% 3.56/3.79  thf('95', plain,
% 3.56/3.79      (![X0 : $i]:
% 3.56/3.79         ((r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 3.56/3.79           (k5_lattices @ X0))
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('sup+', [status(thm)], ['93', '94'])).
% 3.56/3.79  thf('96', plain,
% 3.56/3.79      (![X0 : $i]:
% 3.56/3.79         (~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 3.56/3.79             (k5_lattices @ X0)))),
% 3.56/3.79      inference('simplify', [status(thm)], ['95'])).
% 3.56/3.79  thf('97', plain,
% 3.56/3.79      (![X9 : $i]:
% 3.56/3.79         ((m1_subset_1 @ (k5_lattices @ X9) @ (u1_struct_0 @ X9))
% 3.56/3.79          | ~ (l1_lattices @ X9)
% 3.56/3.79          | (v2_struct_0 @ X9))),
% 3.56/3.79      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 3.56/3.79  thf('98', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.56/3.79         (~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 3.56/3.79          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 3.56/3.79          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['17'])).
% 3.56/3.79  thf('99', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 3.56/3.79          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v9_lattices @ X0))),
% 3.56/3.79      inference('sup-', [status(thm)], ['97', '98'])).
% 3.56/3.79  thf('100', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i]:
% 3.56/3.79         (~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 3.56/3.79          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['99'])).
% 3.56/3.79  thf('101', plain,
% 3.56/3.79      (![X0 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 3.56/3.79             (k5_lattices @ X0))
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v9_lattices @ X0))),
% 3.56/3.79      inference('sup-', [status(thm)], ['96', '100'])).
% 3.56/3.79  thf('102', plain,
% 3.56/3.79      (![X0 : $i]:
% 3.56/3.79         (~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 3.56/3.79             (k5_lattices @ X0))
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['101'])).
% 3.56/3.79  thf('103', plain,
% 3.56/3.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.56/3.79         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 3.56/3.79          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 3.56/3.79              = (k15_lattice3 @ X0 @ X1))
% 3.56/3.79          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 3.56/3.79          | ~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['25'])).
% 3.56/3.79  thf('104', plain,
% 3.56/3.79      (![X0 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v9_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 3.56/3.79          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 3.56/3.79              (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 3.56/3.79      inference('sup-', [status(thm)], ['102', '103'])).
% 3.56/3.79  thf('105', plain,
% 3.56/3.79      (![X0 : $i]:
% 3.56/3.79         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 3.56/3.79            (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 3.56/3.79          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 3.56/3.79          | ~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['104'])).
% 3.56/3.79  thf('106', plain,
% 3.56/3.79      (![X0 : $i]:
% 3.56/3.79         ((v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v9_lattices @ X0)
% 3.56/3.79          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 3.56/3.79              (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 3.56/3.79      inference('sup-', [status(thm)], ['89', '105'])).
% 3.56/3.79  thf('107', plain,
% 3.56/3.79      (![X0 : $i]:
% 3.56/3.79         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 3.56/3.79            (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 3.56/3.79          | ~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0))),
% 3.56/3.79      inference('simplify', [status(thm)], ['106'])).
% 3.56/3.79  thf('108', plain,
% 3.56/3.79      (![X0 : $i]:
% 3.56/3.79         (((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (v13_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v9_lattices @ X0))),
% 3.56/3.79      inference('sup+', [status(thm)], ['88', '107'])).
% 3.56/3.79  thf('109', plain,
% 3.56/3.79      (![X0 : $i]:
% 3.56/3.79         (~ (v9_lattices @ X0)
% 3.56/3.79          | ~ (v8_lattices @ X0)
% 3.56/3.79          | ~ (v6_lattices @ X0)
% 3.56/3.79          | ~ (v4_lattice3 @ X0)
% 3.56/3.79          | ~ (v10_lattices @ X0)
% 3.56/3.79          | ~ (v13_lattices @ X0)
% 3.56/3.79          | ~ (l1_lattices @ X0)
% 3.56/3.79          | ~ (l3_lattices @ X0)
% 3.56/3.79          | (v2_struct_0 @ X0)
% 3.56/3.79          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 3.56/3.79      inference('simplify', [status(thm)], ['108'])).
% 3.56/3.79  thf('110', plain,
% 3.56/3.79      (((v2_struct_0 @ sk_A)
% 3.56/3.79        | ~ (v10_lattices @ sk_A)
% 3.56/3.79        | ~ (v13_lattices @ sk_A)
% 3.56/3.79        | ~ (l3_lattices @ sk_A)
% 3.56/3.79        | ((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf('111', plain,
% 3.56/3.79      ((((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))
% 3.56/3.79         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 3.56/3.79      inference('split', [status(esa)], ['110'])).
% 3.56/3.79  thf('112', plain,
% 3.56/3.79      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 3.56/3.79         | (v2_struct_0 @ sk_A)
% 3.56/3.79         | ~ (l3_lattices @ sk_A)
% 3.56/3.79         | ~ (l1_lattices @ sk_A)
% 3.56/3.79         | ~ (v13_lattices @ sk_A)
% 3.56/3.79         | ~ (v10_lattices @ sk_A)
% 3.56/3.79         | ~ (v4_lattice3 @ sk_A)
% 3.56/3.79         | ~ (v6_lattices @ sk_A)
% 3.56/3.79         | ~ (v8_lattices @ sk_A)
% 3.56/3.79         | ~ (v9_lattices @ sk_A)))
% 3.56/3.79         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 3.56/3.79      inference('sup-', [status(thm)], ['109', '111'])).
% 3.56/3.79  thf('113', plain, ((l3_lattices @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf('114', plain, ((l1_lattices @ sk_A)),
% 3.56/3.79      inference('sup-', [status(thm)], ['57', '58'])).
% 3.56/3.79  thf('115', plain, ((v10_lattices @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf('116', plain, ((v4_lattice3 @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf('117', plain, ((v6_lattices @ sk_A)),
% 3.56/3.79      inference('demod', [status(thm)], ['64', '65', '66'])).
% 3.56/3.79  thf('118', plain, ((v8_lattices @ sk_A)),
% 3.56/3.79      inference('demod', [status(thm)], ['70', '71', '72'])).
% 3.56/3.79  thf('119', plain, ((v9_lattices @ sk_A)),
% 3.56/3.79      inference('demod', [status(thm)], ['76', '77', '78'])).
% 3.56/3.79  thf('120', plain,
% 3.56/3.79      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 3.56/3.79         | (v2_struct_0 @ sk_A)
% 3.56/3.79         | ~ (v13_lattices @ sk_A)))
% 3.56/3.79         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 3.56/3.79      inference('demod', [status(thm)],
% 3.56/3.79                ['112', '113', '114', '115', '116', '117', '118', '119'])).
% 3.56/3.79  thf('121', plain,
% 3.56/3.79      (((~ (v13_lattices @ sk_A) | (v2_struct_0 @ sk_A)))
% 3.56/3.79         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 3.56/3.79      inference('simplify', [status(thm)], ['120'])).
% 3.56/3.79  thf('122', plain, (~ (v2_struct_0 @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf('123', plain,
% 3.56/3.79      ((~ (v13_lattices @ sk_A))
% 3.56/3.79         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 3.56/3.79      inference('clc', [status(thm)], ['121', '122'])).
% 3.56/3.79  thf('124', plain,
% 3.56/3.79      (($false)
% 3.56/3.79         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 3.56/3.79      inference('sup-', [status(thm)], ['80', '123'])).
% 3.56/3.79  thf('125', plain, (((v2_struct_0 @ sk_A)) <= (((v2_struct_0 @ sk_A)))),
% 3.56/3.79      inference('split', [status(esa)], ['110'])).
% 3.56/3.79  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf('127', plain, (~ ((v2_struct_0 @ sk_A))),
% 3.56/3.79      inference('sup-', [status(thm)], ['125', '126'])).
% 3.56/3.79  thf('128', plain, ((l3_lattices @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf('129', plain, ((~ (l3_lattices @ sk_A)) <= (~ ((l3_lattices @ sk_A)))),
% 3.56/3.79      inference('split', [status(esa)], ['110'])).
% 3.56/3.79  thf('130', plain, (((l3_lattices @ sk_A))),
% 3.56/3.79      inference('sup-', [status(thm)], ['128', '129'])).
% 3.56/3.79  thf('131', plain, ((v10_lattices @ sk_A)),
% 3.56/3.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.56/3.79  thf('132', plain, ((~ (v10_lattices @ sk_A)) <= (~ ((v10_lattices @ sk_A)))),
% 3.56/3.79      inference('split', [status(esa)], ['110'])).
% 3.56/3.79  thf('133', plain, (((v10_lattices @ sk_A))),
% 3.56/3.79      inference('sup-', [status(thm)], ['131', '132'])).
% 3.56/3.79  thf('134', plain, ((v13_lattices @ sk_A)),
% 3.56/3.79      inference('demod', [status(thm)],
% 3.56/3.79                ['55', '56', '59', '60', '61', '67', '73', '79'])).
% 3.56/3.79  thf('135', plain, ((~ (v13_lattices @ sk_A)) <= (~ ((v13_lattices @ sk_A)))),
% 3.56/3.79      inference('split', [status(esa)], ['110'])).
% 3.56/3.79  thf('136', plain, (((v13_lattices @ sk_A))),
% 3.56/3.79      inference('sup-', [status(thm)], ['134', '135'])).
% 3.56/3.79  thf('137', plain,
% 3.56/3.79      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))) | 
% 3.56/3.79       ~ ((v13_lattices @ sk_A)) | ~ ((v10_lattices @ sk_A)) | 
% 3.56/3.79       ~ ((l3_lattices @ sk_A)) | ((v2_struct_0 @ sk_A))),
% 3.56/3.79      inference('split', [status(esa)], ['110'])).
% 3.56/3.79  thf('138', plain,
% 3.56/3.79      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 3.56/3.79      inference('sat_resolution*', [status(thm)],
% 3.56/3.79                ['127', '130', '133', '136', '137'])).
% 3.56/3.79  thf('139', plain, ($false),
% 3.56/3.79      inference('simpl_trail', [status(thm)], ['124', '138'])).
% 3.56/3.79  
% 3.56/3.79  % SZS output end Refutation
% 3.56/3.79  
% 3.56/3.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
