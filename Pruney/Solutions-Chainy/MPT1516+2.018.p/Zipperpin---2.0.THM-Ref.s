%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MbYOka7bFA

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:36 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :  170 ( 431 expanded)
%              Number of leaves         :   39 ( 136 expanded)
%              Depth                    :   20
%              Number of atoms          : 2157 (6788 expanded)
%              Number of equality atoms :   65 ( 225 expanded)
%              Maximal formula depth    :   21 (   8 average)

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

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

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

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l3_lattices @ X29 )
      | ( v2_struct_0 @ X29 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) ),
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

thf('4',plain,(
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

thf('5',plain,(
    ! [X17: $i,X18: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ ( sk_D @ X21 @ X17 @ X18 ) @ X21 )
      | ( r4_lattice3 @ X18 @ X17 @ X21 )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('9',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('14',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l3_lattices @ X29 )
      | ( v2_struct_0 @ X29 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) ),
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

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( v2_struct_0 @ X22 )
      | ~ ( v10_lattices @ X22 )
      | ~ ( v4_lattice3 @ X22 )
      | ~ ( l3_lattices @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X22 ) )
      | ( X23
       != ( k15_lattice3 @ X22 @ X24 ) )
      | ~ ( r4_lattice3 @ X22 @ X25 @ X24 )
      | ( r1_lattices @ X22 @ X23 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X22 ) )
      | ~ ( l3_lattices @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('16',plain,(
    ! [X22: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X22 ) )
      | ( r1_lattices @ X22 @ ( k15_lattice3 @ X22 @ X24 ) @ X25 )
      | ~ ( r4_lattice3 @ X22 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X22 @ X24 ) @ ( u1_struct_0 @ X22 ) )
      | ~ ( l3_lattices @ X22 )
      | ~ ( v4_lattice3 @ X22 )
      | ~ ( v10_lattices @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
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
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
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
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l3_lattices @ X29 )
      | ( v2_struct_0 @ X29 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) ),
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
      ( ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['3','28'])).

thf('30',plain,(
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
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('32',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l3_lattices @ X29 )
      | ( v2_struct_0 @ X29 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) ),
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

thf('33',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v6_lattices @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ( ( k2_lattices @ X26 @ X28 @ X27 )
        = ( k2_lattices @ X26 @ X27 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l1_lattices @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d6_lattices])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
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
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X2 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l3_lattices @ X29 )
      | ( v2_struct_0 @ X29 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('39',plain,(
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

thf('40',plain,(
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
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
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
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
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
    inference('sup-',[status(thm)],['30','43'])).

thf('45',plain,(
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
    inference(simplify,[status(thm)],['44'])).

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

thf('46',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( v13_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( v6_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('50',plain,(
    ! [X10: $i] :
      ( ( l1_lattices @ X10 )
      | ~ ( l3_lattices @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('51',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
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

thf('54',plain,(
    ! [X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v8_lattices @ X5 )
      | ~ ( l3_lattices @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('55',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,(
    ! [X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v9_lattices @ X5 )
      | ~ ( l3_lattices @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('66',plain,(
    ! [X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v6_lattices @ X5 )
      | ~ ( l3_lattices @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['47','48','51','52','53','59','65','71'])).

thf('73',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( l3_lattices @ X29 )
      | ( v2_struct_0 @ X29 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X29 @ X30 ) @ ( u1_struct_0 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(dt_k5_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('74',plain,(
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

thf('75',plain,(
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

thf('76',plain,(
    ! [X6: $i,X8: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_lattices @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ( ( k2_lattices @ X6 @ X8 @ ( k5_lattices @ X6 ) )
        = ( k5_lattices @ X6 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X6 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v13_lattices @ X6 ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('82',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('83',plain,(
    ! [X17: $i,X18: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ ( sk_D @ X21 @ X17 @ X18 ) @ X21 )
      | ( r4_lattice3 @ X18 @ X17 @ X21 )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
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
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['87','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
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

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['81','96'])).

thf('98',plain,(
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
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
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
    inference('sup+',[status(thm)],['80','98'])).

thf('100',plain,(
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
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['101'])).

thf('103',plain,
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
    inference('sup-',[status(thm)],['100','102'])).

thf('104',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf('106',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('109',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['62','63','64'])).

thf('110',plain,
    ( ( ( ( k5_lattices @ sk_A )
       != ( k5_lattices @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v13_lattices @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['103','104','105','106','107','108','109'])).

thf('111',plain,
    ( ( ~ ( v13_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,
    ( $false
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','113'])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['101'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ~ ( l3_lattices @ sk_A )
   <= ~ ( l3_lattices @ sk_A ) ),
    inference(split,[status(esa)],['101'])).

thf('120',plain,(
    l3_lattices @ sk_A ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ~ ( v10_lattices @ sk_A )
   <= ~ ( v10_lattices @ sk_A ) ),
    inference(split,[status(esa)],['101'])).

thf('123',plain,(
    v10_lattices @ sk_A ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['47','48','51','52','53','59','65','71'])).

thf('125',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ~ ( v13_lattices @ sk_A ) ),
    inference(split,[status(esa)],['101'])).

thf('126',plain,(
    v13_lattices @ sk_A ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['101'])).

thf('128',plain,(
    ( k5_lattices @ sk_A )
 != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ),
    inference('sat_resolution*',[status(thm)],['117','120','123','126','127'])).

thf('129',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['114','128'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.MbYOka7bFA
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:35:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.94/2.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.94/2.16  % Solved by: fo/fo7.sh
% 1.94/2.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.94/2.16  % done 1484 iterations in 1.702s
% 1.94/2.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.94/2.16  % SZS output start Refutation
% 1.94/2.16  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.94/2.16  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 1.94/2.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.94/2.16  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 1.94/2.16  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.94/2.16  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 1.94/2.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.94/2.16  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.94/2.16  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.94/2.16  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 1.94/2.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.94/2.16  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 1.94/2.16  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 1.94/2.16  thf(sk_A_type, type, sk_A: $i).
% 1.94/2.16  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 1.94/2.16  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 1.94/2.16  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.94/2.16  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 1.94/2.16  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 1.94/2.16  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 1.94/2.16  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 1.94/2.16  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 1.94/2.16  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 1.94/2.16  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 1.94/2.16  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 1.94/2.16  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 1.94/2.16  thf(dt_k15_lattice3, axiom,
% 1.94/2.16    (![A:$i,B:$i]:
% 1.94/2.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 1.94/2.16       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 1.94/2.16  thf('0', plain,
% 1.94/2.16      (![X29 : $i, X30 : $i]:
% 1.94/2.16         (~ (l3_lattices @ X29)
% 1.94/2.16          | (v2_struct_0 @ X29)
% 1.94/2.16          | (m1_subset_1 @ (k15_lattice3 @ X29 @ X30) @ (u1_struct_0 @ X29)))),
% 1.94/2.16      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 1.94/2.16  thf(d13_lattices, axiom,
% 1.94/2.16    (![A:$i]:
% 1.94/2.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 1.94/2.16       ( ( v13_lattices @ A ) <=>
% 1.94/2.16         ( ?[B:$i]:
% 1.94/2.16           ( ( ![C:$i]:
% 1.94/2.16               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.94/2.16                 ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 1.94/2.16                   ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) & 
% 1.94/2.16             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 1.94/2.16  thf('1', plain,
% 1.94/2.16      (![X14 : $i, X15 : $i]:
% 1.94/2.16         ((m1_subset_1 @ (sk_C_1 @ X14 @ X15) @ (u1_struct_0 @ X15))
% 1.94/2.16          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 1.94/2.16          | (v13_lattices @ X15)
% 1.94/2.16          | ~ (l1_lattices @ X15)
% 1.94/2.16          | (v2_struct_0 @ X15))),
% 1.94/2.16      inference('cnf', [status(esa)], [d13_lattices])).
% 1.94/2.16  thf('2', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | (m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.94/2.16             (u1_struct_0 @ X0)))),
% 1.94/2.16      inference('sup-', [status(thm)], ['0', '1'])).
% 1.94/2.16  thf('3', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         ((m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.94/2.16           (u1_struct_0 @ X0))
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['2'])).
% 1.94/2.16  thf('4', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         ((m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.94/2.16           (u1_struct_0 @ X0))
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['2'])).
% 1.94/2.16  thf(d17_lattice3, axiom,
% 1.94/2.16    (![A:$i]:
% 1.94/2.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 1.94/2.16       ( ![B:$i]:
% 1.94/2.16         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.94/2.16           ( ![C:$i]:
% 1.94/2.16             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 1.94/2.16               ( ![D:$i]:
% 1.94/2.16                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.94/2.16                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 1.94/2.16  thf('5', plain,
% 1.94/2.16      (![X17 : $i, X18 : $i, X21 : $i]:
% 1.94/2.16         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 1.94/2.16          | (r2_hidden @ (sk_D @ X21 @ X17 @ X18) @ X21)
% 1.94/2.16          | (r4_lattice3 @ X18 @ X17 @ X21)
% 1.94/2.16          | ~ (l3_lattices @ X18)
% 1.94/2.16          | (v2_struct_0 @ X18))),
% 1.94/2.16      inference('cnf', [status(esa)], [d17_lattice3])).
% 1.94/2.16  thf('6', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (r4_lattice3 @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 1.94/2.16          | (r2_hidden @ 
% 1.94/2.16             (sk_D @ X2 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X0) @ X2))),
% 1.94/2.16      inference('sup-', [status(thm)], ['4', '5'])).
% 1.94/2.16  thf('7', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.16         ((r2_hidden @ 
% 1.94/2.16           (sk_D @ X2 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X0) @ X2)
% 1.94/2.16          | (r4_lattice3 @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['6'])).
% 1.94/2.16  thf(t113_zfmisc_1, axiom,
% 1.94/2.16    (![A:$i,B:$i]:
% 1.94/2.16     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.94/2.16       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.94/2.16  thf('8', plain,
% 1.94/2.16      (![X1 : $i, X2 : $i]:
% 1.94/2.16         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 1.94/2.16      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.94/2.16  thf('9', plain,
% 1.94/2.16      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['8'])).
% 1.94/2.16  thf(t152_zfmisc_1, axiom,
% 1.94/2.16    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 1.94/2.16  thf('10', plain,
% 1.94/2.16      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 1.94/2.16      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 1.94/2.16  thf('11', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.94/2.16      inference('sup-', [status(thm)], ['9', '10'])).
% 1.94/2.16  thf('12', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | (r4_lattice3 @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.94/2.16             k1_xboole_0))),
% 1.94/2.16      inference('sup-', [status(thm)], ['7', '11'])).
% 1.94/2.16  thf('13', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         ((m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.94/2.16           (u1_struct_0 @ X0))
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['2'])).
% 1.94/2.16  thf('14', plain,
% 1.94/2.16      (![X29 : $i, X30 : $i]:
% 1.94/2.16         (~ (l3_lattices @ X29)
% 1.94/2.16          | (v2_struct_0 @ X29)
% 1.94/2.16          | (m1_subset_1 @ (k15_lattice3 @ X29 @ X30) @ (u1_struct_0 @ X29)))),
% 1.94/2.16      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 1.94/2.16  thf(d21_lattice3, axiom,
% 1.94/2.16    (![A:$i]:
% 1.94/2.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 1.94/2.16       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 1.94/2.16           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 1.94/2.16         ( ![B:$i,C:$i]:
% 1.94/2.16           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.94/2.16             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 1.94/2.16               ( ( r4_lattice3 @ A @ C @ B ) & 
% 1.94/2.16                 ( ![D:$i]:
% 1.94/2.16                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 1.94/2.16                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 1.94/2.16                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 1.94/2.16  thf('15', plain,
% 1.94/2.16      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X22)
% 1.94/2.16          | ~ (v10_lattices @ X22)
% 1.94/2.16          | ~ (v4_lattice3 @ X22)
% 1.94/2.16          | ~ (l3_lattices @ X22)
% 1.94/2.16          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X22))
% 1.94/2.16          | ((X23) != (k15_lattice3 @ X22 @ X24))
% 1.94/2.16          | ~ (r4_lattice3 @ X22 @ X25 @ X24)
% 1.94/2.16          | (r1_lattices @ X22 @ X23 @ X25)
% 1.94/2.16          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X22))
% 1.94/2.16          | ~ (l3_lattices @ X22)
% 1.94/2.16          | (v2_struct_0 @ X22))),
% 1.94/2.16      inference('cnf', [status(esa)], [d21_lattice3])).
% 1.94/2.16  thf('16', plain,
% 1.94/2.16      (![X22 : $i, X24 : $i, X25 : $i]:
% 1.94/2.16         (~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X22))
% 1.94/2.16          | (r1_lattices @ X22 @ (k15_lattice3 @ X22 @ X24) @ X25)
% 1.94/2.16          | ~ (r4_lattice3 @ X22 @ X25 @ X24)
% 1.94/2.16          | ~ (m1_subset_1 @ (k15_lattice3 @ X22 @ X24) @ (u1_struct_0 @ X22))
% 1.94/2.16          | ~ (l3_lattices @ X22)
% 1.94/2.16          | ~ (v4_lattice3 @ X22)
% 1.94/2.16          | ~ (v10_lattices @ X22)
% 1.94/2.16          | (v2_struct_0 @ X22))),
% 1.94/2.16      inference('simplify', [status(thm)], ['15'])).
% 1.94/2.16  thf('17', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 1.94/2.16          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.94/2.16          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 1.94/2.16      inference('sup-', [status(thm)], ['14', '16'])).
% 1.94/2.16  thf('18', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.16         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.94/2.16          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.94/2.16          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['17'])).
% 1.94/2.16  thf('19', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | ~ (r4_lattice3 @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 1.94/2.16          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 1.94/2.16             (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)))),
% 1.94/2.16      inference('sup-', [status(thm)], ['13', '18'])).
% 1.94/2.16  thf('20', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.16         ((r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 1.94/2.16           (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 1.94/2.16          | ~ (r4_lattice3 @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['19'])).
% 1.94/2.16  thf('21', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         ((v13_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 1.94/2.16             (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)))),
% 1.94/2.16      inference('sup-', [status(thm)], ['12', '20'])).
% 1.94/2.16  thf('22', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         ((r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 1.94/2.16           (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v13_lattices @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['21'])).
% 1.94/2.16  thf('23', plain,
% 1.94/2.16      (![X29 : $i, X30 : $i]:
% 1.94/2.16         (~ (l3_lattices @ X29)
% 1.94/2.16          | (v2_struct_0 @ X29)
% 1.94/2.16          | (m1_subset_1 @ (k15_lattice3 @ X29 @ X30) @ (u1_struct_0 @ X29)))),
% 1.94/2.16      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 1.94/2.16  thf(t21_lattices, axiom,
% 1.94/2.16    (![A:$i]:
% 1.94/2.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 1.94/2.16         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 1.94/2.16       ( ![B:$i]:
% 1.94/2.16         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.94/2.16           ( ![C:$i]:
% 1.94/2.16             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.94/2.16               ( ( r1_lattices @ A @ B @ C ) <=>
% 1.94/2.16                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 1.94/2.16  thf('24', plain,
% 1.94/2.16      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.94/2.16         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 1.94/2.16          | ~ (r1_lattices @ X12 @ X11 @ X13)
% 1.94/2.16          | ((k2_lattices @ X12 @ X11 @ X13) = (X11))
% 1.94/2.16          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 1.94/2.16          | ~ (l3_lattices @ X12)
% 1.94/2.16          | ~ (v9_lattices @ X12)
% 1.94/2.16          | ~ (v8_lattices @ X12)
% 1.94/2.16          | (v2_struct_0 @ X12))),
% 1.94/2.16      inference('cnf', [status(esa)], [t21_lattices])).
% 1.94/2.16  thf('25', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (v8_lattices @ X0)
% 1.94/2.16          | ~ (v9_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.94/2.16          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.94/2.16              = (k15_lattice3 @ X0 @ X1))
% 1.94/2.16          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 1.94/2.16      inference('sup-', [status(thm)], ['23', '24'])).
% 1.94/2.16  thf('26', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.16         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.94/2.16          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.94/2.16              = (k15_lattice3 @ X0 @ X1))
% 1.94/2.16          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.94/2.16          | ~ (v9_lattices @ X0)
% 1.94/2.16          | ~ (v8_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['25'])).
% 1.94/2.16  thf('27', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         ((v13_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (v8_lattices @ X0)
% 1.94/2.16          | ~ (v9_lattices @ X0)
% 1.94/2.16          | ~ (m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.94/2.16               (u1_struct_0 @ X0))
% 1.94/2.16          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 1.94/2.16              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 1.94/2.16              = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 1.94/2.16      inference('sup-', [status(thm)], ['22', '26'])).
% 1.94/2.16  thf('28', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 1.94/2.16            (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 1.94/2.16            = (k15_lattice3 @ X0 @ k1_xboole_0))
% 1.94/2.16          | ~ (m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.94/2.16               (u1_struct_0 @ X0))
% 1.94/2.16          | ~ (v9_lattices @ X0)
% 1.94/2.16          | ~ (v8_lattices @ X0)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v13_lattices @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['27'])).
% 1.94/2.16  thf('29', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | ~ (v8_lattices @ X0)
% 1.94/2.16          | ~ (v9_lattices @ X0)
% 1.94/2.16          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 1.94/2.16              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 1.94/2.16              = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 1.94/2.16      inference('sup-', [status(thm)], ['3', '28'])).
% 1.94/2.16  thf('30', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 1.94/2.16            (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 1.94/2.16            = (k15_lattice3 @ X0 @ k1_xboole_0))
% 1.94/2.16          | ~ (v9_lattices @ X0)
% 1.94/2.16          | ~ (v8_lattices @ X0)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['29'])).
% 1.94/2.16  thf('31', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         ((m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.94/2.16           (u1_struct_0 @ X0))
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['2'])).
% 1.94/2.16  thf('32', plain,
% 1.94/2.16      (![X29 : $i, X30 : $i]:
% 1.94/2.16         (~ (l3_lattices @ X29)
% 1.94/2.16          | (v2_struct_0 @ X29)
% 1.94/2.16          | (m1_subset_1 @ (k15_lattice3 @ X29 @ X30) @ (u1_struct_0 @ X29)))),
% 1.94/2.16      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 1.94/2.16  thf(d6_lattices, axiom,
% 1.94/2.16    (![A:$i]:
% 1.94/2.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 1.94/2.16       ( ( v6_lattices @ A ) <=>
% 1.94/2.16         ( ![B:$i]:
% 1.94/2.16           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.94/2.16             ( ![C:$i]:
% 1.94/2.16               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.94/2.16                 ( ( k2_lattices @ A @ B @ C ) = ( k2_lattices @ A @ C @ B ) ) ) ) ) ) ) ))).
% 1.94/2.16  thf('33', plain,
% 1.94/2.16      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.94/2.16         (~ (v6_lattices @ X26)
% 1.94/2.16          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 1.94/2.16          | ((k2_lattices @ X26 @ X28 @ X27) = (k2_lattices @ X26 @ X27 @ X28))
% 1.94/2.16          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X26))
% 1.94/2.16          | ~ (l1_lattices @ X26)
% 1.94/2.16          | (v2_struct_0 @ X26))),
% 1.94/2.16      inference('cnf', [status(esa)], [d6_lattices])).
% 1.94/2.16  thf('34', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.94/2.16          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 1.94/2.16              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 1.94/2.16          | ~ (v6_lattices @ X0))),
% 1.94/2.16      inference('sup-', [status(thm)], ['32', '33'])).
% 1.94/2.16  thf('35', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.16         (~ (v6_lattices @ X0)
% 1.94/2.16          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 1.94/2.16              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 1.94/2.16          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['34'])).
% 1.94/2.16  thf('36', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ((k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.94/2.16              (k15_lattice3 @ X0 @ X2))
% 1.94/2.16              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 1.94/2.16                 (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 1.94/2.16          | ~ (v6_lattices @ X0))),
% 1.94/2.16      inference('sup-', [status(thm)], ['31', '35'])).
% 1.94/2.16  thf('37', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.16         (~ (v6_lattices @ X0)
% 1.94/2.16          | ((k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.94/2.16              (k15_lattice3 @ X0 @ X2))
% 1.94/2.16              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 1.94/2.16                 (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['36'])).
% 1.94/2.16  thf('38', plain,
% 1.94/2.16      (![X29 : $i, X30 : $i]:
% 1.94/2.16         (~ (l3_lattices @ X29)
% 1.94/2.16          | (v2_struct_0 @ X29)
% 1.94/2.16          | (m1_subset_1 @ (k15_lattice3 @ X29 @ X30) @ (u1_struct_0 @ X29)))),
% 1.94/2.16      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 1.94/2.16  thf('39', plain,
% 1.94/2.16      (![X14 : $i, X15 : $i]:
% 1.94/2.16         (((k2_lattices @ X15 @ (sk_C_1 @ X14 @ X15) @ X14) != (X14))
% 1.94/2.16          | ((k2_lattices @ X15 @ X14 @ (sk_C_1 @ X14 @ X15)) != (X14))
% 1.94/2.16          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 1.94/2.16          | (v13_lattices @ X15)
% 1.94/2.16          | ~ (l1_lattices @ X15)
% 1.94/2.16          | (v2_struct_0 @ X15))),
% 1.94/2.16      inference('cnf', [status(esa)], [d13_lattices])).
% 1.94/2.16  thf('40', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 1.94/2.16              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 1.94/2.16              != (k15_lattice3 @ X0 @ X1))
% 1.94/2.16          | ((k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.94/2.16              (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1)))),
% 1.94/2.16      inference('sup-', [status(thm)], ['38', '39'])).
% 1.94/2.16  thf('41', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         (((k2_lattices @ X0 @ (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 1.94/2.16            (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1))
% 1.94/2.16          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 1.94/2.16              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 1.94/2.16              != (k15_lattice3 @ X0 @ X1))
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['40'])).
% 1.94/2.16  thf('42', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 1.94/2.16            (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 1.94/2.16            != (k15_lattice3 @ X0 @ X1))
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | ~ (v6_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 1.94/2.16              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 1.94/2.16              != (k15_lattice3 @ X0 @ X1)))),
% 1.94/2.16      inference('sup-', [status(thm)], ['37', '41'])).
% 1.94/2.16  thf('43', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         (~ (v6_lattices @ X0)
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 1.94/2.16              (sk_C_1 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 1.94/2.16              != (k15_lattice3 @ X0 @ X1)))),
% 1.94/2.16      inference('simplify', [status(thm)], ['42'])).
% 1.94/2.16  thf('44', plain,
% 1.94/2.16      (![X0 : $i]:
% 1.94/2.16         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 1.94/2.16            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | ~ (v8_lattices @ X0)
% 1.94/2.16          | ~ (v9_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | ~ (v6_lattices @ X0))),
% 1.94/2.16      inference('sup-', [status(thm)], ['30', '43'])).
% 1.94/2.16  thf('45', plain,
% 1.94/2.16      (![X0 : $i]:
% 1.94/2.16         (~ (v6_lattices @ X0)
% 1.94/2.16          | ~ (v9_lattices @ X0)
% 1.94/2.16          | ~ (v8_lattices @ X0)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | (v13_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['44'])).
% 1.94/2.16  thf(t50_lattice3, conjecture,
% 1.94/2.16    (![A:$i]:
% 1.94/2.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 1.94/2.16         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 1.94/2.16       ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 1.94/2.16         ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 1.94/2.16         ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ))).
% 1.94/2.16  thf(zf_stmt_0, negated_conjecture,
% 1.94/2.16    (~( ![A:$i]:
% 1.94/2.16        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 1.94/2.16            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 1.94/2.16          ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 1.94/2.16            ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 1.94/2.16            ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ) )),
% 1.94/2.16    inference('cnf.neg', [status(esa)], [t50_lattice3])).
% 1.94/2.16  thf('46', plain, (~ (v2_struct_0 @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf('47', plain,
% 1.94/2.16      ((~ (l3_lattices @ sk_A)
% 1.94/2.16        | ~ (l1_lattices @ sk_A)
% 1.94/2.16        | (v13_lattices @ sk_A)
% 1.94/2.16        | ~ (v10_lattices @ sk_A)
% 1.94/2.16        | ~ (v4_lattice3 @ sk_A)
% 1.94/2.16        | ~ (v8_lattices @ sk_A)
% 1.94/2.16        | ~ (v9_lattices @ sk_A)
% 1.94/2.16        | ~ (v6_lattices @ sk_A))),
% 1.94/2.16      inference('sup-', [status(thm)], ['45', '46'])).
% 1.94/2.16  thf('48', plain, ((l3_lattices @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf('49', plain, ((l3_lattices @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf(dt_l3_lattices, axiom,
% 1.94/2.16    (![A:$i]:
% 1.94/2.16     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 1.94/2.16  thf('50', plain,
% 1.94/2.16      (![X10 : $i]: ((l1_lattices @ X10) | ~ (l3_lattices @ X10))),
% 1.94/2.16      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 1.94/2.16  thf('51', plain, ((l1_lattices @ sk_A)),
% 1.94/2.16      inference('sup-', [status(thm)], ['49', '50'])).
% 1.94/2.16  thf('52', plain, ((v10_lattices @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf('53', plain, ((v4_lattice3 @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf(cc1_lattices, axiom,
% 1.94/2.16    (![A:$i]:
% 1.94/2.16     ( ( l3_lattices @ A ) =>
% 1.94/2.16       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 1.94/2.16         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 1.94/2.16           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 1.94/2.16           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 1.94/2.16  thf('54', plain,
% 1.94/2.16      (![X5 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X5)
% 1.94/2.16          | ~ (v10_lattices @ X5)
% 1.94/2.16          | (v8_lattices @ X5)
% 1.94/2.16          | ~ (l3_lattices @ X5))),
% 1.94/2.16      inference('cnf', [status(esa)], [cc1_lattices])).
% 1.94/2.16  thf('55', plain, (~ (v2_struct_0 @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf('56', plain,
% 1.94/2.16      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 1.94/2.16      inference('sup-', [status(thm)], ['54', '55'])).
% 1.94/2.16  thf('57', plain, ((l3_lattices @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf('58', plain, ((v10_lattices @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf('59', plain, ((v8_lattices @ sk_A)),
% 1.94/2.16      inference('demod', [status(thm)], ['56', '57', '58'])).
% 1.94/2.16  thf('60', plain,
% 1.94/2.16      (![X5 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X5)
% 1.94/2.16          | ~ (v10_lattices @ X5)
% 1.94/2.16          | (v9_lattices @ X5)
% 1.94/2.16          | ~ (l3_lattices @ X5))),
% 1.94/2.16      inference('cnf', [status(esa)], [cc1_lattices])).
% 1.94/2.16  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf('62', plain,
% 1.94/2.16      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 1.94/2.16      inference('sup-', [status(thm)], ['60', '61'])).
% 1.94/2.16  thf('63', plain, ((l3_lattices @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf('64', plain, ((v10_lattices @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf('65', plain, ((v9_lattices @ sk_A)),
% 1.94/2.16      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.94/2.16  thf('66', plain,
% 1.94/2.16      (![X5 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X5)
% 1.94/2.16          | ~ (v10_lattices @ X5)
% 1.94/2.16          | (v6_lattices @ X5)
% 1.94/2.16          | ~ (l3_lattices @ X5))),
% 1.94/2.16      inference('cnf', [status(esa)], [cc1_lattices])).
% 1.94/2.16  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf('68', plain,
% 1.94/2.16      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 1.94/2.16      inference('sup-', [status(thm)], ['66', '67'])).
% 1.94/2.16  thf('69', plain, ((l3_lattices @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf('70', plain, ((v10_lattices @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf('71', plain, ((v6_lattices @ sk_A)),
% 1.94/2.16      inference('demod', [status(thm)], ['68', '69', '70'])).
% 1.94/2.16  thf('72', plain, ((v13_lattices @ sk_A)),
% 1.94/2.16      inference('demod', [status(thm)],
% 1.94/2.16                ['47', '48', '51', '52', '53', '59', '65', '71'])).
% 1.94/2.16  thf('73', plain,
% 1.94/2.16      (![X29 : $i, X30 : $i]:
% 1.94/2.16         (~ (l3_lattices @ X29)
% 1.94/2.16          | (v2_struct_0 @ X29)
% 1.94/2.16          | (m1_subset_1 @ (k15_lattice3 @ X29 @ X30) @ (u1_struct_0 @ X29)))),
% 1.94/2.16      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 1.94/2.16  thf(dt_k5_lattices, axiom,
% 1.94/2.16    (![A:$i]:
% 1.94/2.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 1.94/2.16       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 1.94/2.16  thf('74', plain,
% 1.94/2.16      (![X9 : $i]:
% 1.94/2.16         ((m1_subset_1 @ (k5_lattices @ X9) @ (u1_struct_0 @ X9))
% 1.94/2.16          | ~ (l1_lattices @ X9)
% 1.94/2.16          | (v2_struct_0 @ X9))),
% 1.94/2.16      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 1.94/2.16  thf(d16_lattices, axiom,
% 1.94/2.16    (![A:$i]:
% 1.94/2.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 1.94/2.16       ( ( v13_lattices @ A ) =>
% 1.94/2.16         ( ![B:$i]:
% 1.94/2.16           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.94/2.16             ( ( ( B ) = ( k5_lattices @ A ) ) <=>
% 1.94/2.16               ( ![C:$i]:
% 1.94/2.16                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.94/2.16                   ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 1.94/2.16                     ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 1.94/2.16  thf('75', plain,
% 1.94/2.16      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.94/2.16         (~ (v13_lattices @ X6)
% 1.94/2.16          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 1.94/2.16          | ((X7) != (k5_lattices @ X6))
% 1.94/2.16          | ((k2_lattices @ X6 @ X8 @ X7) = (X7))
% 1.94/2.16          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 1.94/2.16          | ~ (l1_lattices @ X6)
% 1.94/2.16          | (v2_struct_0 @ X6))),
% 1.94/2.16      inference('cnf', [status(esa)], [d16_lattices])).
% 1.94/2.16  thf('76', plain,
% 1.94/2.16      (![X6 : $i, X8 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X6)
% 1.94/2.16          | ~ (l1_lattices @ X6)
% 1.94/2.16          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 1.94/2.16          | ((k2_lattices @ X6 @ X8 @ (k5_lattices @ X6)) = (k5_lattices @ X6))
% 1.94/2.16          | ~ (m1_subset_1 @ (k5_lattices @ X6) @ (u1_struct_0 @ X6))
% 1.94/2.16          | ~ (v13_lattices @ X6))),
% 1.94/2.16      inference('simplify', [status(thm)], ['75'])).
% 1.94/2.16  thf('77', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (v13_lattices @ X0)
% 1.94/2.16          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 1.94/2.16          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('sup-', [status(thm)], ['74', '76'])).
% 1.94/2.16  thf('78', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 1.94/2.16          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 1.94/2.16          | ~ (v13_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['77'])).
% 1.94/2.16  thf('79', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (v13_lattices @ X0)
% 1.94/2.16          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 1.94/2.16              = (k5_lattices @ X0)))),
% 1.94/2.16      inference('sup-', [status(thm)], ['73', '78'])).
% 1.94/2.16  thf('80', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 1.94/2.16            = (k5_lattices @ X0))
% 1.94/2.16          | ~ (v13_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['79'])).
% 1.94/2.16  thf('81', plain,
% 1.94/2.16      (![X9 : $i]:
% 1.94/2.16         ((m1_subset_1 @ (k5_lattices @ X9) @ (u1_struct_0 @ X9))
% 1.94/2.16          | ~ (l1_lattices @ X9)
% 1.94/2.16          | (v2_struct_0 @ X9))),
% 1.94/2.16      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 1.94/2.16  thf('82', plain,
% 1.94/2.16      (![X9 : $i]:
% 1.94/2.16         ((m1_subset_1 @ (k5_lattices @ X9) @ (u1_struct_0 @ X9))
% 1.94/2.16          | ~ (l1_lattices @ X9)
% 1.94/2.16          | (v2_struct_0 @ X9))),
% 1.94/2.16      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 1.94/2.16  thf('83', plain,
% 1.94/2.16      (![X17 : $i, X18 : $i, X21 : $i]:
% 1.94/2.16         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 1.94/2.16          | (r2_hidden @ (sk_D @ X21 @ X17 @ X18) @ X21)
% 1.94/2.16          | (r4_lattice3 @ X18 @ X17 @ X21)
% 1.94/2.16          | ~ (l3_lattices @ X18)
% 1.94/2.16          | (v2_struct_0 @ X18))),
% 1.94/2.16      inference('cnf', [status(esa)], [d17_lattice3])).
% 1.94/2.16  thf('84', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ X1)
% 1.94/2.16          | (r2_hidden @ (sk_D @ X1 @ (k5_lattices @ X0) @ X0) @ X1))),
% 1.94/2.16      inference('sup-', [status(thm)], ['82', '83'])).
% 1.94/2.16  thf('85', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         ((r2_hidden @ (sk_D @ X1 @ (k5_lattices @ X0) @ X0) @ X1)
% 1.94/2.16          | (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ X1)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['84'])).
% 1.94/2.16  thf('86', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 1.94/2.16      inference('sup-', [status(thm)], ['9', '10'])).
% 1.94/2.16  thf('87', plain,
% 1.94/2.16      (![X0 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ k1_xboole_0))),
% 1.94/2.16      inference('sup-', [status(thm)], ['85', '86'])).
% 1.94/2.16  thf('88', plain,
% 1.94/2.16      (![X9 : $i]:
% 1.94/2.16         ((m1_subset_1 @ (k5_lattices @ X9) @ (u1_struct_0 @ X9))
% 1.94/2.16          | ~ (l1_lattices @ X9)
% 1.94/2.16          | (v2_struct_0 @ X9))),
% 1.94/2.16      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 1.94/2.16  thf('89', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.16         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.94/2.16          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.94/2.16          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['17'])).
% 1.94/2.16  thf('90', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | ~ (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ X1)
% 1.94/2.16          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0)))),
% 1.94/2.16      inference('sup-', [status(thm)], ['88', '89'])).
% 1.94/2.16  thf('91', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i]:
% 1.94/2.16         ((r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 1.94/2.16          | ~ (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ X1)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['90'])).
% 1.94/2.16  thf('92', plain,
% 1.94/2.16      (![X0 : $i]:
% 1.94/2.16         (~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 1.94/2.16             (k5_lattices @ X0)))),
% 1.94/2.16      inference('sup-', [status(thm)], ['87', '91'])).
% 1.94/2.16  thf('93', plain,
% 1.94/2.16      (![X0 : $i]:
% 1.94/2.16         ((r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 1.94/2.16           (k5_lattices @ X0))
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['92'])).
% 1.94/2.16  thf('94', plain,
% 1.94/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.16         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.94/2.16          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 1.94/2.16              = (k15_lattice3 @ X0 @ X1))
% 1.94/2.16          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.94/2.16          | ~ (v9_lattices @ X0)
% 1.94/2.16          | ~ (v8_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['25'])).
% 1.94/2.16  thf('95', plain,
% 1.94/2.16      (![X0 : $i]:
% 1.94/2.16         (~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (v8_lattices @ X0)
% 1.94/2.16          | ~ (v9_lattices @ X0)
% 1.94/2.16          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 1.94/2.16          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 1.94/2.16              (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 1.94/2.16      inference('sup-', [status(thm)], ['93', '94'])).
% 1.94/2.16  thf('96', plain,
% 1.94/2.16      (![X0 : $i]:
% 1.94/2.16         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 1.94/2.16            (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 1.94/2.16          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 1.94/2.16          | ~ (v9_lattices @ X0)
% 1.94/2.16          | ~ (v8_lattices @ X0)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['95'])).
% 1.94/2.16  thf('97', plain,
% 1.94/2.16      (![X0 : $i]:
% 1.94/2.16         ((v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | ~ (v8_lattices @ X0)
% 1.94/2.16          | ~ (v9_lattices @ X0)
% 1.94/2.16          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 1.94/2.16              (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 1.94/2.16      inference('sup-', [status(thm)], ['81', '96'])).
% 1.94/2.16  thf('98', plain,
% 1.94/2.16      (![X0 : $i]:
% 1.94/2.16         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 1.94/2.16            (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 1.94/2.16          | ~ (v9_lattices @ X0)
% 1.94/2.16          | ~ (v8_lattices @ X0)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0))),
% 1.94/2.16      inference('simplify', [status(thm)], ['97'])).
% 1.94/2.16  thf('99', plain,
% 1.94/2.16      (![X0 : $i]:
% 1.94/2.16         (((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (v13_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | ~ (v8_lattices @ X0)
% 1.94/2.16          | ~ (v9_lattices @ X0))),
% 1.94/2.16      inference('sup+', [status(thm)], ['80', '98'])).
% 1.94/2.16  thf('100', plain,
% 1.94/2.16      (![X0 : $i]:
% 1.94/2.16         (~ (v9_lattices @ X0)
% 1.94/2.16          | ~ (v8_lattices @ X0)
% 1.94/2.16          | ~ (v4_lattice3 @ X0)
% 1.94/2.16          | ~ (v10_lattices @ X0)
% 1.94/2.16          | ~ (v13_lattices @ X0)
% 1.94/2.16          | ~ (l1_lattices @ X0)
% 1.94/2.16          | ~ (l3_lattices @ X0)
% 1.94/2.16          | (v2_struct_0 @ X0)
% 1.94/2.16          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 1.94/2.16      inference('simplify', [status(thm)], ['99'])).
% 1.94/2.16  thf('101', plain,
% 1.94/2.16      (((v2_struct_0 @ sk_A)
% 1.94/2.16        | ~ (v10_lattices @ sk_A)
% 1.94/2.16        | ~ (v13_lattices @ sk_A)
% 1.94/2.16        | ~ (l3_lattices @ sk_A)
% 1.94/2.16        | ((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf('102', plain,
% 1.94/2.16      ((((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))
% 1.94/2.16         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 1.94/2.16      inference('split', [status(esa)], ['101'])).
% 1.94/2.16  thf('103', plain,
% 1.94/2.16      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 1.94/2.16         | (v2_struct_0 @ sk_A)
% 1.94/2.16         | ~ (l3_lattices @ sk_A)
% 1.94/2.16         | ~ (l1_lattices @ sk_A)
% 1.94/2.16         | ~ (v13_lattices @ sk_A)
% 1.94/2.16         | ~ (v10_lattices @ sk_A)
% 1.94/2.16         | ~ (v4_lattice3 @ sk_A)
% 1.94/2.16         | ~ (v8_lattices @ sk_A)
% 1.94/2.16         | ~ (v9_lattices @ sk_A)))
% 1.94/2.16         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 1.94/2.16      inference('sup-', [status(thm)], ['100', '102'])).
% 1.94/2.16  thf('104', plain, ((l3_lattices @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf('105', plain, ((l1_lattices @ sk_A)),
% 1.94/2.16      inference('sup-', [status(thm)], ['49', '50'])).
% 1.94/2.16  thf('106', plain, ((v10_lattices @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf('107', plain, ((v4_lattice3 @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf('108', plain, ((v8_lattices @ sk_A)),
% 1.94/2.16      inference('demod', [status(thm)], ['56', '57', '58'])).
% 1.94/2.16  thf('109', plain, ((v9_lattices @ sk_A)),
% 1.94/2.16      inference('demod', [status(thm)], ['62', '63', '64'])).
% 1.94/2.16  thf('110', plain,
% 1.94/2.16      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 1.94/2.16         | (v2_struct_0 @ sk_A)
% 1.94/2.16         | ~ (v13_lattices @ sk_A)))
% 1.94/2.16         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 1.94/2.16      inference('demod', [status(thm)],
% 1.94/2.16                ['103', '104', '105', '106', '107', '108', '109'])).
% 1.94/2.16  thf('111', plain,
% 1.94/2.16      (((~ (v13_lattices @ sk_A) | (v2_struct_0 @ sk_A)))
% 1.94/2.16         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 1.94/2.16      inference('simplify', [status(thm)], ['110'])).
% 1.94/2.16  thf('112', plain, (~ (v2_struct_0 @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf('113', plain,
% 1.94/2.16      ((~ (v13_lattices @ sk_A))
% 1.94/2.16         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 1.94/2.16      inference('clc', [status(thm)], ['111', '112'])).
% 1.94/2.16  thf('114', plain,
% 1.94/2.16      (($false)
% 1.94/2.16         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 1.94/2.16      inference('sup-', [status(thm)], ['72', '113'])).
% 1.94/2.16  thf('115', plain, (((v2_struct_0 @ sk_A)) <= (((v2_struct_0 @ sk_A)))),
% 1.94/2.16      inference('split', [status(esa)], ['101'])).
% 1.94/2.16  thf('116', plain, (~ (v2_struct_0 @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf('117', plain, (~ ((v2_struct_0 @ sk_A))),
% 1.94/2.16      inference('sup-', [status(thm)], ['115', '116'])).
% 1.94/2.16  thf('118', plain, ((l3_lattices @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf('119', plain, ((~ (l3_lattices @ sk_A)) <= (~ ((l3_lattices @ sk_A)))),
% 1.94/2.16      inference('split', [status(esa)], ['101'])).
% 1.94/2.16  thf('120', plain, (((l3_lattices @ sk_A))),
% 1.94/2.16      inference('sup-', [status(thm)], ['118', '119'])).
% 1.94/2.16  thf('121', plain, ((v10_lattices @ sk_A)),
% 1.94/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.16  thf('122', plain, ((~ (v10_lattices @ sk_A)) <= (~ ((v10_lattices @ sk_A)))),
% 1.94/2.16      inference('split', [status(esa)], ['101'])).
% 1.94/2.16  thf('123', plain, (((v10_lattices @ sk_A))),
% 1.94/2.16      inference('sup-', [status(thm)], ['121', '122'])).
% 1.94/2.16  thf('124', plain, ((v13_lattices @ sk_A)),
% 1.94/2.16      inference('demod', [status(thm)],
% 1.94/2.16                ['47', '48', '51', '52', '53', '59', '65', '71'])).
% 1.94/2.16  thf('125', plain, ((~ (v13_lattices @ sk_A)) <= (~ ((v13_lattices @ sk_A)))),
% 1.94/2.16      inference('split', [status(esa)], ['101'])).
% 1.94/2.16  thf('126', plain, (((v13_lattices @ sk_A))),
% 1.94/2.16      inference('sup-', [status(thm)], ['124', '125'])).
% 1.94/2.16  thf('127', plain,
% 1.94/2.16      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))) | 
% 1.94/2.16       ~ ((v13_lattices @ sk_A)) | ~ ((v10_lattices @ sk_A)) | 
% 1.94/2.16       ~ ((l3_lattices @ sk_A)) | ((v2_struct_0 @ sk_A))),
% 1.94/2.16      inference('split', [status(esa)], ['101'])).
% 1.94/2.16  thf('128', plain,
% 1.94/2.16      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 1.94/2.16      inference('sat_resolution*', [status(thm)],
% 1.94/2.16                ['117', '120', '123', '126', '127'])).
% 1.94/2.16  thf('129', plain, ($false),
% 1.94/2.16      inference('simpl_trail', [status(thm)], ['114', '128'])).
% 1.94/2.16  
% 1.94/2.16  % SZS output end Refutation
% 1.94/2.16  
% 1.94/2.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
