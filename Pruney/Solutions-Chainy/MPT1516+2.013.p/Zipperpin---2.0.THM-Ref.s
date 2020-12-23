%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Zbxc1TLa1V

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:36 EST 2020

% Result     : Theorem 4.86s
% Output     : Refutation 4.95s
% Verified   : 
% Statistics : Number of formulae       :  224 (1215 expanded)
%              Number of leaves         :   41 ( 327 expanded)
%              Depth                    :   31
%              Number of atoms          : 3637 (25602 expanded)
%              Number of equality atoms :  113 ( 749 expanded)
%              Maximal formula depth    :   23 (   9 average)

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

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

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

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(d18_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( ( v4_lattice3 @ A )
      <=> ! [B: $i] :
          ? [C: $i] :
            ( ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
               => ( ( r4_lattice3 @ A @ D @ B )
                 => ( r1_lattices @ A @ C @ D ) ) )
            & ( r4_lattice3 @ A @ C @ B )
            & ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v4_lattice3 @ X23 )
      | ( m1_subset_1 @ ( sk_C_2 @ X24 @ X23 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('1',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v4_lattice3 @ X23 )
      | ( r4_lattice3 @ X23 @ ( sk_C_2 @ X24 @ X23 ) @ X24 )
      | ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('2',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v4_lattice3 @ X23 )
      | ( r4_lattice3 @ X23 @ ( sk_C_2 @ X24 @ X23 ) @ X24 )
      | ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('3',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v4_lattice3 @ X23 )
      | ( m1_subset_1 @ ( sk_C_2 @ X24 @ X23 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

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

thf('4',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v10_lattices @ X26 )
      | ~ ( v4_lattice3 @ X26 )
      | ~ ( l3_lattices @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( r4_lattice3 @ X26 @ X27 @ X28 )
      | ( r4_lattice3 @ X26 @ ( sk_D_2 @ X27 @ X28 @ X26 ) @ X28 )
      | ( X27
        = ( k15_lattice3 @ X26 @ X28 ) )
      | ~ ( l3_lattices @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X27
        = ( k15_lattice3 @ X26 @ X28 ) )
      | ( r4_lattice3 @ X26 @ ( sk_D_2 @ X27 @ X28 @ X26 ) @ X28 )
      | ~ ( r4_lattice3 @ X26 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l3_lattices @ X26 )
      | ~ ( v4_lattice3 @ X26 )
      | ~ ( v10_lattices @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C_2 @ X1 @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( sk_D_2 @ ( sk_C_2 @ X1 @ X0 ) @ X2 @ X0 ) @ X2 )
      | ( ( sk_C_2 @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C_2 @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X2 ) )
      | ( r4_lattice3 @ X0 @ ( sk_D_2 @ ( sk_C_2 @ X1 @ X0 ) @ X2 @ X0 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C_2 @ X1 @ X0 ) @ X2 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( r4_lattice3 @ X1 @ ( sk_D_2 @ ( sk_C_2 @ X0 @ X1 ) @ X0 @ X1 ) @ X0 )
      | ( ( sk_C_2 @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_2 @ X0 @ X1 )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ( r4_lattice3 @ X1 @ ( sk_D_2 @ ( sk_C_2 @ X0 @ X1 ) @ X0 @ X1 ) @ X0 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v4_lattice3 @ X23 )
      | ( m1_subset_1 @ ( sk_C_2 @ X24 @ X23 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

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

thf('11',plain,(
    ! [X17: $i,X18: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ ( sk_D @ X21 @ X17 @ X18 ) @ X21 )
      | ( r4_lattice3 @ X18 @ X17 @ X21 )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( sk_C_2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( sk_C_2 @ X1 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('15',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( r4_lattice3 @ X0 @ ( sk_C_2 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf('19',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v4_lattice3 @ X23 )
      | ( m1_subset_1 @ ( sk_C_2 @ X24 @ X23 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('20',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v10_lattices @ X26 )
      | ~ ( v4_lattice3 @ X26 )
      | ~ ( l3_lattices @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( r4_lattice3 @ X26 @ X27 @ X28 )
      | ( m1_subset_1 @ ( sk_D_2 @ X27 @ X28 @ X26 ) @ ( u1_struct_0 @ X26 ) )
      | ( X27
        = ( k15_lattice3 @ X26 @ X28 ) )
      | ~ ( l3_lattices @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('21',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X27
        = ( k15_lattice3 @ X26 @ X28 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X27 @ X28 @ X26 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( r4_lattice3 @ X26 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l3_lattices @ X26 )
      | ~ ( v4_lattice3 @ X26 )
      | ~ ( v10_lattices @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C_2 @ X1 @ X0 ) @ X2 )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_C_2 @ X1 @ X0 ) @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_C_2 @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C_2 @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ X2 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_C_2 @ X1 @ X0 ) @ X2 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C_2 @ X1 @ X0 ) @ X2 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_C_2 @ X1 @ X0 ) @ k1_xboole_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_C_2 @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_2 @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ ( sk_C_2 @ X1 @ X0 ) @ k1_xboole_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v4_lattice3 @ X23 )
      | ~ ( r4_lattice3 @ X23 @ X25 @ X24 )
      | ( r1_lattices @ X23 @ ( sk_C_2 @ X24 @ X23 ) @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C_2 @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( sk_C_2 @ X2 @ X0 ) @ ( sk_D_2 @ ( sk_C_2 @ X1 @ X0 ) @ k1_xboole_0 @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_D_2 @ ( sk_C_2 @ X1 @ X0 ) @ k1_xboole_0 @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_D_2 @ ( sk_C_2 @ X1 @ X0 ) @ k1_xboole_0 @ X0 ) @ X2 )
      | ( r1_lattices @ X0 @ ( sk_C_2 @ X2 @ X0 ) @ ( sk_D_2 @ ( sk_C_2 @ X1 @ X0 ) @ k1_xboole_0 @ X0 ) )
      | ( ( sk_C_2 @ X1 @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C_2 @ k1_xboole_0 @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C_2 @ k1_xboole_0 @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( r1_lattices @ X0 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ ( sk_D_2 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ X0 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ ( sk_D_2 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 @ X0 ) )
      | ( ( sk_C_2 @ k1_xboole_0 @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v2_struct_0 @ X26 )
      | ~ ( v10_lattices @ X26 )
      | ~ ( v4_lattice3 @ X26 )
      | ~ ( l3_lattices @ X26 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( r4_lattice3 @ X26 @ X27 @ X28 )
      | ~ ( r1_lattices @ X26 @ X27 @ ( sk_D_2 @ X27 @ X28 @ X26 ) )
      | ( X27
        = ( k15_lattice3 @ X26 @ X28 ) )
      | ~ ( l3_lattices @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('32',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X27
        = ( k15_lattice3 @ X26 @ X28 ) )
      | ~ ( r1_lattices @ X26 @ X27 @ ( sk_D_2 @ X27 @ X28 @ X26 ) )
      | ~ ( r4_lattice3 @ X26 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l3_lattices @ X26 )
      | ~ ( v4_lattice3 @ X26 )
      | ~ ( v10_lattices @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C_2 @ k1_xboole_0 @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( ( sk_C_2 @ k1_xboole_0 @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_C_2 @ k1_xboole_0 @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C_2 @ k1_xboole_0 @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( sk_C_2 @ k1_xboole_0 @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( ( sk_C_2 @ k1_xboole_0 @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ k1_xboole_0 @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v4_lattice3 @ X23 )
      | ( m1_subset_1 @ ( sk_C_2 @ X24 @ X23 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

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

thf('40',plain,(
    ! [X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ X14 @ X15 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ( v13_lattices @ X15 )
      | ~ ( l1_lattices @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_lattices])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ k1_xboole_0 @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ k1_xboole_0 @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('48',plain,(
    ! [X17: $i,X18: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ ( sk_D @ X21 @ X17 @ X18 ) @ X21 )
      | ( r4_lattice3 @ X18 @ X17 @ X21 )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( sk_C_1 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( sk_C_1 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( sk_C_1 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( sk_C_1 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) @ X2 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( sk_C_1 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C_1 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('54',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v4_lattice3 @ X23 )
      | ~ ( r4_lattice3 @ X23 @ X25 @ X24 )
      | ( r1_lattices @ X23 @ ( sk_C_2 @ X24 @ X23 ) @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( sk_C_2 @ X2 @ X0 ) @ ( sk_C_1 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( sk_C_1 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( sk_C_1 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) @ X2 )
      | ( r1_lattices @ X0 @ ( sk_C_2 @ X2 @ X0 ) @ ( sk_C_1 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ ( sk_C_1 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X0 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ ( sk_C_1 @ ( sk_C_2 @ X1 @ X0 ) @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ X0 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['46','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_lattices @ X0 @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_2 @ k1_xboole_0 @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('64',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v4_lattice3 @ X23 )
      | ( m1_subset_1 @ ( sk_C_2 @ X24 @ X23 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d18_lattice3])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

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

thf('67',plain,(
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

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X1 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X1 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['44','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

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

thf('76',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v6_lattices @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( u1_struct_0 @ X30 ) )
      | ( ( k2_lattices @ X30 @ X32 @ X31 )
        = ( k2_lattices @ X30 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X30 ) )
      | ~ ( l1_lattices @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d6_lattices])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X1 ) )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) ) )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('82',plain,(
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

thf('83',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( ( k2_lattices @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
       != ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
       != ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['80','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_1 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
       != ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['87'])).

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

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( v13_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( v6_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('95',plain,(
    ! [X10: $i] :
      ( ( l1_lattices @ X10 )
      | ~ ( l3_lattices @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('96',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['94','95'])).

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

thf('97',plain,(
    ! [X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v8_lattices @ X5 )
      | ~ ( l3_lattices @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v9_lattices @ X5 )
      | ~ ( l3_lattices @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    ! [X5: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v6_lattices @ X5 )
      | ~ ( l3_lattices @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('110',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['90','91','92','93','96','102','108','114'])).

thf(dt_k5_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('116',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('117',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('118',plain,(
    ! [X17: $i,X18: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ ( sk_D @ X21 @ X17 @ X18 ) @ X21 )
      | ( r4_lattice3 @ X18 @ X17 @ X21 )
      | ~ ( l3_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('119',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k5_lattices @ X0 ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k5_lattices @ X0 ) @ X0 ) @ X1 )
      | ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('124',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('125',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X27
        = ( k15_lattice3 @ X26 @ X28 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ X27 @ X28 @ X26 ) @ ( u1_struct_0 @ X26 ) )
      | ~ ( r4_lattice3 @ X26 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l3_lattices @ X26 )
      | ~ ( v4_lattice3 @ X26 )
      | ~ ( v10_lattices @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( sk_D_2 @ ( k5_lattices @ X0 ) @ X1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ ( k5_lattices @ X0 ) @ X1 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( m1_subset_1 @ ( sk_D_2 @ ( k5_lattices @ X0 ) @ k1_xboole_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['123','127'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ ( k5_lattices @ X0 ) @ k1_xboole_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
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

thf('131',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v13_lattices @ X6 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( X7
       != ( k5_lattices @ X6 ) )
      | ( ( k2_lattices @ X6 @ X7 @ X8 )
        = X7 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d16_lattices])).

thf('132',plain,(
    ! [X6: $i,X8: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( l1_lattices @ X6 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X6 ) )
      | ( ( k2_lattices @ X6 @ ( k5_lattices @ X6 ) @ X8 )
        = ( k5_lattices @ X6 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X6 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( v13_lattices @ X6 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['130','132'])).

thf('134',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( sk_D_2 @ ( k5_lattices @ X0 ) @ k1_xboole_0 @ X0 ) )
        = ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['129','134'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( sk_D_2 @ ( k5_lattices @ X0 ) @ k1_xboole_0 @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ ( sk_D_2 @ ( k5_lattices @ X0 ) @ k1_xboole_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('138',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('139',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ( ( k2_lattices @ X12 @ X11 @ X13 )
       != X11 )
      | ( r1_lattices @ X12 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l3_lattices @ X12 )
      | ~ ( v9_lattices @ X12 )
      | ~ ( v8_lattices @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
       != ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
       != ( k5_lattices @ X0 ) )
      | ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( sk_D_2 @ ( k5_lattices @ X0 ) @ k1_xboole_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( sk_D_2 @ ( k5_lattices @ X0 ) @ k1_xboole_0 @ X0 ) )
       != ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['137','141'])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( sk_D_2 @ ( k5_lattices @ X0 ) @ k1_xboole_0 @ X0 ) )
       != ( k5_lattices @ X0 ) )
      | ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( sk_D_2 @ ( k5_lattices @ X0 ) @ k1_xboole_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( ( k5_lattices @ X0 )
       != ( k5_lattices @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( sk_D_2 @ ( k5_lattices @ X0 ) @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['136','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ X0 @ ( k5_lattices @ X0 ) @ ( sk_D_2 @ ( k5_lattices @ X0 ) @ k1_xboole_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['144'])).

thf('146',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( X27
        = ( k15_lattice3 @ X26 @ X28 ) )
      | ~ ( r1_lattices @ X26 @ X27 @ ( sk_D_2 @ X27 @ X28 @ X26 ) )
      | ~ ( r4_lattice3 @ X26 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X26 ) )
      | ~ ( l3_lattices @ X26 )
      | ~ ( v4_lattice3 @ X26 )
      | ~ ( v10_lattices @ X26 )
      | ( v2_struct_0 @ X26 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ k1_xboole_0 )
      | ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['122','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k5_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['116','150'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k5_lattices @ X0 )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['153'])).

thf('155',plain,
    ( ( ( ( k5_lattices @ sk_A )
       != ( k5_lattices @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( v13_lattices @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['152','154'])).

thf('156',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['94','95'])).

thf('157',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('161',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('162',plain,
    ( ( ( ( k5_lattices @ sk_A )
       != ( k5_lattices @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v13_lattices @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['155','156','157','158','159','160','161'])).

thf('163',plain,
    ( ( ~ ( v13_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['163','164'])).

thf('166',plain,
    ( $false
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['115','165'])).

thf('167',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['153'])).

thf('168',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,
    ( ~ ( l3_lattices @ sk_A )
   <= ~ ( l3_lattices @ sk_A ) ),
    inference(split,[status(esa)],['153'])).

thf('172',plain,(
    l3_lattices @ sk_A ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ~ ( v10_lattices @ sk_A )
   <= ~ ( v10_lattices @ sk_A ) ),
    inference(split,[status(esa)],['153'])).

thf('175',plain,(
    v10_lattices @ sk_A ),
    inference('sup-',[status(thm)],['173','174'])).

thf('176',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['90','91','92','93','96','102','108','114'])).

thf('177',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ~ ( v13_lattices @ sk_A ) ),
    inference(split,[status(esa)],['153'])).

thf('178',plain,(
    v13_lattices @ sk_A ),
    inference('sup-',[status(thm)],['176','177'])).

thf('179',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['153'])).

thf('180',plain,(
    ( k5_lattices @ sk_A )
 != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ),
    inference('sat_resolution*',[status(thm)],['169','172','175','178','179'])).

thf('181',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['166','180'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Zbxc1TLa1V
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:09:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 4.86/5.11  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.86/5.11  % Solved by: fo/fo7.sh
% 4.86/5.11  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.86/5.11  % done 3690 iterations in 4.647s
% 4.86/5.11  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.86/5.11  % SZS output start Refutation
% 4.86/5.11  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.86/5.11  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 4.86/5.11  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.86/5.11  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 4.86/5.11  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.86/5.11  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 4.86/5.11  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 4.86/5.11  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 4.86/5.11  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.86/5.11  thf(sk_A_type, type, sk_A: $i).
% 4.86/5.11  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 4.86/5.11  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.86/5.11  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 4.86/5.11  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 4.86/5.11  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 4.86/5.11  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 4.86/5.11  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 4.86/5.11  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 4.86/5.11  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 4.86/5.11  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 4.86/5.11  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 4.86/5.11  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 4.86/5.11  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 4.86/5.11  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 4.86/5.11  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 4.86/5.11  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 4.86/5.11  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 4.86/5.11  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 4.86/5.11  thf(d18_lattice3, axiom,
% 4.86/5.11    (![A:$i]:
% 4.86/5.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 4.86/5.11       ( ( v4_lattice3 @ A ) <=>
% 4.86/5.11         ( ![B:$i]:
% 4.86/5.11           ( ?[C:$i]:
% 4.86/5.11             ( ( ![D:$i]:
% 4.86/5.11                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 4.86/5.11                   ( ( r4_lattice3 @ A @ D @ B ) => ( r1_lattices @ A @ C @ D ) ) ) ) & 
% 4.86/5.11               ( r4_lattice3 @ A @ C @ B ) & 
% 4.86/5.11               ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 4.86/5.11  thf('0', plain,
% 4.86/5.11      (![X23 : $i, X24 : $i]:
% 4.86/5.11         (~ (v4_lattice3 @ X23)
% 4.86/5.11          | (m1_subset_1 @ (sk_C_2 @ X24 @ X23) @ (u1_struct_0 @ X23))
% 4.86/5.11          | ~ (l3_lattices @ X23)
% 4.86/5.11          | (v2_struct_0 @ X23))),
% 4.86/5.11      inference('cnf', [status(esa)], [d18_lattice3])).
% 4.86/5.11  thf('1', plain,
% 4.86/5.11      (![X23 : $i, X24 : $i]:
% 4.86/5.11         (~ (v4_lattice3 @ X23)
% 4.86/5.11          | (r4_lattice3 @ X23 @ (sk_C_2 @ X24 @ X23) @ X24)
% 4.86/5.11          | ~ (l3_lattices @ X23)
% 4.86/5.11          | (v2_struct_0 @ X23))),
% 4.86/5.11      inference('cnf', [status(esa)], [d18_lattice3])).
% 4.86/5.11  thf('2', plain,
% 4.86/5.11      (![X23 : $i, X24 : $i]:
% 4.86/5.11         (~ (v4_lattice3 @ X23)
% 4.86/5.11          | (r4_lattice3 @ X23 @ (sk_C_2 @ X24 @ X23) @ X24)
% 4.86/5.11          | ~ (l3_lattices @ X23)
% 4.86/5.11          | (v2_struct_0 @ X23))),
% 4.86/5.11      inference('cnf', [status(esa)], [d18_lattice3])).
% 4.86/5.11  thf('3', plain,
% 4.86/5.11      (![X23 : $i, X24 : $i]:
% 4.86/5.11         (~ (v4_lattice3 @ X23)
% 4.86/5.11          | (m1_subset_1 @ (sk_C_2 @ X24 @ X23) @ (u1_struct_0 @ X23))
% 4.86/5.11          | ~ (l3_lattices @ X23)
% 4.86/5.11          | (v2_struct_0 @ X23))),
% 4.86/5.11      inference('cnf', [status(esa)], [d18_lattice3])).
% 4.86/5.11  thf(d21_lattice3, axiom,
% 4.86/5.11    (![A:$i]:
% 4.86/5.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 4.86/5.11       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 4.86/5.11           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 4.86/5.11         ( ![B:$i,C:$i]:
% 4.86/5.11           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.86/5.11             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 4.86/5.11               ( ( r4_lattice3 @ A @ C @ B ) & 
% 4.86/5.11                 ( ![D:$i]:
% 4.86/5.11                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 4.86/5.11                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 4.86/5.11                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 4.86/5.11  thf('4', plain,
% 4.86/5.11      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.86/5.11         ((v2_struct_0 @ X26)
% 4.86/5.11          | ~ (v10_lattices @ X26)
% 4.86/5.11          | ~ (v4_lattice3 @ X26)
% 4.86/5.11          | ~ (l3_lattices @ X26)
% 4.86/5.11          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 4.86/5.11          | ~ (r4_lattice3 @ X26 @ X27 @ X28)
% 4.86/5.11          | (r4_lattice3 @ X26 @ (sk_D_2 @ X27 @ X28 @ X26) @ X28)
% 4.86/5.11          | ((X27) = (k15_lattice3 @ X26 @ X28))
% 4.86/5.11          | ~ (l3_lattices @ X26)
% 4.86/5.11          | (v2_struct_0 @ X26))),
% 4.86/5.11      inference('cnf', [status(esa)], [d21_lattice3])).
% 4.86/5.11  thf('5', plain,
% 4.86/5.11      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.86/5.11         (((X27) = (k15_lattice3 @ X26 @ X28))
% 4.86/5.11          | (r4_lattice3 @ X26 @ (sk_D_2 @ X27 @ X28 @ X26) @ X28)
% 4.86/5.11          | ~ (r4_lattice3 @ X26 @ X27 @ X28)
% 4.86/5.11          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 4.86/5.11          | ~ (l3_lattices @ X26)
% 4.86/5.11          | ~ (v4_lattice3 @ X26)
% 4.86/5.11          | ~ (v10_lattices @ X26)
% 4.86/5.11          | (v2_struct_0 @ X26))),
% 4.86/5.11      inference('simplify', [status(thm)], ['4'])).
% 4.86/5.11  thf('6', plain,
% 4.86/5.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.86/5.11         ((v2_struct_0 @ X0)
% 4.86/5.11          | ~ (l3_lattices @ X0)
% 4.86/5.11          | ~ (v4_lattice3 @ X0)
% 4.86/5.11          | (v2_struct_0 @ X0)
% 4.86/5.11          | ~ (v10_lattices @ X0)
% 4.86/5.11          | ~ (v4_lattice3 @ X0)
% 4.86/5.11          | ~ (l3_lattices @ X0)
% 4.86/5.11          | ~ (r4_lattice3 @ X0 @ (sk_C_2 @ X1 @ X0) @ X2)
% 4.86/5.11          | (r4_lattice3 @ X0 @ (sk_D_2 @ (sk_C_2 @ X1 @ X0) @ X2 @ X0) @ X2)
% 4.86/5.11          | ((sk_C_2 @ X1 @ X0) = (k15_lattice3 @ X0 @ X2)))),
% 4.86/5.11      inference('sup-', [status(thm)], ['3', '5'])).
% 4.86/5.11  thf('7', plain,
% 4.86/5.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.86/5.11         (((sk_C_2 @ X1 @ X0) = (k15_lattice3 @ X0 @ X2))
% 4.86/5.11          | (r4_lattice3 @ X0 @ (sk_D_2 @ (sk_C_2 @ X1 @ X0) @ X2 @ X0) @ X2)
% 4.86/5.11          | ~ (r4_lattice3 @ X0 @ (sk_C_2 @ X1 @ X0) @ X2)
% 4.86/5.11          | ~ (v10_lattices @ X0)
% 4.86/5.11          | ~ (v4_lattice3 @ X0)
% 4.86/5.11          | ~ (l3_lattices @ X0)
% 4.86/5.11          | (v2_struct_0 @ X0))),
% 4.86/5.11      inference('simplify', [status(thm)], ['6'])).
% 4.86/5.11  thf('8', plain,
% 4.86/5.11      (![X0 : $i, X1 : $i]:
% 4.86/5.11         ((v2_struct_0 @ X1)
% 4.86/5.11          | ~ (l3_lattices @ X1)
% 4.86/5.11          | ~ (v4_lattice3 @ X1)
% 4.86/5.11          | (v2_struct_0 @ X1)
% 4.86/5.11          | ~ (l3_lattices @ X1)
% 4.86/5.11          | ~ (v4_lattice3 @ X1)
% 4.86/5.11          | ~ (v10_lattices @ X1)
% 4.86/5.11          | (r4_lattice3 @ X1 @ (sk_D_2 @ (sk_C_2 @ X0 @ X1) @ X0 @ X1) @ X0)
% 4.86/5.11          | ((sk_C_2 @ X0 @ X1) = (k15_lattice3 @ X1 @ X0)))),
% 4.86/5.11      inference('sup-', [status(thm)], ['2', '7'])).
% 4.86/5.11  thf('9', plain,
% 4.86/5.11      (![X0 : $i, X1 : $i]:
% 4.86/5.11         (((sk_C_2 @ X0 @ X1) = (k15_lattice3 @ X1 @ X0))
% 4.86/5.11          | (r4_lattice3 @ X1 @ (sk_D_2 @ (sk_C_2 @ X0 @ X1) @ X0 @ X1) @ X0)
% 4.86/5.11          | ~ (v10_lattices @ X1)
% 4.86/5.11          | ~ (v4_lattice3 @ X1)
% 4.86/5.11          | ~ (l3_lattices @ X1)
% 4.86/5.11          | (v2_struct_0 @ X1))),
% 4.86/5.11      inference('simplify', [status(thm)], ['8'])).
% 4.86/5.11  thf('10', plain,
% 4.86/5.11      (![X23 : $i, X24 : $i]:
% 4.86/5.11         (~ (v4_lattice3 @ X23)
% 4.86/5.11          | (m1_subset_1 @ (sk_C_2 @ X24 @ X23) @ (u1_struct_0 @ X23))
% 4.86/5.11          | ~ (l3_lattices @ X23)
% 4.86/5.11          | (v2_struct_0 @ X23))),
% 4.86/5.11      inference('cnf', [status(esa)], [d18_lattice3])).
% 4.86/5.11  thf(d17_lattice3, axiom,
% 4.86/5.11    (![A:$i]:
% 4.86/5.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 4.86/5.11       ( ![B:$i]:
% 4.86/5.11         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 4.86/5.11           ( ![C:$i]:
% 4.86/5.11             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 4.86/5.11               ( ![D:$i]:
% 4.86/5.11                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 4.86/5.11                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 4.86/5.11  thf('11', plain,
% 4.86/5.11      (![X17 : $i, X18 : $i, X21 : $i]:
% 4.86/5.11         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 4.86/5.11          | (r2_hidden @ (sk_D @ X21 @ X17 @ X18) @ X21)
% 4.86/5.11          | (r4_lattice3 @ X18 @ X17 @ X21)
% 4.86/5.11          | ~ (l3_lattices @ X18)
% 4.86/5.11          | (v2_struct_0 @ X18))),
% 4.86/5.11      inference('cnf', [status(esa)], [d17_lattice3])).
% 4.86/5.11  thf('12', plain,
% 4.86/5.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.86/5.11         ((v2_struct_0 @ X0)
% 4.86/5.11          | ~ (l3_lattices @ X0)
% 4.86/5.11          | ~ (v4_lattice3 @ X0)
% 4.86/5.11          | (v2_struct_0 @ X0)
% 4.86/5.11          | ~ (l3_lattices @ X0)
% 4.86/5.11          | (r4_lattice3 @ X0 @ (sk_C_2 @ X1 @ X0) @ X2)
% 4.86/5.11          | (r2_hidden @ (sk_D @ X2 @ (sk_C_2 @ X1 @ X0) @ X0) @ X2))),
% 4.86/5.11      inference('sup-', [status(thm)], ['10', '11'])).
% 4.86/5.11  thf('13', plain,
% 4.86/5.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.86/5.11         ((r2_hidden @ (sk_D @ X2 @ (sk_C_2 @ X1 @ X0) @ X0) @ X2)
% 4.86/5.11          | (r4_lattice3 @ X0 @ (sk_C_2 @ X1 @ X0) @ X2)
% 4.86/5.11          | ~ (v4_lattice3 @ X0)
% 4.86/5.11          | ~ (l3_lattices @ X0)
% 4.86/5.11          | (v2_struct_0 @ X0))),
% 4.86/5.11      inference('simplify', [status(thm)], ['12'])).
% 4.86/5.11  thf(t113_zfmisc_1, axiom,
% 4.86/5.11    (![A:$i,B:$i]:
% 4.86/5.11     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 4.86/5.11       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 4.86/5.11  thf('14', plain,
% 4.86/5.11      (![X1 : $i, X2 : $i]:
% 4.86/5.11         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 4.86/5.11      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 4.86/5.11  thf('15', plain,
% 4.86/5.11      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 4.86/5.11      inference('simplify', [status(thm)], ['14'])).
% 4.86/5.11  thf(t152_zfmisc_1, axiom,
% 4.86/5.11    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 4.86/5.11  thf('16', plain,
% 4.86/5.11      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 4.86/5.11      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 4.86/5.11  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 4.86/5.11      inference('sup-', [status(thm)], ['15', '16'])).
% 4.86/5.11  thf('18', plain,
% 4.86/5.11      (![X0 : $i, X1 : $i]:
% 4.86/5.11         ((v2_struct_0 @ X0)
% 4.86/5.11          | ~ (l3_lattices @ X0)
% 4.86/5.11          | ~ (v4_lattice3 @ X0)
% 4.86/5.11          | (r4_lattice3 @ X0 @ (sk_C_2 @ X1 @ X0) @ k1_xboole_0))),
% 4.86/5.11      inference('sup-', [status(thm)], ['13', '17'])).
% 4.86/5.11  thf('19', plain,
% 4.86/5.11      (![X23 : $i, X24 : $i]:
% 4.86/5.11         (~ (v4_lattice3 @ X23)
% 4.86/5.11          | (m1_subset_1 @ (sk_C_2 @ X24 @ X23) @ (u1_struct_0 @ X23))
% 4.86/5.11          | ~ (l3_lattices @ X23)
% 4.86/5.11          | (v2_struct_0 @ X23))),
% 4.86/5.11      inference('cnf', [status(esa)], [d18_lattice3])).
% 4.86/5.11  thf('20', plain,
% 4.86/5.11      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.86/5.11         ((v2_struct_0 @ X26)
% 4.86/5.11          | ~ (v10_lattices @ X26)
% 4.86/5.11          | ~ (v4_lattice3 @ X26)
% 4.86/5.11          | ~ (l3_lattices @ X26)
% 4.86/5.11          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 4.86/5.11          | ~ (r4_lattice3 @ X26 @ X27 @ X28)
% 4.86/5.11          | (m1_subset_1 @ (sk_D_2 @ X27 @ X28 @ X26) @ (u1_struct_0 @ X26))
% 4.86/5.11          | ((X27) = (k15_lattice3 @ X26 @ X28))
% 4.86/5.11          | ~ (l3_lattices @ X26)
% 4.86/5.11          | (v2_struct_0 @ X26))),
% 4.86/5.11      inference('cnf', [status(esa)], [d21_lattice3])).
% 4.86/5.11  thf('21', plain,
% 4.86/5.11      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.86/5.11         (((X27) = (k15_lattice3 @ X26 @ X28))
% 4.86/5.11          | (m1_subset_1 @ (sk_D_2 @ X27 @ X28 @ X26) @ (u1_struct_0 @ X26))
% 4.86/5.11          | ~ (r4_lattice3 @ X26 @ X27 @ X28)
% 4.86/5.11          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 4.86/5.11          | ~ (l3_lattices @ X26)
% 4.86/5.11          | ~ (v4_lattice3 @ X26)
% 4.86/5.11          | ~ (v10_lattices @ X26)
% 4.86/5.11          | (v2_struct_0 @ X26))),
% 4.86/5.11      inference('simplify', [status(thm)], ['20'])).
% 4.86/5.11  thf('22', plain,
% 4.86/5.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.86/5.11         ((v2_struct_0 @ X0)
% 4.86/5.11          | ~ (l3_lattices @ X0)
% 4.86/5.11          | ~ (v4_lattice3 @ X0)
% 4.86/5.11          | (v2_struct_0 @ X0)
% 4.86/5.11          | ~ (v10_lattices @ X0)
% 4.86/5.11          | ~ (v4_lattice3 @ X0)
% 4.86/5.11          | ~ (l3_lattices @ X0)
% 4.86/5.11          | ~ (r4_lattice3 @ X0 @ (sk_C_2 @ X1 @ X0) @ X2)
% 4.86/5.11          | (m1_subset_1 @ (sk_D_2 @ (sk_C_2 @ X1 @ X0) @ X2 @ X0) @ 
% 4.86/5.11             (u1_struct_0 @ X0))
% 4.86/5.11          | ((sk_C_2 @ X1 @ X0) = (k15_lattice3 @ X0 @ X2)))),
% 4.86/5.11      inference('sup-', [status(thm)], ['19', '21'])).
% 4.86/5.11  thf('23', plain,
% 4.86/5.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.86/5.11         (((sk_C_2 @ X1 @ X0) = (k15_lattice3 @ X0 @ X2))
% 4.86/5.11          | (m1_subset_1 @ (sk_D_2 @ (sk_C_2 @ X1 @ X0) @ X2 @ X0) @ 
% 4.86/5.11             (u1_struct_0 @ X0))
% 4.95/5.11          | ~ (r4_lattice3 @ X0 @ (sk_C_2 @ X1 @ X0) @ X2)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['22'])).
% 4.95/5.11  thf('24', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         (~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | (m1_subset_1 @ (sk_D_2 @ (sk_C_2 @ X1 @ X0) @ k1_xboole_0 @ X0) @ 
% 4.95/5.11             (u1_struct_0 @ X0))
% 4.95/5.11          | ((sk_C_2 @ X1 @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 4.95/5.11      inference('sup-', [status(thm)], ['18', '23'])).
% 4.95/5.11  thf('25', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         (((sk_C_2 @ X1 @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | (m1_subset_1 @ (sk_D_2 @ (sk_C_2 @ X1 @ X0) @ k1_xboole_0 @ X0) @ 
% 4.95/5.11             (u1_struct_0 @ X0))
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['24'])).
% 4.95/5.11  thf('26', plain,
% 4.95/5.11      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.95/5.11         (~ (v4_lattice3 @ X23)
% 4.95/5.11          | ~ (r4_lattice3 @ X23 @ X25 @ X24)
% 4.95/5.11          | (r1_lattices @ X23 @ (sk_C_2 @ X24 @ X23) @ X25)
% 4.95/5.11          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 4.95/5.11          | ~ (l3_lattices @ X23)
% 4.95/5.11          | (v2_struct_0 @ X23))),
% 4.95/5.11      inference('cnf', [status(esa)], [d18_lattice3])).
% 4.95/5.11  thf('27', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.95/5.11         (~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ((sk_C_2 @ X1 @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (r1_lattices @ X0 @ (sk_C_2 @ X2 @ X0) @ 
% 4.95/5.11             (sk_D_2 @ (sk_C_2 @ X1 @ X0) @ k1_xboole_0 @ X0))
% 4.95/5.11          | ~ (r4_lattice3 @ X0 @ 
% 4.95/5.11               (sk_D_2 @ (sk_C_2 @ X1 @ X0) @ k1_xboole_0 @ X0) @ X2)
% 4.95/5.11          | ~ (v4_lattice3 @ X0))),
% 4.95/5.11      inference('sup-', [status(thm)], ['25', '26'])).
% 4.95/5.11  thf('28', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.95/5.11         (~ (r4_lattice3 @ X0 @ 
% 4.95/5.11             (sk_D_2 @ (sk_C_2 @ X1 @ X0) @ k1_xboole_0 @ X0) @ X2)
% 4.95/5.11          | (r1_lattices @ X0 @ (sk_C_2 @ X2 @ X0) @ 
% 4.95/5.11             (sk_D_2 @ (sk_C_2 @ X1 @ X0) @ k1_xboole_0 @ X0))
% 4.95/5.11          | ((sk_C_2 @ X1 @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['27'])).
% 4.95/5.11  thf('29', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ((sk_C_2 @ k1_xboole_0 @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ((sk_C_2 @ k1_xboole_0 @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | (r1_lattices @ X0 @ (sk_C_2 @ k1_xboole_0 @ X0) @ 
% 4.95/5.11             (sk_D_2 @ (sk_C_2 @ k1_xboole_0 @ X0) @ k1_xboole_0 @ X0)))),
% 4.95/5.11      inference('sup-', [status(thm)], ['9', '28'])).
% 4.95/5.11  thf('30', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         ((r1_lattices @ X0 @ (sk_C_2 @ k1_xboole_0 @ X0) @ 
% 4.95/5.11           (sk_D_2 @ (sk_C_2 @ k1_xboole_0 @ X0) @ k1_xboole_0 @ X0))
% 4.95/5.11          | ((sk_C_2 @ k1_xboole_0 @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['29'])).
% 4.95/5.11  thf('31', plain,
% 4.95/5.11      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X26)
% 4.95/5.11          | ~ (v10_lattices @ X26)
% 4.95/5.11          | ~ (v4_lattice3 @ X26)
% 4.95/5.11          | ~ (l3_lattices @ X26)
% 4.95/5.11          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 4.95/5.11          | ~ (r4_lattice3 @ X26 @ X27 @ X28)
% 4.95/5.11          | ~ (r1_lattices @ X26 @ X27 @ (sk_D_2 @ X27 @ X28 @ X26))
% 4.95/5.11          | ((X27) = (k15_lattice3 @ X26 @ X28))
% 4.95/5.11          | ~ (l3_lattices @ X26)
% 4.95/5.11          | (v2_struct_0 @ X26))),
% 4.95/5.11      inference('cnf', [status(esa)], [d21_lattice3])).
% 4.95/5.11  thf('32', plain,
% 4.95/5.11      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.95/5.11         (((X27) = (k15_lattice3 @ X26 @ X28))
% 4.95/5.11          | ~ (r1_lattices @ X26 @ X27 @ (sk_D_2 @ X27 @ X28 @ X26))
% 4.95/5.11          | ~ (r4_lattice3 @ X26 @ X27 @ X28)
% 4.95/5.11          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 4.95/5.11          | ~ (l3_lattices @ X26)
% 4.95/5.11          | ~ (v4_lattice3 @ X26)
% 4.95/5.11          | ~ (v10_lattices @ X26)
% 4.95/5.11          | (v2_struct_0 @ X26))),
% 4.95/5.11      inference('simplify', [status(thm)], ['31'])).
% 4.95/5.11  thf('33', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ((sk_C_2 @ k1_xboole_0 @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (m1_subset_1 @ (sk_C_2 @ k1_xboole_0 @ X0) @ (u1_struct_0 @ X0))
% 4.95/5.11          | ~ (r4_lattice3 @ X0 @ (sk_C_2 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 4.95/5.11          | ((sk_C_2 @ k1_xboole_0 @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 4.95/5.11      inference('sup-', [status(thm)], ['30', '32'])).
% 4.95/5.11  thf('34', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (~ (r4_lattice3 @ X0 @ (sk_C_2 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 4.95/5.11          | ~ (m1_subset_1 @ (sk_C_2 @ k1_xboole_0 @ X0) @ (u1_struct_0 @ X0))
% 4.95/5.11          | ((sk_C_2 @ k1_xboole_0 @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['33'])).
% 4.95/5.11  thf('35', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ((sk_C_2 @ k1_xboole_0 @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (m1_subset_1 @ (sk_C_2 @ k1_xboole_0 @ X0) @ (u1_struct_0 @ X0)))),
% 4.95/5.11      inference('sup-', [status(thm)], ['1', '34'])).
% 4.95/5.11  thf('36', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (~ (m1_subset_1 @ (sk_C_2 @ k1_xboole_0 @ X0) @ (u1_struct_0 @ X0))
% 4.95/5.11          | ((sk_C_2 @ k1_xboole_0 @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['35'])).
% 4.95/5.11  thf('37', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ((sk_C_2 @ k1_xboole_0 @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 4.95/5.11      inference('sup-', [status(thm)], ['0', '36'])).
% 4.95/5.11  thf('38', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (((sk_C_2 @ k1_xboole_0 @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['37'])).
% 4.95/5.11  thf('39', plain,
% 4.95/5.11      (![X23 : $i, X24 : $i]:
% 4.95/5.11         (~ (v4_lattice3 @ X23)
% 4.95/5.11          | (m1_subset_1 @ (sk_C_2 @ X24 @ X23) @ (u1_struct_0 @ X23))
% 4.95/5.11          | ~ (l3_lattices @ X23)
% 4.95/5.11          | (v2_struct_0 @ X23))),
% 4.95/5.11      inference('cnf', [status(esa)], [d18_lattice3])).
% 4.95/5.11  thf(d13_lattices, axiom,
% 4.95/5.11    (![A:$i]:
% 4.95/5.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 4.95/5.11       ( ( v13_lattices @ A ) <=>
% 4.95/5.11         ( ?[B:$i]:
% 4.95/5.11           ( ( ![C:$i]:
% 4.95/5.11               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.95/5.11                 ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 4.95/5.11                   ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) & 
% 4.95/5.11             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 4.95/5.11  thf('40', plain,
% 4.95/5.11      (![X14 : $i, X15 : $i]:
% 4.95/5.11         ((m1_subset_1 @ (sk_C_1 @ X14 @ X15) @ (u1_struct_0 @ X15))
% 4.95/5.11          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 4.95/5.11          | (v13_lattices @ X15)
% 4.95/5.11          | ~ (l1_lattices @ X15)
% 4.95/5.11          | (v2_struct_0 @ X15))),
% 4.95/5.11      inference('cnf', [status(esa)], [d13_lattices])).
% 4.95/5.11  thf('41', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | (m1_subset_1 @ (sk_C_1 @ (sk_C_2 @ X1 @ X0) @ X0) @ 
% 4.95/5.11             (u1_struct_0 @ X0)))),
% 4.95/5.11      inference('sup-', [status(thm)], ['39', '40'])).
% 4.95/5.11  thf('42', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         ((m1_subset_1 @ (sk_C_1 @ (sk_C_2 @ X1 @ X0) @ X0) @ 
% 4.95/5.11           (u1_struct_0 @ X0))
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['41'])).
% 4.95/5.11  thf('43', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         ((m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 4.95/5.11           (u1_struct_0 @ X0))
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0))),
% 4.95/5.11      inference('sup+', [status(thm)], ['38', '42'])).
% 4.95/5.11  thf('44', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         ((v13_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | (m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 4.95/5.11             (u1_struct_0 @ X0)))),
% 4.95/5.11      inference('simplify', [status(thm)], ['43'])).
% 4.95/5.11  thf('45', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (((sk_C_2 @ k1_xboole_0 @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['37'])).
% 4.95/5.11  thf('46', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (((sk_C_2 @ k1_xboole_0 @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['37'])).
% 4.95/5.11  thf('47', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         ((m1_subset_1 @ (sk_C_1 @ (sk_C_2 @ X1 @ X0) @ X0) @ 
% 4.95/5.11           (u1_struct_0 @ X0))
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['41'])).
% 4.95/5.11  thf('48', plain,
% 4.95/5.11      (![X17 : $i, X18 : $i, X21 : $i]:
% 4.95/5.11         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 4.95/5.11          | (r2_hidden @ (sk_D @ X21 @ X17 @ X18) @ X21)
% 4.95/5.11          | (r4_lattice3 @ X18 @ X17 @ X21)
% 4.95/5.11          | ~ (l3_lattices @ X18)
% 4.95/5.11          | (v2_struct_0 @ X18))),
% 4.95/5.11      inference('cnf', [status(esa)], [d17_lattice3])).
% 4.95/5.11  thf('49', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (r4_lattice3 @ X0 @ (sk_C_1 @ (sk_C_2 @ X1 @ X0) @ X0) @ X2)
% 4.95/5.11          | (r2_hidden @ 
% 4.95/5.11             (sk_D @ X2 @ (sk_C_1 @ (sk_C_2 @ X1 @ X0) @ X0) @ X0) @ X2))),
% 4.95/5.11      inference('sup-', [status(thm)], ['47', '48'])).
% 4.95/5.11  thf('50', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.95/5.11         ((r2_hidden @ (sk_D @ X2 @ (sk_C_1 @ (sk_C_2 @ X1 @ X0) @ X0) @ X0) @ 
% 4.95/5.11           X2)
% 4.95/5.11          | (r4_lattice3 @ X0 @ (sk_C_1 @ (sk_C_2 @ X1 @ X0) @ X0) @ X2)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['49'])).
% 4.95/5.11  thf('51', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 4.95/5.11      inference('sup-', [status(thm)], ['15', '16'])).
% 4.95/5.11  thf('52', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | (r4_lattice3 @ X0 @ (sk_C_1 @ (sk_C_2 @ X1 @ X0) @ X0) @ 
% 4.95/5.11             k1_xboole_0))),
% 4.95/5.11      inference('sup-', [status(thm)], ['50', '51'])).
% 4.95/5.11  thf('53', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         ((m1_subset_1 @ (sk_C_1 @ (sk_C_2 @ X1 @ X0) @ X0) @ 
% 4.95/5.11           (u1_struct_0 @ X0))
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['41'])).
% 4.95/5.11  thf('54', plain,
% 4.95/5.11      (![X23 : $i, X24 : $i, X25 : $i]:
% 4.95/5.11         (~ (v4_lattice3 @ X23)
% 4.95/5.11          | ~ (r4_lattice3 @ X23 @ X25 @ X24)
% 4.95/5.11          | (r1_lattices @ X23 @ (sk_C_2 @ X24 @ X23) @ X25)
% 4.95/5.11          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 4.95/5.11          | ~ (l3_lattices @ X23)
% 4.95/5.11          | (v2_struct_0 @ X23))),
% 4.95/5.11      inference('cnf', [status(esa)], [d18_lattice3])).
% 4.95/5.11  thf('55', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (r1_lattices @ X0 @ (sk_C_2 @ X2 @ X0) @ 
% 4.95/5.11             (sk_C_1 @ (sk_C_2 @ X1 @ X0) @ X0))
% 4.95/5.11          | ~ (r4_lattice3 @ X0 @ (sk_C_1 @ (sk_C_2 @ X1 @ X0) @ X0) @ X2)
% 4.95/5.11          | ~ (v4_lattice3 @ X0))),
% 4.95/5.11      inference('sup-', [status(thm)], ['53', '54'])).
% 4.95/5.11  thf('56', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.95/5.11         (~ (r4_lattice3 @ X0 @ (sk_C_1 @ (sk_C_2 @ X1 @ X0) @ X0) @ X2)
% 4.95/5.11          | (r1_lattices @ X0 @ (sk_C_2 @ X2 @ X0) @ 
% 4.95/5.11             (sk_C_1 @ (sk_C_2 @ X1 @ X0) @ X0))
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['55'])).
% 4.95/5.11  thf('57', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         ((v13_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | (r1_lattices @ X0 @ (sk_C_2 @ k1_xboole_0 @ X0) @ 
% 4.95/5.11             (sk_C_1 @ (sk_C_2 @ X1 @ X0) @ X0)))),
% 4.95/5.11      inference('sup-', [status(thm)], ['52', '56'])).
% 4.95/5.11  thf('58', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         ((r1_lattices @ X0 @ (sk_C_2 @ k1_xboole_0 @ X0) @ 
% 4.95/5.11           (sk_C_1 @ (sk_C_2 @ X1 @ X0) @ X0))
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['57'])).
% 4.95/5.11  thf('59', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         ((r1_lattices @ X0 @ (sk_C_2 @ k1_xboole_0 @ X0) @ 
% 4.95/5.11           (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('sup+', [status(thm)], ['46', '58'])).
% 4.95/5.11  thf('60', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (~ (l1_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | (r1_lattices @ X0 @ (sk_C_2 @ k1_xboole_0 @ X0) @ 
% 4.95/5.11             (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0)))),
% 4.95/5.11      inference('simplify', [status(thm)], ['59'])).
% 4.95/5.11  thf('61', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         ((r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.95/5.11           (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0))),
% 4.95/5.11      inference('sup+', [status(thm)], ['45', '60'])).
% 4.95/5.11  thf('62', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (~ (l1_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.95/5.11             (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0)))),
% 4.95/5.11      inference('simplify', [status(thm)], ['61'])).
% 4.95/5.11  thf('63', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (((sk_C_2 @ k1_xboole_0 @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['37'])).
% 4.95/5.11  thf('64', plain,
% 4.95/5.11      (![X23 : $i, X24 : $i]:
% 4.95/5.11         (~ (v4_lattice3 @ X23)
% 4.95/5.11          | (m1_subset_1 @ (sk_C_2 @ X24 @ X23) @ (u1_struct_0 @ X23))
% 4.95/5.11          | ~ (l3_lattices @ X23)
% 4.95/5.11          | (v2_struct_0 @ X23))),
% 4.95/5.11      inference('cnf', [status(esa)], [d18_lattice3])).
% 4.95/5.11  thf('65', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         ((m1_subset_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ (u1_struct_0 @ X0))
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0))),
% 4.95/5.11      inference('sup+', [status(thm)], ['63', '64'])).
% 4.95/5.11  thf('66', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | (m1_subset_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.95/5.11             (u1_struct_0 @ X0)))),
% 4.95/5.11      inference('simplify', [status(thm)], ['65'])).
% 4.95/5.11  thf(t21_lattices, axiom,
% 4.95/5.11    (![A:$i]:
% 4.95/5.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 4.95/5.11         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 4.95/5.11       ( ![B:$i]:
% 4.95/5.11         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 4.95/5.11           ( ![C:$i]:
% 4.95/5.11             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.95/5.11               ( ( r1_lattices @ A @ B @ C ) <=>
% 4.95/5.11                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 4.95/5.11  thf('67', plain,
% 4.95/5.11      (![X11 : $i, X12 : $i, X13 : $i]:
% 4.95/5.11         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 4.95/5.11          | ~ (r1_lattices @ X12 @ X11 @ X13)
% 4.95/5.11          | ((k2_lattices @ X12 @ X11 @ X13) = (X11))
% 4.95/5.11          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 4.95/5.11          | ~ (l3_lattices @ X12)
% 4.95/5.11          | ~ (v9_lattices @ X12)
% 4.95/5.11          | ~ (v8_lattices @ X12)
% 4.95/5.11          | (v2_struct_0 @ X12))),
% 4.95/5.11      inference('cnf', [status(esa)], [t21_lattices])).
% 4.95/5.11  thf('68', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (v8_lattices @ X0)
% 4.95/5.11          | ~ (v9_lattices @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 4.95/5.11          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X1)
% 4.95/5.11              = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X1))),
% 4.95/5.11      inference('sup-', [status(thm)], ['66', '67'])).
% 4.95/5.11  thf('69', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X1)
% 4.95/5.11          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X1)
% 4.95/5.11              = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 4.95/5.11          | ~ (v9_lattices @ X0)
% 4.95/5.11          | ~ (v8_lattices @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['68'])).
% 4.95/5.11  thf('70', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v8_lattices @ X0)
% 4.95/5.11          | ~ (v9_lattices @ X0)
% 4.95/5.11          | ~ (m1_subset_1 @ 
% 4.95/5.11               (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 4.95/5.11               (u1_struct_0 @ X0))
% 4.95/5.11          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.95/5.11              (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 4.95/5.11              = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 4.95/5.11      inference('sup-', [status(thm)], ['62', '69'])).
% 4.95/5.11  thf('71', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.95/5.11            (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 4.95/5.11            = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (m1_subset_1 @ 
% 4.95/5.11               (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 4.95/5.11               (u1_struct_0 @ X0))
% 4.95/5.11          | ~ (v9_lattices @ X0)
% 4.95/5.11          | ~ (v8_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['70'])).
% 4.95/5.11  thf('72', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (v8_lattices @ X0)
% 4.95/5.11          | ~ (v9_lattices @ X0)
% 4.95/5.11          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.95/5.11              (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 4.95/5.11              = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 4.95/5.11      inference('sup-', [status(thm)], ['44', '71'])).
% 4.95/5.11  thf('73', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.95/5.11            (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 4.95/5.11            = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v9_lattices @ X0)
% 4.95/5.11          | ~ (v8_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['72'])).
% 4.95/5.11  thf('74', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         ((v13_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | (m1_subset_1 @ (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 4.95/5.11             (u1_struct_0 @ X0)))),
% 4.95/5.11      inference('simplify', [status(thm)], ['43'])).
% 4.95/5.11  thf('75', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | (m1_subset_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.95/5.11             (u1_struct_0 @ X0)))),
% 4.95/5.11      inference('simplify', [status(thm)], ['65'])).
% 4.95/5.11  thf(d6_lattices, axiom,
% 4.95/5.11    (![A:$i]:
% 4.95/5.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 4.95/5.11       ( ( v6_lattices @ A ) <=>
% 4.95/5.11         ( ![B:$i]:
% 4.95/5.11           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 4.95/5.11             ( ![C:$i]:
% 4.95/5.11               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.95/5.11                 ( ( k2_lattices @ A @ B @ C ) = ( k2_lattices @ A @ C @ B ) ) ) ) ) ) ) ))).
% 4.95/5.11  thf('76', plain,
% 4.95/5.11      (![X30 : $i, X31 : $i, X32 : $i]:
% 4.95/5.11         (~ (v6_lattices @ X30)
% 4.95/5.11          | ~ (m1_subset_1 @ X31 @ (u1_struct_0 @ X30))
% 4.95/5.11          | ((k2_lattices @ X30 @ X32 @ X31) = (k2_lattices @ X30 @ X31 @ X32))
% 4.95/5.11          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X30))
% 4.95/5.11          | ~ (l1_lattices @ X30)
% 4.95/5.11          | (v2_struct_0 @ X30))),
% 4.95/5.11      inference('cnf', [status(esa)], [d6_lattices])).
% 4.95/5.11  thf('77', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 4.95/5.11          | ((k2_lattices @ X0 @ X1 @ (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X1))
% 4.95/5.11          | ~ (v6_lattices @ X0))),
% 4.95/5.11      inference('sup-', [status(thm)], ['75', '76'])).
% 4.95/5.11  thf('78', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         (~ (v6_lattices @ X0)
% 4.95/5.11          | ((k2_lattices @ X0 @ X1 @ (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X1))
% 4.95/5.11          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['77'])).
% 4.95/5.11  thf('79', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ((k2_lattices @ X0 @ 
% 4.95/5.11              (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 4.95/5.11              (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.95/5.11                 (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0)))
% 4.95/5.11          | ~ (v6_lattices @ X0))),
% 4.95/5.11      inference('sup-', [status(thm)], ['74', '78'])).
% 4.95/5.11  thf('80', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (~ (v6_lattices @ X0)
% 4.95/5.11          | ((k2_lattices @ X0 @ 
% 4.95/5.11              (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 4.95/5.11              (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.95/5.11                 (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0)))
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['79'])).
% 4.95/5.11  thf('81', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | (m1_subset_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.95/5.11             (u1_struct_0 @ X0)))),
% 4.95/5.11      inference('simplify', [status(thm)], ['65'])).
% 4.95/5.11  thf('82', plain,
% 4.95/5.11      (![X14 : $i, X15 : $i]:
% 4.95/5.11         (((k2_lattices @ X15 @ (sk_C_1 @ X14 @ X15) @ X14) != (X14))
% 4.95/5.11          | ((k2_lattices @ X15 @ X14 @ (sk_C_1 @ X14 @ X15)) != (X14))
% 4.95/5.11          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 4.95/5.11          | (v13_lattices @ X15)
% 4.95/5.11          | ~ (l1_lattices @ X15)
% 4.95/5.11          | (v2_struct_0 @ X15))),
% 4.95/5.11      inference('cnf', [status(esa)], [d13_lattices])).
% 4.95/5.11  thf('83', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.95/5.11              (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 4.95/5.11              != (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ((k2_lattices @ X0 @ 
% 4.95/5.11              (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 4.95/5.11              (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11              != (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 4.95/5.11      inference('sup-', [status(thm)], ['81', '82'])).
% 4.95/5.11  thf('84', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (((k2_lattices @ X0 @ 
% 4.95/5.11            (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 4.95/5.11            (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.95/5.11              (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 4.95/5.11              != (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['83'])).
% 4.95/5.11  thf('85', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.95/5.11            (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 4.95/5.11            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ~ (v6_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.95/5.11              (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 4.95/5.11              != (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 4.95/5.11      inference('sup-', [status(thm)], ['80', '84'])).
% 4.95/5.11  thf('86', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (~ (v6_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.95/5.11              (sk_C_1 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 4.95/5.11              != (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 4.95/5.11      inference('simplify', [status(thm)], ['85'])).
% 4.95/5.11  thf('87', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 4.95/5.11            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ~ (v8_lattices @ X0)
% 4.95/5.11          | ~ (v9_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ~ (v6_lattices @ X0))),
% 4.95/5.11      inference('sup-', [status(thm)], ['73', '86'])).
% 4.95/5.11  thf('88', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (~ (v6_lattices @ X0)
% 4.95/5.11          | ~ (v9_lattices @ X0)
% 4.95/5.11          | ~ (v8_lattices @ X0)
% 4.95/5.11          | (v13_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['87'])).
% 4.95/5.11  thf(t50_lattice3, conjecture,
% 4.95/5.11    (![A:$i]:
% 4.95/5.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 4.95/5.11         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 4.95/5.11       ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 4.95/5.11         ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 4.95/5.11         ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ))).
% 4.95/5.11  thf(zf_stmt_0, negated_conjecture,
% 4.95/5.11    (~( ![A:$i]:
% 4.95/5.11        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 4.95/5.11            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 4.95/5.11          ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 4.95/5.11            ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 4.95/5.11            ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ) )),
% 4.95/5.11    inference('cnf.neg', [status(esa)], [t50_lattice3])).
% 4.95/5.11  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('90', plain,
% 4.95/5.11      ((~ (l3_lattices @ sk_A)
% 4.95/5.11        | ~ (v4_lattice3 @ sk_A)
% 4.95/5.11        | ~ (v10_lattices @ sk_A)
% 4.95/5.11        | ~ (l1_lattices @ sk_A)
% 4.95/5.11        | (v13_lattices @ sk_A)
% 4.95/5.11        | ~ (v8_lattices @ sk_A)
% 4.95/5.11        | ~ (v9_lattices @ sk_A)
% 4.95/5.11        | ~ (v6_lattices @ sk_A))),
% 4.95/5.11      inference('sup-', [status(thm)], ['88', '89'])).
% 4.95/5.11  thf('91', plain, ((l3_lattices @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('92', plain, ((v4_lattice3 @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('93', plain, ((v10_lattices @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('94', plain, ((l3_lattices @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf(dt_l3_lattices, axiom,
% 4.95/5.11    (![A:$i]:
% 4.95/5.11     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 4.95/5.11  thf('95', plain,
% 4.95/5.11      (![X10 : $i]: ((l1_lattices @ X10) | ~ (l3_lattices @ X10))),
% 4.95/5.11      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 4.95/5.11  thf('96', plain, ((l1_lattices @ sk_A)),
% 4.95/5.11      inference('sup-', [status(thm)], ['94', '95'])).
% 4.95/5.11  thf(cc1_lattices, axiom,
% 4.95/5.11    (![A:$i]:
% 4.95/5.11     ( ( l3_lattices @ A ) =>
% 4.95/5.11       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 4.95/5.11         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 4.95/5.11           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 4.95/5.11           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 4.95/5.11  thf('97', plain,
% 4.95/5.11      (![X5 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X5)
% 4.95/5.11          | ~ (v10_lattices @ X5)
% 4.95/5.11          | (v8_lattices @ X5)
% 4.95/5.11          | ~ (l3_lattices @ X5))),
% 4.95/5.11      inference('cnf', [status(esa)], [cc1_lattices])).
% 4.95/5.11  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('99', plain,
% 4.95/5.11      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 4.95/5.11      inference('sup-', [status(thm)], ['97', '98'])).
% 4.95/5.11  thf('100', plain, ((l3_lattices @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('101', plain, ((v10_lattices @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('102', plain, ((v8_lattices @ sk_A)),
% 4.95/5.11      inference('demod', [status(thm)], ['99', '100', '101'])).
% 4.95/5.11  thf('103', plain,
% 4.95/5.11      (![X5 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X5)
% 4.95/5.11          | ~ (v10_lattices @ X5)
% 4.95/5.11          | (v9_lattices @ X5)
% 4.95/5.11          | ~ (l3_lattices @ X5))),
% 4.95/5.11      inference('cnf', [status(esa)], [cc1_lattices])).
% 4.95/5.11  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('105', plain,
% 4.95/5.11      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 4.95/5.11      inference('sup-', [status(thm)], ['103', '104'])).
% 4.95/5.11  thf('106', plain, ((l3_lattices @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('107', plain, ((v10_lattices @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('108', plain, ((v9_lattices @ sk_A)),
% 4.95/5.11      inference('demod', [status(thm)], ['105', '106', '107'])).
% 4.95/5.11  thf('109', plain,
% 4.95/5.11      (![X5 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X5)
% 4.95/5.11          | ~ (v10_lattices @ X5)
% 4.95/5.11          | (v6_lattices @ X5)
% 4.95/5.11          | ~ (l3_lattices @ X5))),
% 4.95/5.11      inference('cnf', [status(esa)], [cc1_lattices])).
% 4.95/5.11  thf('110', plain, (~ (v2_struct_0 @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('111', plain,
% 4.95/5.11      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 4.95/5.11      inference('sup-', [status(thm)], ['109', '110'])).
% 4.95/5.11  thf('112', plain, ((l3_lattices @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('113', plain, ((v10_lattices @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('114', plain, ((v6_lattices @ sk_A)),
% 4.95/5.11      inference('demod', [status(thm)], ['111', '112', '113'])).
% 4.95/5.11  thf('115', plain, ((v13_lattices @ sk_A)),
% 4.95/5.11      inference('demod', [status(thm)],
% 4.95/5.11                ['90', '91', '92', '93', '96', '102', '108', '114'])).
% 4.95/5.11  thf(dt_k5_lattices, axiom,
% 4.95/5.11    (![A:$i]:
% 4.95/5.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 4.95/5.11       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 4.95/5.11  thf('116', plain,
% 4.95/5.11      (![X9 : $i]:
% 4.95/5.11         ((m1_subset_1 @ (k5_lattices @ X9) @ (u1_struct_0 @ X9))
% 4.95/5.11          | ~ (l1_lattices @ X9)
% 4.95/5.11          | (v2_struct_0 @ X9))),
% 4.95/5.11      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 4.95/5.11  thf('117', plain,
% 4.95/5.11      (![X9 : $i]:
% 4.95/5.11         ((m1_subset_1 @ (k5_lattices @ X9) @ (u1_struct_0 @ X9))
% 4.95/5.11          | ~ (l1_lattices @ X9)
% 4.95/5.11          | (v2_struct_0 @ X9))),
% 4.95/5.11      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 4.95/5.11  thf('118', plain,
% 4.95/5.11      (![X17 : $i, X18 : $i, X21 : $i]:
% 4.95/5.11         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 4.95/5.11          | (r2_hidden @ (sk_D @ X21 @ X17 @ X18) @ X21)
% 4.95/5.11          | (r4_lattice3 @ X18 @ X17 @ X21)
% 4.95/5.11          | ~ (l3_lattices @ X18)
% 4.95/5.11          | (v2_struct_0 @ X18))),
% 4.95/5.11      inference('cnf', [status(esa)], [d17_lattice3])).
% 4.95/5.11  thf('119', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ X1)
% 4.95/5.11          | (r2_hidden @ (sk_D @ X1 @ (k5_lattices @ X0) @ X0) @ X1))),
% 4.95/5.11      inference('sup-', [status(thm)], ['117', '118'])).
% 4.95/5.11  thf('120', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         ((r2_hidden @ (sk_D @ X1 @ (k5_lattices @ X0) @ X0) @ X1)
% 4.95/5.11          | (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ X1)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['119'])).
% 4.95/5.11  thf('121', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 4.95/5.11      inference('sup-', [status(thm)], ['15', '16'])).
% 4.95/5.11  thf('122', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ k1_xboole_0))),
% 4.95/5.11      inference('sup-', [status(thm)], ['120', '121'])).
% 4.95/5.11  thf('123', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ k1_xboole_0))),
% 4.95/5.11      inference('sup-', [status(thm)], ['120', '121'])).
% 4.95/5.11  thf('124', plain,
% 4.95/5.11      (![X9 : $i]:
% 4.95/5.11         ((m1_subset_1 @ (k5_lattices @ X9) @ (u1_struct_0 @ X9))
% 4.95/5.11          | ~ (l1_lattices @ X9)
% 4.95/5.11          | (v2_struct_0 @ X9))),
% 4.95/5.11      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 4.95/5.11  thf('125', plain,
% 4.95/5.11      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.95/5.11         (((X27) = (k15_lattice3 @ X26 @ X28))
% 4.95/5.11          | (m1_subset_1 @ (sk_D_2 @ X27 @ X28 @ X26) @ (u1_struct_0 @ X26))
% 4.95/5.11          | ~ (r4_lattice3 @ X26 @ X27 @ X28)
% 4.95/5.11          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 4.95/5.11          | ~ (l3_lattices @ X26)
% 4.95/5.11          | ~ (v4_lattice3 @ X26)
% 4.95/5.11          | ~ (v10_lattices @ X26)
% 4.95/5.11          | (v2_struct_0 @ X26))),
% 4.95/5.11      inference('simplify', [status(thm)], ['20'])).
% 4.95/5.11  thf('126', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ X1)
% 4.95/5.11          | (m1_subset_1 @ (sk_D_2 @ (k5_lattices @ X0) @ X1 @ X0) @ 
% 4.95/5.11             (u1_struct_0 @ X0))
% 4.95/5.11          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ X1)))),
% 4.95/5.11      inference('sup-', [status(thm)], ['124', '125'])).
% 4.95/5.11  thf('127', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         (((k5_lattices @ X0) = (k15_lattice3 @ X0 @ X1))
% 4.95/5.11          | (m1_subset_1 @ (sk_D_2 @ (k5_lattices @ X0) @ X1 @ X0) @ 
% 4.95/5.11             (u1_struct_0 @ X0))
% 4.95/5.11          | ~ (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ X1)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['126'])).
% 4.95/5.11  thf('128', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (m1_subset_1 @ (sk_D_2 @ (k5_lattices @ X0) @ k1_xboole_0 @ X0) @ 
% 4.95/5.11             (u1_struct_0 @ X0))
% 4.95/5.11          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 4.95/5.11      inference('sup-', [status(thm)], ['123', '127'])).
% 4.95/5.11  thf('129', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | (m1_subset_1 @ (sk_D_2 @ (k5_lattices @ X0) @ k1_xboole_0 @ X0) @ 
% 4.95/5.11             (u1_struct_0 @ X0))
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['128'])).
% 4.95/5.11  thf('130', plain,
% 4.95/5.11      (![X9 : $i]:
% 4.95/5.11         ((m1_subset_1 @ (k5_lattices @ X9) @ (u1_struct_0 @ X9))
% 4.95/5.11          | ~ (l1_lattices @ X9)
% 4.95/5.11          | (v2_struct_0 @ X9))),
% 4.95/5.11      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 4.95/5.11  thf(d16_lattices, axiom,
% 4.95/5.11    (![A:$i]:
% 4.95/5.11     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 4.95/5.11       ( ( v13_lattices @ A ) =>
% 4.95/5.11         ( ![B:$i]:
% 4.95/5.11           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 4.95/5.11             ( ( ( B ) = ( k5_lattices @ A ) ) <=>
% 4.95/5.11               ( ![C:$i]:
% 4.95/5.11                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.95/5.11                   ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 4.95/5.11                     ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 4.95/5.11  thf('131', plain,
% 4.95/5.11      (![X6 : $i, X7 : $i, X8 : $i]:
% 4.95/5.11         (~ (v13_lattices @ X6)
% 4.95/5.11          | ~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X6))
% 4.95/5.11          | ((X7) != (k5_lattices @ X6))
% 4.95/5.11          | ((k2_lattices @ X6 @ X7 @ X8) = (X7))
% 4.95/5.11          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 4.95/5.11          | ~ (l1_lattices @ X6)
% 4.95/5.11          | (v2_struct_0 @ X6))),
% 4.95/5.11      inference('cnf', [status(esa)], [d16_lattices])).
% 4.95/5.11  thf('132', plain,
% 4.95/5.11      (![X6 : $i, X8 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X6)
% 4.95/5.11          | ~ (l1_lattices @ X6)
% 4.95/5.11          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X6))
% 4.95/5.11          | ((k2_lattices @ X6 @ (k5_lattices @ X6) @ X8) = (k5_lattices @ X6))
% 4.95/5.11          | ~ (m1_subset_1 @ (k5_lattices @ X6) @ (u1_struct_0 @ X6))
% 4.95/5.11          | ~ (v13_lattices @ X6))),
% 4.95/5.11      inference('simplify', [status(thm)], ['131'])).
% 4.95/5.11  thf('133', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (v13_lattices @ X0)
% 4.95/5.11          | ((k2_lattices @ X0 @ (k5_lattices @ X0) @ X1) = (k5_lattices @ X0))
% 4.95/5.11          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('sup-', [status(thm)], ['130', '132'])).
% 4.95/5.11  thf('134', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 4.95/5.11          | ((k2_lattices @ X0 @ (k5_lattices @ X0) @ X1) = (k5_lattices @ X0))
% 4.95/5.11          | ~ (v13_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['133'])).
% 4.95/5.11  thf('135', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (v13_lattices @ X0)
% 4.95/5.11          | ((k2_lattices @ X0 @ (k5_lattices @ X0) @ 
% 4.95/5.11              (sk_D_2 @ (k5_lattices @ X0) @ k1_xboole_0 @ X0))
% 4.95/5.11              = (k5_lattices @ X0)))),
% 4.95/5.11      inference('sup-', [status(thm)], ['129', '134'])).
% 4.95/5.11  thf('136', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (((k2_lattices @ X0 @ (k5_lattices @ X0) @ 
% 4.95/5.11            (sk_D_2 @ (k5_lattices @ X0) @ k1_xboole_0 @ X0))
% 4.95/5.11            = (k5_lattices @ X0))
% 4.95/5.11          | ~ (v13_lattices @ X0)
% 4.95/5.11          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['135'])).
% 4.95/5.11  thf('137', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | (m1_subset_1 @ (sk_D_2 @ (k5_lattices @ X0) @ k1_xboole_0 @ X0) @ 
% 4.95/5.11             (u1_struct_0 @ X0))
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['128'])).
% 4.95/5.11  thf('138', plain,
% 4.95/5.11      (![X9 : $i]:
% 4.95/5.11         ((m1_subset_1 @ (k5_lattices @ X9) @ (u1_struct_0 @ X9))
% 4.95/5.11          | ~ (l1_lattices @ X9)
% 4.95/5.11          | (v2_struct_0 @ X9))),
% 4.95/5.11      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 4.95/5.11  thf('139', plain,
% 4.95/5.11      (![X11 : $i, X12 : $i, X13 : $i]:
% 4.95/5.11         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 4.95/5.11          | ((k2_lattices @ X12 @ X11 @ X13) != (X11))
% 4.95/5.11          | (r1_lattices @ X12 @ X11 @ X13)
% 4.95/5.11          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 4.95/5.11          | ~ (l3_lattices @ X12)
% 4.95/5.11          | ~ (v9_lattices @ X12)
% 4.95/5.11          | ~ (v8_lattices @ X12)
% 4.95/5.11          | (v2_struct_0 @ X12))),
% 4.95/5.11      inference('cnf', [status(esa)], [t21_lattices])).
% 4.95/5.11  thf('140', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (v8_lattices @ X0)
% 4.95/5.11          | ~ (v9_lattices @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 4.95/5.11          | (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 4.95/5.11          | ((k2_lattices @ X0 @ (k5_lattices @ X0) @ X1) != (k5_lattices @ X0)))),
% 4.95/5.11      inference('sup-', [status(thm)], ['138', '139'])).
% 4.95/5.11  thf('141', plain,
% 4.95/5.11      (![X0 : $i, X1 : $i]:
% 4.95/5.11         (((k2_lattices @ X0 @ (k5_lattices @ X0) @ X1) != (k5_lattices @ X0))
% 4.95/5.11          | (r1_lattices @ X0 @ (k5_lattices @ X0) @ X1)
% 4.95/5.11          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (v9_lattices @ X0)
% 4.95/5.11          | ~ (v8_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['140'])).
% 4.95/5.11  thf('142', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (v8_lattices @ X0)
% 4.95/5.11          | ~ (v9_lattices @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | (r1_lattices @ X0 @ (k5_lattices @ X0) @ 
% 4.95/5.11             (sk_D_2 @ (k5_lattices @ X0) @ k1_xboole_0 @ X0))
% 4.95/5.11          | ((k2_lattices @ X0 @ (k5_lattices @ X0) @ 
% 4.95/5.11              (sk_D_2 @ (k5_lattices @ X0) @ k1_xboole_0 @ X0))
% 4.95/5.11              != (k5_lattices @ X0)))),
% 4.95/5.11      inference('sup-', [status(thm)], ['137', '141'])).
% 4.95/5.11  thf('143', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (((k2_lattices @ X0 @ (k5_lattices @ X0) @ 
% 4.95/5.11            (sk_D_2 @ (k5_lattices @ X0) @ k1_xboole_0 @ X0))
% 4.95/5.11            != (k5_lattices @ X0))
% 4.95/5.11          | (r1_lattices @ X0 @ (k5_lattices @ X0) @ 
% 4.95/5.11             (sk_D_2 @ (k5_lattices @ X0) @ k1_xboole_0 @ X0))
% 4.95/5.11          | ~ (v9_lattices @ X0)
% 4.95/5.11          | ~ (v8_lattices @ X0)
% 4.95/5.11          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['142'])).
% 4.95/5.11  thf('144', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (((k5_lattices @ X0) != (k5_lattices @ X0))
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v13_lattices @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v8_lattices @ X0)
% 4.95/5.11          | ~ (v9_lattices @ X0)
% 4.95/5.11          | (r1_lattices @ X0 @ (k5_lattices @ X0) @ 
% 4.95/5.11             (sk_D_2 @ (k5_lattices @ X0) @ k1_xboole_0 @ X0)))),
% 4.95/5.11      inference('sup-', [status(thm)], ['136', '143'])).
% 4.95/5.11  thf('145', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         ((r1_lattices @ X0 @ (k5_lattices @ X0) @ 
% 4.95/5.11           (sk_D_2 @ (k5_lattices @ X0) @ k1_xboole_0 @ X0))
% 4.95/5.11          | ~ (v9_lattices @ X0)
% 4.95/5.11          | ~ (v8_lattices @ X0)
% 4.95/5.11          | ~ (v13_lattices @ X0)
% 4.95/5.11          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['144'])).
% 4.95/5.11  thf('146', plain,
% 4.95/5.11      (![X26 : $i, X27 : $i, X28 : $i]:
% 4.95/5.11         (((X27) = (k15_lattice3 @ X26 @ X28))
% 4.95/5.11          | ~ (r1_lattices @ X26 @ X27 @ (sk_D_2 @ X27 @ X28 @ X26))
% 4.95/5.11          | ~ (r4_lattice3 @ X26 @ X27 @ X28)
% 4.95/5.11          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X26))
% 4.95/5.11          | ~ (l3_lattices @ X26)
% 4.95/5.11          | ~ (v4_lattice3 @ X26)
% 4.95/5.11          | ~ (v10_lattices @ X26)
% 4.95/5.11          | (v2_struct_0 @ X26))),
% 4.95/5.11      inference('simplify', [status(thm)], ['31'])).
% 4.95/5.11  thf('147', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v13_lattices @ X0)
% 4.95/5.11          | ~ (v8_lattices @ X0)
% 4.95/5.11          | ~ (v9_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 4.95/5.11          | ~ (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ k1_xboole_0)
% 4.95/5.11          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 4.95/5.11      inference('sup-', [status(thm)], ['145', '146'])).
% 4.95/5.11  thf('148', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (~ (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ k1_xboole_0)
% 4.95/5.11          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 4.95/5.11          | ~ (v9_lattices @ X0)
% 4.95/5.11          | ~ (v8_lattices @ X0)
% 4.95/5.11          | ~ (v13_lattices @ X0)
% 4.95/5.11          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['147'])).
% 4.95/5.11  thf('149', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v13_lattices @ X0)
% 4.95/5.11          | ~ (v8_lattices @ X0)
% 4.95/5.11          | ~ (v9_lattices @ X0)
% 4.95/5.11          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0)))),
% 4.95/5.11      inference('sup-', [status(thm)], ['122', '148'])).
% 4.95/5.11  thf('150', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 4.95/5.11          | ~ (v9_lattices @ X0)
% 4.95/5.11          | ~ (v8_lattices @ X0)
% 4.95/5.11          | ~ (v13_lattices @ X0)
% 4.95/5.11          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['149'])).
% 4.95/5.11  thf('151', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         ((v2_struct_0 @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v13_lattices @ X0)
% 4.95/5.11          | ~ (v8_lattices @ X0)
% 4.95/5.11          | ~ (v9_lattices @ X0))),
% 4.95/5.11      inference('sup-', [status(thm)], ['116', '150'])).
% 4.95/5.11  thf('152', plain,
% 4.95/5.11      (![X0 : $i]:
% 4.95/5.11         (~ (v9_lattices @ X0)
% 4.95/5.11          | ~ (v8_lattices @ X0)
% 4.95/5.11          | ~ (v13_lattices @ X0)
% 4.95/5.11          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.95/5.11          | ~ (v4_lattice3 @ X0)
% 4.95/5.11          | ~ (v10_lattices @ X0)
% 4.95/5.11          | ~ (l3_lattices @ X0)
% 4.95/5.11          | ~ (l1_lattices @ X0)
% 4.95/5.11          | (v2_struct_0 @ X0))),
% 4.95/5.11      inference('simplify', [status(thm)], ['151'])).
% 4.95/5.11  thf('153', plain,
% 4.95/5.11      (((v2_struct_0 @ sk_A)
% 4.95/5.11        | ~ (v10_lattices @ sk_A)
% 4.95/5.11        | ~ (v13_lattices @ sk_A)
% 4.95/5.11        | ~ (l3_lattices @ sk_A)
% 4.95/5.11        | ((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('154', plain,
% 4.95/5.11      ((((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))
% 4.95/5.11         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 4.95/5.11      inference('split', [status(esa)], ['153'])).
% 4.95/5.11  thf('155', plain,
% 4.95/5.11      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 4.95/5.11         | (v2_struct_0 @ sk_A)
% 4.95/5.11         | ~ (l1_lattices @ sk_A)
% 4.95/5.11         | ~ (l3_lattices @ sk_A)
% 4.95/5.11         | ~ (v10_lattices @ sk_A)
% 4.95/5.11         | ~ (v4_lattice3 @ sk_A)
% 4.95/5.11         | ~ (v13_lattices @ sk_A)
% 4.95/5.11         | ~ (v8_lattices @ sk_A)
% 4.95/5.11         | ~ (v9_lattices @ sk_A)))
% 4.95/5.11         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 4.95/5.11      inference('sup-', [status(thm)], ['152', '154'])).
% 4.95/5.11  thf('156', plain, ((l1_lattices @ sk_A)),
% 4.95/5.11      inference('sup-', [status(thm)], ['94', '95'])).
% 4.95/5.11  thf('157', plain, ((l3_lattices @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('158', plain, ((v10_lattices @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('159', plain, ((v4_lattice3 @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('160', plain, ((v8_lattices @ sk_A)),
% 4.95/5.11      inference('demod', [status(thm)], ['99', '100', '101'])).
% 4.95/5.11  thf('161', plain, ((v9_lattices @ sk_A)),
% 4.95/5.11      inference('demod', [status(thm)], ['105', '106', '107'])).
% 4.95/5.11  thf('162', plain,
% 4.95/5.11      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 4.95/5.11         | (v2_struct_0 @ sk_A)
% 4.95/5.11         | ~ (v13_lattices @ sk_A)))
% 4.95/5.11         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 4.95/5.11      inference('demod', [status(thm)],
% 4.95/5.11                ['155', '156', '157', '158', '159', '160', '161'])).
% 4.95/5.11  thf('163', plain,
% 4.95/5.11      (((~ (v13_lattices @ sk_A) | (v2_struct_0 @ sk_A)))
% 4.95/5.11         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 4.95/5.11      inference('simplify', [status(thm)], ['162'])).
% 4.95/5.11  thf('164', plain, (~ (v2_struct_0 @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('165', plain,
% 4.95/5.11      ((~ (v13_lattices @ sk_A))
% 4.95/5.11         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 4.95/5.11      inference('clc', [status(thm)], ['163', '164'])).
% 4.95/5.11  thf('166', plain,
% 4.95/5.11      (($false)
% 4.95/5.11         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 4.95/5.11      inference('sup-', [status(thm)], ['115', '165'])).
% 4.95/5.11  thf('167', plain, (((v2_struct_0 @ sk_A)) <= (((v2_struct_0 @ sk_A)))),
% 4.95/5.11      inference('split', [status(esa)], ['153'])).
% 4.95/5.11  thf('168', plain, (~ (v2_struct_0 @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('169', plain, (~ ((v2_struct_0 @ sk_A))),
% 4.95/5.11      inference('sup-', [status(thm)], ['167', '168'])).
% 4.95/5.11  thf('170', plain, ((l3_lattices @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('171', plain, ((~ (l3_lattices @ sk_A)) <= (~ ((l3_lattices @ sk_A)))),
% 4.95/5.11      inference('split', [status(esa)], ['153'])).
% 4.95/5.11  thf('172', plain, (((l3_lattices @ sk_A))),
% 4.95/5.11      inference('sup-', [status(thm)], ['170', '171'])).
% 4.95/5.11  thf('173', plain, ((v10_lattices @ sk_A)),
% 4.95/5.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.95/5.11  thf('174', plain, ((~ (v10_lattices @ sk_A)) <= (~ ((v10_lattices @ sk_A)))),
% 4.95/5.11      inference('split', [status(esa)], ['153'])).
% 4.95/5.11  thf('175', plain, (((v10_lattices @ sk_A))),
% 4.95/5.11      inference('sup-', [status(thm)], ['173', '174'])).
% 4.95/5.11  thf('176', plain, ((v13_lattices @ sk_A)),
% 4.95/5.11      inference('demod', [status(thm)],
% 4.95/5.11                ['90', '91', '92', '93', '96', '102', '108', '114'])).
% 4.95/5.11  thf('177', plain, ((~ (v13_lattices @ sk_A)) <= (~ ((v13_lattices @ sk_A)))),
% 4.95/5.11      inference('split', [status(esa)], ['153'])).
% 4.95/5.11  thf('178', plain, (((v13_lattices @ sk_A))),
% 4.95/5.11      inference('sup-', [status(thm)], ['176', '177'])).
% 4.95/5.11  thf('179', plain,
% 4.95/5.11      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))) | 
% 4.95/5.11       ~ ((v13_lattices @ sk_A)) | ~ ((v10_lattices @ sk_A)) | 
% 4.95/5.11       ~ ((l3_lattices @ sk_A)) | ((v2_struct_0 @ sk_A))),
% 4.95/5.11      inference('split', [status(esa)], ['153'])).
% 4.95/5.11  thf('180', plain,
% 4.95/5.11      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 4.95/5.11      inference('sat_resolution*', [status(thm)],
% 4.95/5.11                ['169', '172', '175', '178', '179'])).
% 4.95/5.11  thf('181', plain, ($false),
% 4.95/5.11      inference('simpl_trail', [status(thm)], ['166', '180'])).
% 4.95/5.11  
% 4.95/5.11  % SZS output end Refutation
% 4.95/5.11  
% 4.95/5.12  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
