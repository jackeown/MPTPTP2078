%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3UqUZJCPKJ

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:37 EST 2020

% Result     : Theorem 2.59s
% Output     : Refutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 525 expanded)
%              Number of leaves         :   42 ( 163 expanded)
%              Depth                    :   24
%              Number of atoms          : 2497 (8730 expanded)
%              Number of equality atoms :   79 ( 282 expanded)
%              Maximal formula depth    :   23 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
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

thf('1',plain,(
    ! [X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( sk_C_2 @ X22 @ X23 ) @ ( u1_struct_0 @ X23 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( v13_lattices @ X23 )
      | ~ ( l1_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d13_lattices])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( m1_subset_1 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
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
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ( ( k15_lattice3 @ X36 @ ( k6_domain_1 @ ( u1_struct_0 @ X36 ) @ X35 ) )
        = X35 )
      | ~ ( l3_lattices @ X36 )
      | ~ ( v4_lattice3 @ X36 )
      | ~ ( v10_lattices @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
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
      | ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) )
        = ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) )
        = ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l3_lattices @ X28 )
      | ( v2_struct_0 @ X28 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X28 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) ),
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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X39 @ X40 @ X38 ) @ X40 )
      | ( r3_lattices @ X38 @ ( k15_lattice3 @ X38 @ X40 ) @ ( k15_lattice3 @ X38 @ X39 ) )
      | ~ ( l3_lattices @ X38 )
      | ~ ( v4_lattice3 @ X38 )
      | ~ ( v10_lattices @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t48_lattice3])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('10',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ X6 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ~ ( r2_hidden @ X8 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
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
    ! [X28: $i,X29: $i] :
      ( ~ ( l3_lattices @ X28 )
      | ( v2_struct_0 @ X28 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X28 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('15',plain,(
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

thf('16',plain,(
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

thf('24',plain,(
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
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) )
        = ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
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
    ! [X28: $i,X29: $i] :
      ( ~ ( l3_lattices @ X28 )
      | ( v2_struct_0 @ X28 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X28 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('36',plain,(
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

thf('37',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v6_lattices @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X25 ) )
      | ( ( k2_lattices @ X25 @ X27 @ X26 )
        = ( k2_lattices @ X25 @ X26 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( u1_struct_0 @ X25 ) )
      | ~ ( l1_lattices @ X25 )
      | ( v2_struct_0 @ X25 ) ) ),
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
        = ( k2_lattices @ X0 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l3_lattices @ X28 )
      | ( v2_struct_0 @ X28 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X28 @ X29 ) @ ( u1_struct_0 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('47',plain,(
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

thf('48',plain,(
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
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
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
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['45','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) )
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
    ! [X15: $i] :
      ( ( l1_lattices @ X15 )
      | ~ ( l3_lattices @ X15 ) ) ),
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
    ! [X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v6_lattices @ X10 )
      | ~ ( l3_lattices @ X10 ) ) ),
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
    ! [X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v8_lattices @ X10 )
      | ~ ( l3_lattices @ X10 ) ) ),
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
    ! [X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v9_lattices @ X10 )
      | ~ ( l3_lattices @ X10 ) ) ),
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

thf('82',plain,(
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

thf('83',plain,(
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

thf('84',plain,(
    ! [X11: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( l1_lattices @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( ( k2_lattices @ X11 @ X13 @ ( k5_lattices @ X11 ) )
        = ( k5_lattices @ X11 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X11 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v13_lattices @ X11 ) ) ),
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
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('90',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('91',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( u1_struct_0 @ X36 ) )
      | ( ( k15_lattice3 @ X36 @ ( k6_domain_1 @ ( u1_struct_0 @ X36 ) @ X35 ) )
        = X35 )
      | ~ ( l3_lattices @ X36 )
      | ~ ( v4_lattice3 @ X36 )
      | ~ ( v10_lattices @ X36 )
      | ( v2_struct_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t43_lattice3])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k5_lattices @ X0 ) ) )
        = ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k5_lattices @ X0 ) ) )
        = ( k5_lattices @ X0 ) )
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
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3UqUZJCPKJ
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.59/2.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.59/2.85  % Solved by: fo/fo7.sh
% 2.59/2.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.59/2.85  % done 1467 iterations in 2.394s
% 2.59/2.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.59/2.85  % SZS output start Refutation
% 2.59/2.85  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 2.59/2.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.59/2.85  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 2.59/2.85  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 2.59/2.85  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 2.59/2.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.59/2.85  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 2.59/2.85  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 2.59/2.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.59/2.85  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 2.59/2.85  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 2.59/2.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.59/2.85  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 2.59/2.85  thf(sk_A_type, type, sk_A: $i).
% 2.59/2.85  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 2.59/2.85  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 2.59/2.85  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 2.59/2.85  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 2.59/2.85  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 2.59/2.85  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 2.59/2.85  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 2.59/2.85  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 2.59/2.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.59/2.85  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 2.59/2.85  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 2.59/2.85  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 2.59/2.85  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 2.59/2.85  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.59/2.85  thf(dt_k15_lattice3, axiom,
% 2.59/2.85    (![A:$i,B:$i]:
% 2.59/2.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 2.59/2.85       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 2.59/2.85  thf('0', plain,
% 2.59/2.85      (![X28 : $i, X29 : $i]:
% 2.59/2.85         (~ (l3_lattices @ X28)
% 2.59/2.85          | (v2_struct_0 @ X28)
% 2.59/2.85          | (m1_subset_1 @ (k15_lattice3 @ X28 @ X29) @ (u1_struct_0 @ X28)))),
% 2.59/2.85      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.59/2.85  thf(d13_lattices, axiom,
% 2.59/2.85    (![A:$i]:
% 2.59/2.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 2.59/2.85       ( ( v13_lattices @ A ) <=>
% 2.59/2.85         ( ?[B:$i]:
% 2.59/2.85           ( ( ![C:$i]:
% 2.59/2.85               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.59/2.85                 ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 2.59/2.85                   ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) & 
% 2.59/2.85             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 2.59/2.85  thf('1', plain,
% 2.59/2.85      (![X22 : $i, X23 : $i]:
% 2.59/2.85         ((m1_subset_1 @ (sk_C_2 @ X22 @ X23) @ (u1_struct_0 @ X23))
% 2.59/2.85          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 2.59/2.85          | (v13_lattices @ X23)
% 2.59/2.85          | ~ (l1_lattices @ X23)
% 2.59/2.85          | (v2_struct_0 @ X23))),
% 2.59/2.85      inference('cnf', [status(esa)], [d13_lattices])).
% 2.59/2.85  thf('2', plain,
% 2.59/2.85      (![X0 : $i, X1 : $i]:
% 2.59/2.85         ((v2_struct_0 @ X0)
% 2.59/2.85          | ~ (l3_lattices @ X0)
% 2.59/2.85          | (v2_struct_0 @ X0)
% 2.59/2.85          | ~ (l1_lattices @ X0)
% 2.59/2.85          | (v13_lattices @ X0)
% 2.59/2.85          | (m1_subset_1 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.59/2.85             (u1_struct_0 @ X0)))),
% 2.59/2.85      inference('sup-', [status(thm)], ['0', '1'])).
% 2.59/2.85  thf('3', plain,
% 2.59/2.85      (![X0 : $i, X1 : $i]:
% 2.59/2.85         ((m1_subset_1 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.59/2.85           (u1_struct_0 @ X0))
% 2.59/2.85          | (v13_lattices @ X0)
% 2.59/2.85          | ~ (l1_lattices @ X0)
% 2.59/2.85          | ~ (l3_lattices @ X0)
% 2.59/2.85          | (v2_struct_0 @ X0))),
% 2.59/2.85      inference('simplify', [status(thm)], ['2'])).
% 2.59/2.85  thf(t43_lattice3, axiom,
% 2.59/2.85    (![A:$i]:
% 2.59/2.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.59/2.85         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.59/2.85       ( ![B:$i]:
% 2.59/2.85         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.59/2.85           ( ( ( k15_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 2.59/2.85               ( B ) ) & 
% 2.59/2.85             ( ( k16_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 2.59/2.85               ( B ) ) ) ) ) ))).
% 2.59/2.85  thf('4', plain,
% 2.59/2.85      (![X35 : $i, X36 : $i]:
% 2.59/2.85         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X36))
% 2.59/2.85          | ((k15_lattice3 @ X36 @ (k6_domain_1 @ (u1_struct_0 @ X36) @ X35))
% 2.59/2.85              = (X35))
% 2.59/2.85          | ~ (l3_lattices @ X36)
% 2.59/2.85          | ~ (v4_lattice3 @ X36)
% 2.59/2.85          | ~ (v10_lattices @ X36)
% 2.59/2.85          | (v2_struct_0 @ X36))),
% 2.59/2.85      inference('cnf', [status(esa)], [t43_lattice3])).
% 2.59/2.85  thf('5', plain,
% 2.59/2.85      (![X0 : $i, X1 : $i]:
% 2.59/2.85         ((v2_struct_0 @ X0)
% 2.59/2.85          | ~ (l3_lattices @ X0)
% 2.59/2.85          | ~ (l1_lattices @ X0)
% 2.59/2.85          | (v13_lattices @ X0)
% 2.59/2.85          | (v2_struct_0 @ X0)
% 2.59/2.85          | ~ (v10_lattices @ X0)
% 2.59/2.85          | ~ (v4_lattice3 @ X0)
% 2.59/2.85          | ~ (l3_lattices @ X0)
% 2.59/2.85          | ((k15_lattice3 @ X0 @ 
% 2.59/2.85              (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 2.59/2.85               (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 2.59/2.85              = (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0)))),
% 2.59/2.85      inference('sup-', [status(thm)], ['3', '4'])).
% 2.59/2.85  thf('6', plain,
% 2.59/2.85      (![X0 : $i, X1 : $i]:
% 2.59/2.85         (((k15_lattice3 @ X0 @ 
% 2.59/2.85            (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 2.59/2.85             (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 2.59/2.85            = (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.59/2.85          | ~ (v4_lattice3 @ X0)
% 2.59/2.85          | ~ (v10_lattices @ X0)
% 2.59/2.85          | (v13_lattices @ X0)
% 2.59/2.85          | ~ (l1_lattices @ X0)
% 2.59/2.85          | ~ (l3_lattices @ X0)
% 2.59/2.85          | (v2_struct_0 @ X0))),
% 2.59/2.85      inference('simplify', [status(thm)], ['5'])).
% 2.59/2.85  thf('7', plain,
% 2.59/2.85      (![X28 : $i, X29 : $i]:
% 2.59/2.85         (~ (l3_lattices @ X28)
% 2.59/2.85          | (v2_struct_0 @ X28)
% 2.59/2.85          | (m1_subset_1 @ (k15_lattice3 @ X28 @ X29) @ (u1_struct_0 @ X28)))),
% 2.59/2.85      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.59/2.85  thf(t48_lattice3, axiom,
% 2.59/2.85    (![A:$i]:
% 2.59/2.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.59/2.85         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.59/2.85       ( ![B:$i,C:$i]:
% 2.59/2.85         ( ( ![D:$i]:
% 2.59/2.85             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 2.59/2.85               ( ~( ( r2_hidden @ D @ B ) & 
% 2.59/2.85                    ( ![E:$i]:
% 2.59/2.85                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 2.59/2.85                        ( ~( ( r3_lattices @ A @ D @ E ) & 
% 2.59/2.85                             ( r2_hidden @ E @ C ) ) ) ) ) ) ) ) ) =>
% 2.59/2.85           ( r3_lattices @
% 2.59/2.85             A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) ) ) ))).
% 2.59/2.85  thf('8', plain,
% 2.59/2.85      (![X38 : $i, X39 : $i, X40 : $i]:
% 2.59/2.85         ((r2_hidden @ (sk_D_1 @ X39 @ X40 @ X38) @ X40)
% 2.59/2.85          | (r3_lattices @ X38 @ (k15_lattice3 @ X38 @ X40) @ 
% 2.59/2.85             (k15_lattice3 @ X38 @ X39))
% 2.59/2.85          | ~ (l3_lattices @ X38)
% 2.59/2.85          | ~ (v4_lattice3 @ X38)
% 2.59/2.85          | ~ (v10_lattices @ X38)
% 2.59/2.85          | (v2_struct_0 @ X38))),
% 2.59/2.85      inference('cnf', [status(esa)], [t48_lattice3])).
% 2.59/2.85  thf(t113_zfmisc_1, axiom,
% 2.59/2.85    (![A:$i,B:$i]:
% 2.59/2.85     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.59/2.85       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.59/2.85  thf('9', plain,
% 2.59/2.85      (![X6 : $i, X7 : $i]:
% 2.59/2.85         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 2.59/2.85      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.59/2.85  thf('10', plain,
% 2.59/2.85      (![X6 : $i]: ((k2_zfmisc_1 @ X6 @ k1_xboole_0) = (k1_xboole_0))),
% 2.59/2.85      inference('simplify', [status(thm)], ['9'])).
% 2.59/2.85  thf(t152_zfmisc_1, axiom,
% 2.59/2.85    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 2.59/2.85  thf('11', plain,
% 2.59/2.85      (![X8 : $i, X9 : $i]: ~ (r2_hidden @ X8 @ (k2_zfmisc_1 @ X8 @ X9))),
% 2.59/2.85      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 2.59/2.85  thf('12', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 2.59/2.85      inference('sup-', [status(thm)], ['10', '11'])).
% 2.59/2.85  thf('13', plain,
% 2.59/2.85      (![X0 : $i, X1 : $i]:
% 2.59/2.85         ((v2_struct_0 @ X0)
% 2.59/2.85          | ~ (v10_lattices @ X0)
% 2.59/2.85          | ~ (v4_lattice3 @ X0)
% 2.59/2.85          | ~ (l3_lattices @ X0)
% 2.59/2.85          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.59/2.85             (k15_lattice3 @ X0 @ X1)))),
% 2.59/2.85      inference('sup-', [status(thm)], ['8', '12'])).
% 2.59/2.85  thf('14', plain,
% 2.59/2.85      (![X28 : $i, X29 : $i]:
% 2.59/2.85         (~ (l3_lattices @ X28)
% 2.59/2.85          | (v2_struct_0 @ X28)
% 2.59/2.85          | (m1_subset_1 @ (k15_lattice3 @ X28 @ X29) @ (u1_struct_0 @ X28)))),
% 2.59/2.85      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.59/2.85  thf('15', plain,
% 2.59/2.85      (![X28 : $i, X29 : $i]:
% 2.59/2.85         (~ (l3_lattices @ X28)
% 2.59/2.85          | (v2_struct_0 @ X28)
% 2.59/2.85          | (m1_subset_1 @ (k15_lattice3 @ X28 @ X29) @ (u1_struct_0 @ X28)))),
% 2.59/2.85      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.59/2.85  thf(redefinition_r3_lattices, axiom,
% 2.59/2.85    (![A:$i,B:$i,C:$i]:
% 2.59/2.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 2.59/2.85         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 2.59/2.85         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 2.59/2.85         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 2.59/2.85       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 2.59/2.85  thf('16', plain,
% 2.59/2.85      (![X16 : $i, X17 : $i, X18 : $i]:
% 2.59/2.85         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 2.59/2.85          | ~ (l3_lattices @ X17)
% 2.59/2.85          | ~ (v9_lattices @ X17)
% 2.59/2.85          | ~ (v8_lattices @ X17)
% 2.59/2.85          | ~ (v6_lattices @ X17)
% 2.59/2.85          | (v2_struct_0 @ X17)
% 2.59/2.85          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 2.59/2.85          | (r1_lattices @ X17 @ X16 @ X18)
% 2.59/2.85          | ~ (r3_lattices @ X17 @ X16 @ X18))),
% 2.59/2.85      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 2.59/2.85  thf('17', plain,
% 2.59/2.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.59/2.85         ((v2_struct_0 @ X0)
% 2.59/2.85          | ~ (l3_lattices @ X0)
% 2.59/2.85          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.59/2.85          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.59/2.85          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.59/2.85          | (v2_struct_0 @ X0)
% 2.59/2.85          | ~ (v6_lattices @ X0)
% 2.59/2.85          | ~ (v8_lattices @ X0)
% 2.59/2.85          | ~ (v9_lattices @ X0)
% 2.59/2.85          | ~ (l3_lattices @ X0))),
% 2.59/2.85      inference('sup-', [status(thm)], ['15', '16'])).
% 2.59/2.85  thf('18', plain,
% 2.59/2.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.59/2.85         (~ (v9_lattices @ X0)
% 2.59/2.85          | ~ (v8_lattices @ X0)
% 2.59/2.85          | ~ (v6_lattices @ X0)
% 2.59/2.85          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.59/2.85          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.59/2.85          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.59/2.85          | ~ (l3_lattices @ X0)
% 2.59/2.85          | (v2_struct_0 @ X0))),
% 2.59/2.85      inference('simplify', [status(thm)], ['17'])).
% 2.59/2.85  thf('19', plain,
% 2.59/2.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.59/2.85         ((v2_struct_0 @ X0)
% 2.59/2.85          | ~ (l3_lattices @ X0)
% 2.59/2.85          | (v2_struct_0 @ X0)
% 2.59/2.85          | ~ (l3_lattices @ X0)
% 2.59/2.85          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.59/2.85               (k15_lattice3 @ X0 @ X1))
% 2.59/2.85          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.59/2.85             (k15_lattice3 @ X0 @ X1))
% 2.59/2.85          | ~ (v6_lattices @ X0)
% 2.59/2.85          | ~ (v8_lattices @ X0)
% 2.59/2.85          | ~ (v9_lattices @ X0))),
% 2.59/2.85      inference('sup-', [status(thm)], ['14', '18'])).
% 2.59/2.85  thf('20', plain,
% 2.59/2.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.59/2.85         (~ (v9_lattices @ X0)
% 2.59/2.85          | ~ (v8_lattices @ X0)
% 2.59/2.85          | ~ (v6_lattices @ X0)
% 2.59/2.85          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.59/2.85             (k15_lattice3 @ X0 @ X1))
% 2.59/2.85          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.59/2.85               (k15_lattice3 @ X0 @ X1))
% 2.59/2.85          | ~ (l3_lattices @ X0)
% 2.59/2.85          | (v2_struct_0 @ X0))),
% 2.59/2.85      inference('simplify', [status(thm)], ['19'])).
% 2.59/2.85  thf('21', plain,
% 2.59/2.85      (![X0 : $i, X1 : $i]:
% 2.59/2.85         (~ (l3_lattices @ X1)
% 2.59/2.85          | ~ (v4_lattice3 @ X1)
% 2.59/2.85          | ~ (v10_lattices @ X1)
% 2.59/2.85          | (v2_struct_0 @ X1)
% 2.59/2.85          | (v2_struct_0 @ X1)
% 2.59/2.85          | ~ (l3_lattices @ X1)
% 2.59/2.85          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 2.59/2.85             (k15_lattice3 @ X1 @ X0))
% 2.59/2.85          | ~ (v6_lattices @ X1)
% 2.59/2.85          | ~ (v8_lattices @ X1)
% 2.59/2.85          | ~ (v9_lattices @ X1))),
% 2.59/2.85      inference('sup-', [status(thm)], ['13', '20'])).
% 2.59/2.85  thf('22', plain,
% 2.59/2.85      (![X0 : $i, X1 : $i]:
% 2.59/2.85         (~ (v9_lattices @ X1)
% 2.59/2.85          | ~ (v8_lattices @ X1)
% 2.59/2.85          | ~ (v6_lattices @ X1)
% 2.59/2.85          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 2.59/2.85             (k15_lattice3 @ X1 @ X0))
% 2.59/2.85          | (v2_struct_0 @ X1)
% 2.59/2.85          | ~ (v10_lattices @ X1)
% 2.59/2.85          | ~ (v4_lattice3 @ X1)
% 2.59/2.85          | ~ (l3_lattices @ X1))),
% 2.59/2.85      inference('simplify', [status(thm)], ['21'])).
% 2.59/2.85  thf('23', plain,
% 2.59/2.85      (![X28 : $i, X29 : $i]:
% 2.59/2.85         (~ (l3_lattices @ X28)
% 2.59/2.85          | (v2_struct_0 @ X28)
% 2.59/2.85          | (m1_subset_1 @ (k15_lattice3 @ X28 @ X29) @ (u1_struct_0 @ X28)))),
% 2.59/2.85      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.59/2.85  thf(t21_lattices, axiom,
% 2.59/2.85    (![A:$i]:
% 2.59/2.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 2.59/2.85         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 2.59/2.85       ( ![B:$i]:
% 2.59/2.85         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.59/2.85           ( ![C:$i]:
% 2.59/2.85             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.59/2.85               ( ( r1_lattices @ A @ B @ C ) <=>
% 2.59/2.85                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 2.59/2.85  thf('24', plain,
% 2.59/2.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 2.59/2.85         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 2.59/2.85          | ~ (r1_lattices @ X20 @ X19 @ X21)
% 2.59/2.85          | ((k2_lattices @ X20 @ X19 @ X21) = (X19))
% 2.59/2.85          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 2.59/2.85          | ~ (l3_lattices @ X20)
% 2.59/2.85          | ~ (v9_lattices @ X20)
% 2.59/2.85          | ~ (v8_lattices @ X20)
% 2.59/2.85          | (v2_struct_0 @ X20))),
% 2.59/2.85      inference('cnf', [status(esa)], [t21_lattices])).
% 2.59/2.85  thf('25', plain,
% 2.59/2.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.59/2.85         ((v2_struct_0 @ X0)
% 2.59/2.85          | ~ (l3_lattices @ X0)
% 2.59/2.85          | (v2_struct_0 @ X0)
% 2.59/2.85          | ~ (v8_lattices @ X0)
% 2.59/2.85          | ~ (v9_lattices @ X0)
% 2.59/2.85          | ~ (l3_lattices @ X0)
% 2.59/2.85          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.59/2.85          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.59/2.85              = (k15_lattice3 @ X0 @ X1))
% 2.59/2.85          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 2.59/2.85      inference('sup-', [status(thm)], ['23', '24'])).
% 2.59/2.85  thf('26', plain,
% 2.59/2.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.59/2.85         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.59/2.85          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.59/2.85              = (k15_lattice3 @ X0 @ X1))
% 2.59/2.85          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.59/2.85          | ~ (v9_lattices @ X0)
% 2.59/2.85          | ~ (v8_lattices @ X0)
% 2.59/2.85          | ~ (l3_lattices @ X0)
% 2.59/2.85          | (v2_struct_0 @ X0))),
% 2.59/2.85      inference('simplify', [status(thm)], ['25'])).
% 2.59/2.85  thf('27', plain,
% 2.59/2.85      (![X0 : $i, X1 : $i]:
% 2.59/2.85         (~ (l3_lattices @ X1)
% 2.59/2.85          | ~ (v4_lattice3 @ X1)
% 2.59/2.85          | ~ (v10_lattices @ X1)
% 2.59/2.85          | (v2_struct_0 @ X1)
% 2.59/2.85          | ~ (v6_lattices @ X1)
% 2.59/2.85          | ~ (v8_lattices @ X1)
% 2.59/2.85          | ~ (v9_lattices @ X1)
% 2.59/2.85          | (v2_struct_0 @ X1)
% 2.59/2.85          | ~ (l3_lattices @ X1)
% 2.59/2.85          | ~ (v8_lattices @ X1)
% 2.59/2.85          | ~ (v9_lattices @ X1)
% 2.59/2.85          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 2.59/2.85          | ((k2_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 2.59/2.85              (k15_lattice3 @ X1 @ X0)) = (k15_lattice3 @ X1 @ k1_xboole_0)))),
% 2.59/2.85      inference('sup-', [status(thm)], ['22', '26'])).
% 2.59/2.85  thf('28', plain,
% 2.59/2.85      (![X0 : $i, X1 : $i]:
% 2.59/2.85         (((k2_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 2.59/2.85            (k15_lattice3 @ X1 @ X0)) = (k15_lattice3 @ X1 @ k1_xboole_0))
% 2.59/2.85          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 2.59/2.85          | ~ (v9_lattices @ X1)
% 2.59/2.85          | ~ (v8_lattices @ X1)
% 2.59/2.85          | ~ (v6_lattices @ X1)
% 2.59/2.85          | (v2_struct_0 @ X1)
% 2.59/2.85          | ~ (v10_lattices @ X1)
% 2.59/2.85          | ~ (v4_lattice3 @ X1)
% 2.59/2.85          | ~ (l3_lattices @ X1))),
% 2.59/2.85      inference('simplify', [status(thm)], ['27'])).
% 2.59/2.85  thf('29', plain,
% 2.59/2.85      (![X0 : $i, X1 : $i]:
% 2.59/2.85         ((v2_struct_0 @ X0)
% 2.59/2.85          | ~ (l3_lattices @ X0)
% 2.59/2.85          | ~ (l3_lattices @ X0)
% 2.59/2.85          | ~ (v4_lattice3 @ X0)
% 2.59/2.85          | ~ (v10_lattices @ X0)
% 2.59/2.85          | (v2_struct_0 @ X0)
% 2.59/2.85          | ~ (v6_lattices @ X0)
% 2.59/2.85          | ~ (v8_lattices @ X0)
% 2.59/2.85          | ~ (v9_lattices @ X0)
% 2.59/2.85          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.59/2.85              (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.59/2.85      inference('sup-', [status(thm)], ['7', '28'])).
% 2.59/2.85  thf('30', plain,
% 2.59/2.85      (![X0 : $i, X1 : $i]:
% 2.59/2.85         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.59/2.85            (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.59/2.85          | ~ (v9_lattices @ X0)
% 2.59/2.85          | ~ (v8_lattices @ X0)
% 2.59/2.85          | ~ (v6_lattices @ X0)
% 2.59/2.85          | ~ (v10_lattices @ X0)
% 2.59/2.85          | ~ (v4_lattice3 @ X0)
% 2.59/2.85          | ~ (l3_lattices @ X0)
% 2.59/2.85          | (v2_struct_0 @ X0))),
% 2.59/2.85      inference('simplify', [status(thm)], ['29'])).
% 2.59/2.85  thf('31', plain,
% 2.59/2.85      (![X0 : $i, X1 : $i]:
% 2.59/2.85         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.59/2.85            (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.59/2.85            = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.59/2.85          | (v2_struct_0 @ X0)
% 2.59/2.85          | ~ (l3_lattices @ X0)
% 2.59/2.85          | ~ (l1_lattices @ X0)
% 2.59/2.85          | (v13_lattices @ X0)
% 2.59/2.85          | ~ (v10_lattices @ X0)
% 2.59/2.85          | ~ (v4_lattice3 @ X0)
% 2.59/2.85          | (v2_struct_0 @ X0)
% 2.59/2.85          | ~ (l3_lattices @ X0)
% 2.59/2.85          | ~ (v4_lattice3 @ X0)
% 2.59/2.85          | ~ (v10_lattices @ X0)
% 2.59/2.85          | ~ (v6_lattices @ X0)
% 2.59/2.85          | ~ (v8_lattices @ X0)
% 2.59/2.85          | ~ (v9_lattices @ X0))),
% 2.59/2.85      inference('sup+', [status(thm)], ['6', '30'])).
% 2.59/2.85  thf('32', plain,
% 2.59/2.85      (![X0 : $i, X1 : $i]:
% 2.59/2.85         (~ (v9_lattices @ X0)
% 2.59/2.85          | ~ (v8_lattices @ X0)
% 2.59/2.85          | ~ (v6_lattices @ X0)
% 2.59/2.85          | ~ (v4_lattice3 @ X0)
% 2.59/2.85          | ~ (v10_lattices @ X0)
% 2.59/2.85          | (v13_lattices @ X0)
% 2.59/2.85          | ~ (l1_lattices @ X0)
% 2.59/2.85          | ~ (l3_lattices @ X0)
% 2.59/2.85          | (v2_struct_0 @ X0)
% 2.59/2.85          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.59/2.85              (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.59/2.85              = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.59/2.85      inference('simplify', [status(thm)], ['31'])).
% 2.59/2.85  thf('33', plain,
% 2.59/2.85      (![X0 : $i, X1 : $i]:
% 2.59/2.85         (((k15_lattice3 @ X0 @ 
% 2.59/2.85            (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 2.59/2.86             (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 2.59/2.86            = (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | (v13_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0))),
% 2.59/2.86      inference('simplify', [status(thm)], ['5'])).
% 2.59/2.86  thf('34', plain,
% 2.59/2.86      (![X0 : $i, X1 : $i]:
% 2.59/2.86         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.59/2.86            (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.59/2.86          | ~ (v9_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0))),
% 2.59/2.86      inference('simplify', [status(thm)], ['29'])).
% 2.59/2.86  thf('35', plain,
% 2.59/2.86      (![X28 : $i, X29 : $i]:
% 2.59/2.86         (~ (l3_lattices @ X28)
% 2.59/2.86          | (v2_struct_0 @ X28)
% 2.59/2.86          | (m1_subset_1 @ (k15_lattice3 @ X28 @ X29) @ (u1_struct_0 @ X28)))),
% 2.59/2.86      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.59/2.86  thf('36', plain,
% 2.59/2.86      (![X28 : $i, X29 : $i]:
% 2.59/2.86         (~ (l3_lattices @ X28)
% 2.59/2.86          | (v2_struct_0 @ X28)
% 2.59/2.86          | (m1_subset_1 @ (k15_lattice3 @ X28 @ X29) @ (u1_struct_0 @ X28)))),
% 2.59/2.86      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.59/2.86  thf(d6_lattices, axiom,
% 2.59/2.86    (![A:$i]:
% 2.59/2.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 2.59/2.86       ( ( v6_lattices @ A ) <=>
% 2.59/2.86         ( ![B:$i]:
% 2.59/2.86           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.59/2.86             ( ![C:$i]:
% 2.59/2.86               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.59/2.86                 ( ( k2_lattices @ A @ B @ C ) = ( k2_lattices @ A @ C @ B ) ) ) ) ) ) ) ))).
% 2.59/2.86  thf('37', plain,
% 2.59/2.86      (![X25 : $i, X26 : $i, X27 : $i]:
% 2.59/2.86         (~ (v6_lattices @ X25)
% 2.59/2.86          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X25))
% 2.59/2.86          | ((k2_lattices @ X25 @ X27 @ X26) = (k2_lattices @ X25 @ X26 @ X27))
% 2.59/2.86          | ~ (m1_subset_1 @ X27 @ (u1_struct_0 @ X25))
% 2.59/2.86          | ~ (l1_lattices @ X25)
% 2.59/2.86          | (v2_struct_0 @ X25))),
% 2.59/2.86      inference('cnf', [status(esa)], [d6_lattices])).
% 2.59/2.86  thf('38', plain,
% 2.59/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.59/2.86         ((v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.59/2.86          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 2.59/2.86              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 2.59/2.86          | ~ (v6_lattices @ X0))),
% 2.59/2.86      inference('sup-', [status(thm)], ['36', '37'])).
% 2.59/2.86  thf('39', plain,
% 2.59/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.59/2.86         (~ (v6_lattices @ X0)
% 2.59/2.86          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 2.59/2.86              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 2.59/2.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0))),
% 2.59/2.86      inference('simplify', [status(thm)], ['38'])).
% 2.59/2.86  thf('40', plain,
% 2.59/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.59/2.86         ((v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.59/2.86              (k15_lattice3 @ X0 @ X2))
% 2.59/2.86              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.59/2.86                 (k15_lattice3 @ X0 @ X1)))
% 2.59/2.86          | ~ (v6_lattices @ X0))),
% 2.59/2.86      inference('sup-', [status(thm)], ['35', '39'])).
% 2.59/2.86  thf('41', plain,
% 2.59/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.59/2.86         (~ (v6_lattices @ X0)
% 2.59/2.86          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.59/2.86              (k15_lattice3 @ X0 @ X2))
% 2.59/2.86              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 2.59/2.86                 (k15_lattice3 @ X0 @ X1)))
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0))),
% 2.59/2.86      inference('simplify', [status(thm)], ['40'])).
% 2.59/2.86  thf('42', plain,
% 2.59/2.86      (![X0 : $i, X1 : $i]:
% 2.59/2.86         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.59/2.86            = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.59/2.86               (k15_lattice3 @ X0 @ k1_xboole_0)))
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v9_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (v6_lattices @ X0))),
% 2.59/2.86      inference('sup+', [status(thm)], ['34', '41'])).
% 2.59/2.86  thf('43', plain,
% 2.59/2.86      (![X0 : $i, X1 : $i]:
% 2.59/2.86         (~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (v9_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.59/2.86              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.59/2.86                 (k15_lattice3 @ X0 @ k1_xboole_0))))),
% 2.59/2.86      inference('simplify', [status(thm)], ['42'])).
% 2.59/2.86  thf('44', plain,
% 2.59/2.86      (![X0 : $i, X1 : $i]:
% 2.59/2.86         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.59/2.86            = (k2_lattices @ X0 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.59/2.86               (k15_lattice3 @ X0 @ k1_xboole_0)))
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | (v13_lattices @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v9_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0))),
% 2.59/2.86      inference('sup+', [status(thm)], ['33', '43'])).
% 2.59/2.86  thf('45', plain,
% 2.59/2.86      (![X0 : $i, X1 : $i]:
% 2.59/2.86         (~ (v9_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | (v13_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.59/2.86              = (k2_lattices @ X0 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.59/2.86                 (k15_lattice3 @ X0 @ k1_xboole_0))))),
% 2.59/2.86      inference('simplify', [status(thm)], ['44'])).
% 2.59/2.86  thf('46', plain,
% 2.59/2.86      (![X28 : $i, X29 : $i]:
% 2.59/2.86         (~ (l3_lattices @ X28)
% 2.59/2.86          | (v2_struct_0 @ X28)
% 2.59/2.86          | (m1_subset_1 @ (k15_lattice3 @ X28 @ X29) @ (u1_struct_0 @ X28)))),
% 2.59/2.86      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.59/2.86  thf('47', plain,
% 2.59/2.86      (![X22 : $i, X23 : $i]:
% 2.59/2.86         (((k2_lattices @ X23 @ (sk_C_2 @ X22 @ X23) @ X22) != (X22))
% 2.59/2.86          | ((k2_lattices @ X23 @ X22 @ (sk_C_2 @ X22 @ X23)) != (X22))
% 2.59/2.86          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 2.59/2.86          | (v13_lattices @ X23)
% 2.59/2.86          | ~ (l1_lattices @ X23)
% 2.59/2.86          | (v2_struct_0 @ X23))),
% 2.59/2.86      inference('cnf', [status(esa)], [d13_lattices])).
% 2.59/2.86  thf('48', plain,
% 2.59/2.86      (![X0 : $i, X1 : $i]:
% 2.59/2.86         ((v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | (v13_lattices @ X0)
% 2.59/2.86          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.59/2.86              (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.59/2.86              != (k15_lattice3 @ X0 @ X1))
% 2.59/2.86          | ((k2_lattices @ X0 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.59/2.86              (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1)))),
% 2.59/2.86      inference('sup-', [status(thm)], ['46', '47'])).
% 2.59/2.86  thf('49', plain,
% 2.59/2.86      (![X0 : $i, X1 : $i]:
% 2.59/2.86         (((k2_lattices @ X0 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 2.59/2.86            (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1))
% 2.59/2.86          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 2.59/2.86              (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 2.59/2.86              != (k15_lattice3 @ X0 @ X1))
% 2.59/2.86          | (v13_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0))),
% 2.59/2.86      inference('simplify', [status(thm)], ['48'])).
% 2.59/2.86  thf('50', plain,
% 2.59/2.86      (![X0 : $i]:
% 2.59/2.86         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.59/2.86            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | (v13_lattices @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v9_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | (v13_lattices @ X0)
% 2.59/2.86          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.59/2.86              (sk_C_2 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 2.59/2.86              != (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.59/2.86      inference('sup-', [status(thm)], ['45', '49'])).
% 2.59/2.86  thf('51', plain,
% 2.59/2.86      (![X0 : $i]:
% 2.59/2.86         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.59/2.86            (sk_C_2 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0))
% 2.59/2.86            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.59/2.86          | ~ (v9_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | (v13_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0))),
% 2.59/2.86      inference('simplify', [status(thm)], ['50'])).
% 2.59/2.86  thf('52', plain,
% 2.59/2.86      (![X0 : $i]:
% 2.59/2.86         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 2.59/2.86            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | (v13_lattices @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v9_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | (v13_lattices @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v9_lattices @ X0))),
% 2.59/2.86      inference('sup-', [status(thm)], ['32', '51'])).
% 2.59/2.86  thf('53', plain,
% 2.59/2.86      (![X0 : $i]:
% 2.59/2.86         (~ (v9_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | (v13_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0))),
% 2.59/2.86      inference('simplify', [status(thm)], ['52'])).
% 2.59/2.86  thf(t50_lattice3, conjecture,
% 2.59/2.86    (![A:$i]:
% 2.59/2.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.59/2.86         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.59/2.86       ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.59/2.86         ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 2.59/2.86         ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ))).
% 2.59/2.86  thf(zf_stmt_0, negated_conjecture,
% 2.59/2.86    (~( ![A:$i]:
% 2.59/2.86        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.59/2.86            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 2.59/2.86          ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 2.59/2.86            ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 2.59/2.86            ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ) )),
% 2.59/2.86    inference('cnf.neg', [status(esa)], [t50_lattice3])).
% 2.59/2.86  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf('55', plain,
% 2.59/2.86      ((~ (l3_lattices @ sk_A)
% 2.59/2.86        | ~ (l1_lattices @ sk_A)
% 2.59/2.86        | (v13_lattices @ sk_A)
% 2.59/2.86        | ~ (v10_lattices @ sk_A)
% 2.59/2.86        | ~ (v4_lattice3 @ sk_A)
% 2.59/2.86        | ~ (v6_lattices @ sk_A)
% 2.59/2.86        | ~ (v8_lattices @ sk_A)
% 2.59/2.86        | ~ (v9_lattices @ sk_A))),
% 2.59/2.86      inference('sup-', [status(thm)], ['53', '54'])).
% 2.59/2.86  thf('56', plain, ((l3_lattices @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf('57', plain, ((l3_lattices @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf(dt_l3_lattices, axiom,
% 2.59/2.86    (![A:$i]:
% 2.59/2.86     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 2.59/2.86  thf('58', plain,
% 2.59/2.86      (![X15 : $i]: ((l1_lattices @ X15) | ~ (l3_lattices @ X15))),
% 2.59/2.86      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 2.59/2.86  thf('59', plain, ((l1_lattices @ sk_A)),
% 2.59/2.86      inference('sup-', [status(thm)], ['57', '58'])).
% 2.59/2.86  thf('60', plain, ((v10_lattices @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf('61', plain, ((v4_lattice3 @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf(cc1_lattices, axiom,
% 2.59/2.86    (![A:$i]:
% 2.59/2.86     ( ( l3_lattices @ A ) =>
% 2.59/2.86       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 2.59/2.86         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 2.59/2.86           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 2.59/2.86           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 2.59/2.86  thf('62', plain,
% 2.59/2.86      (![X10 : $i]:
% 2.59/2.86         ((v2_struct_0 @ X10)
% 2.59/2.86          | ~ (v10_lattices @ X10)
% 2.59/2.86          | (v6_lattices @ X10)
% 2.59/2.86          | ~ (l3_lattices @ X10))),
% 2.59/2.86      inference('cnf', [status(esa)], [cc1_lattices])).
% 2.59/2.86  thf('63', plain, (~ (v2_struct_0 @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf('64', plain,
% 2.59/2.86      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 2.59/2.86      inference('sup-', [status(thm)], ['62', '63'])).
% 2.59/2.86  thf('65', plain, ((l3_lattices @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf('66', plain, ((v10_lattices @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf('67', plain, ((v6_lattices @ sk_A)),
% 2.59/2.86      inference('demod', [status(thm)], ['64', '65', '66'])).
% 2.59/2.86  thf('68', plain,
% 2.59/2.86      (![X10 : $i]:
% 2.59/2.86         ((v2_struct_0 @ X10)
% 2.59/2.86          | ~ (v10_lattices @ X10)
% 2.59/2.86          | (v8_lattices @ X10)
% 2.59/2.86          | ~ (l3_lattices @ X10))),
% 2.59/2.86      inference('cnf', [status(esa)], [cc1_lattices])).
% 2.59/2.86  thf('69', plain, (~ (v2_struct_0 @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf('70', plain,
% 2.59/2.86      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 2.59/2.86      inference('sup-', [status(thm)], ['68', '69'])).
% 2.59/2.86  thf('71', plain, ((l3_lattices @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf('72', plain, ((v10_lattices @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf('73', plain, ((v8_lattices @ sk_A)),
% 2.59/2.86      inference('demod', [status(thm)], ['70', '71', '72'])).
% 2.59/2.86  thf('74', plain,
% 2.59/2.86      (![X10 : $i]:
% 2.59/2.86         ((v2_struct_0 @ X10)
% 2.59/2.86          | ~ (v10_lattices @ X10)
% 2.59/2.86          | (v9_lattices @ X10)
% 2.59/2.86          | ~ (l3_lattices @ X10))),
% 2.59/2.86      inference('cnf', [status(esa)], [cc1_lattices])).
% 2.59/2.86  thf('75', plain, (~ (v2_struct_0 @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf('76', plain,
% 2.59/2.86      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 2.59/2.86      inference('sup-', [status(thm)], ['74', '75'])).
% 2.59/2.86  thf('77', plain, ((l3_lattices @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf('78', plain, ((v10_lattices @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf('79', plain, ((v9_lattices @ sk_A)),
% 2.59/2.86      inference('demod', [status(thm)], ['76', '77', '78'])).
% 2.59/2.86  thf('80', plain, ((v13_lattices @ sk_A)),
% 2.59/2.86      inference('demod', [status(thm)],
% 2.59/2.86                ['55', '56', '59', '60', '61', '67', '73', '79'])).
% 2.59/2.86  thf('81', plain,
% 2.59/2.86      (![X28 : $i, X29 : $i]:
% 2.59/2.86         (~ (l3_lattices @ X28)
% 2.59/2.86          | (v2_struct_0 @ X28)
% 2.59/2.86          | (m1_subset_1 @ (k15_lattice3 @ X28 @ X29) @ (u1_struct_0 @ X28)))),
% 2.59/2.86      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 2.59/2.86  thf(dt_k5_lattices, axiom,
% 2.59/2.86    (![A:$i]:
% 2.59/2.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 2.59/2.86       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 2.59/2.86  thf('82', plain,
% 2.59/2.86      (![X14 : $i]:
% 2.59/2.86         ((m1_subset_1 @ (k5_lattices @ X14) @ (u1_struct_0 @ X14))
% 2.59/2.86          | ~ (l1_lattices @ X14)
% 2.59/2.86          | (v2_struct_0 @ X14))),
% 2.59/2.86      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 2.59/2.86  thf(d16_lattices, axiom,
% 2.59/2.86    (![A:$i]:
% 2.59/2.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 2.59/2.86       ( ( v13_lattices @ A ) =>
% 2.59/2.86         ( ![B:$i]:
% 2.59/2.86           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.59/2.86             ( ( ( B ) = ( k5_lattices @ A ) ) <=>
% 2.59/2.86               ( ![C:$i]:
% 2.59/2.86                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.59/2.86                   ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 2.59/2.86                     ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 2.59/2.86  thf('83', plain,
% 2.59/2.86      (![X11 : $i, X12 : $i, X13 : $i]:
% 2.59/2.86         (~ (v13_lattices @ X11)
% 2.59/2.86          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 2.59/2.86          | ((X12) != (k5_lattices @ X11))
% 2.59/2.86          | ((k2_lattices @ X11 @ X13 @ X12) = (X12))
% 2.59/2.86          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 2.59/2.86          | ~ (l1_lattices @ X11)
% 2.59/2.86          | (v2_struct_0 @ X11))),
% 2.59/2.86      inference('cnf', [status(esa)], [d16_lattices])).
% 2.59/2.86  thf('84', plain,
% 2.59/2.86      (![X11 : $i, X13 : $i]:
% 2.59/2.86         ((v2_struct_0 @ X11)
% 2.59/2.86          | ~ (l1_lattices @ X11)
% 2.59/2.86          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 2.59/2.86          | ((k2_lattices @ X11 @ X13 @ (k5_lattices @ X11))
% 2.59/2.86              = (k5_lattices @ X11))
% 2.59/2.86          | ~ (m1_subset_1 @ (k5_lattices @ X11) @ (u1_struct_0 @ X11))
% 2.59/2.86          | ~ (v13_lattices @ X11))),
% 2.59/2.86      inference('simplify', [status(thm)], ['83'])).
% 2.59/2.86  thf('85', plain,
% 2.59/2.86      (![X0 : $i, X1 : $i]:
% 2.59/2.86         ((v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (v13_lattices @ X0)
% 2.59/2.86          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 2.59/2.86          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0))),
% 2.59/2.86      inference('sup-', [status(thm)], ['82', '84'])).
% 2.59/2.86  thf('86', plain,
% 2.59/2.86      (![X0 : $i, X1 : $i]:
% 2.59/2.86         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 2.59/2.86          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 2.59/2.86          | ~ (v13_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0))),
% 2.59/2.86      inference('simplify', [status(thm)], ['85'])).
% 2.59/2.86  thf('87', plain,
% 2.59/2.86      (![X0 : $i, X1 : $i]:
% 2.59/2.86         ((v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (v13_lattices @ X0)
% 2.59/2.86          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.59/2.86              = (k5_lattices @ X0)))),
% 2.59/2.86      inference('sup-', [status(thm)], ['81', '86'])).
% 2.59/2.86  thf('88', plain,
% 2.59/2.86      (![X0 : $i, X1 : $i]:
% 2.59/2.86         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.59/2.86            = (k5_lattices @ X0))
% 2.59/2.86          | ~ (v13_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0))),
% 2.59/2.86      inference('simplify', [status(thm)], ['87'])).
% 2.59/2.86  thf('89', plain,
% 2.59/2.86      (![X14 : $i]:
% 2.59/2.86         ((m1_subset_1 @ (k5_lattices @ X14) @ (u1_struct_0 @ X14))
% 2.59/2.86          | ~ (l1_lattices @ X14)
% 2.59/2.86          | (v2_struct_0 @ X14))),
% 2.59/2.86      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 2.59/2.86  thf('90', plain,
% 2.59/2.86      (![X14 : $i]:
% 2.59/2.86         ((m1_subset_1 @ (k5_lattices @ X14) @ (u1_struct_0 @ X14))
% 2.59/2.86          | ~ (l1_lattices @ X14)
% 2.59/2.86          | (v2_struct_0 @ X14))),
% 2.59/2.86      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 2.59/2.86  thf('91', plain,
% 2.59/2.86      (![X35 : $i, X36 : $i]:
% 2.59/2.86         (~ (m1_subset_1 @ X35 @ (u1_struct_0 @ X36))
% 2.59/2.86          | ((k15_lattice3 @ X36 @ (k6_domain_1 @ (u1_struct_0 @ X36) @ X35))
% 2.59/2.86              = (X35))
% 2.59/2.86          | ~ (l3_lattices @ X36)
% 2.59/2.86          | ~ (v4_lattice3 @ X36)
% 2.59/2.86          | ~ (v10_lattices @ X36)
% 2.59/2.86          | (v2_struct_0 @ X36))),
% 2.59/2.86      inference('cnf', [status(esa)], [t43_lattice3])).
% 2.59/2.86  thf('92', plain,
% 2.59/2.86      (![X0 : $i]:
% 2.59/2.86         ((v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ((k15_lattice3 @ X0 @ 
% 2.59/2.86              (k6_domain_1 @ (u1_struct_0 @ X0) @ (k5_lattices @ X0)))
% 2.59/2.86              = (k5_lattices @ X0)))),
% 2.59/2.86      inference('sup-', [status(thm)], ['90', '91'])).
% 2.59/2.86  thf('93', plain,
% 2.59/2.86      (![X0 : $i]:
% 2.59/2.86         (((k15_lattice3 @ X0 @ 
% 2.59/2.86            (k6_domain_1 @ (u1_struct_0 @ X0) @ (k5_lattices @ X0)))
% 2.59/2.86            = (k5_lattices @ X0))
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0))),
% 2.59/2.86      inference('simplify', [status(thm)], ['92'])).
% 2.59/2.86  thf('94', plain,
% 2.59/2.86      (![X0 : $i, X1 : $i]:
% 2.59/2.86         ((v2_struct_0 @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.59/2.86             (k15_lattice3 @ X0 @ X1)))),
% 2.59/2.86      inference('sup-', [status(thm)], ['8', '12'])).
% 2.59/2.86  thf('95', plain,
% 2.59/2.86      (![X0 : $i]:
% 2.59/2.86         ((r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.59/2.86           (k5_lattices @ X0))
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0))),
% 2.59/2.86      inference('sup+', [status(thm)], ['93', '94'])).
% 2.59/2.86  thf('96', plain,
% 2.59/2.86      (![X0 : $i]:
% 2.59/2.86         (~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.59/2.86             (k5_lattices @ X0)))),
% 2.59/2.86      inference('simplify', [status(thm)], ['95'])).
% 2.59/2.86  thf('97', plain,
% 2.59/2.86      (![X14 : $i]:
% 2.59/2.86         ((m1_subset_1 @ (k5_lattices @ X14) @ (u1_struct_0 @ X14))
% 2.59/2.86          | ~ (l1_lattices @ X14)
% 2.59/2.86          | (v2_struct_0 @ X14))),
% 2.59/2.86      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 2.59/2.86  thf('98', plain,
% 2.59/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.59/2.86         (~ (v9_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.59/2.86          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.59/2.86          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0))),
% 2.59/2.86      inference('simplify', [status(thm)], ['17'])).
% 2.59/2.86  thf('99', plain,
% 2.59/2.86      (![X0 : $i, X1 : $i]:
% 2.59/2.86         ((v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.59/2.86          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v9_lattices @ X0))),
% 2.59/2.86      inference('sup-', [status(thm)], ['97', '98'])).
% 2.59/2.86  thf('100', plain,
% 2.59/2.86      (![X0 : $i, X1 : $i]:
% 2.59/2.86         (~ (v9_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.59/2.86          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0))),
% 2.59/2.86      inference('simplify', [status(thm)], ['99'])).
% 2.59/2.86  thf('101', plain,
% 2.59/2.86      (![X0 : $i]:
% 2.59/2.86         ((v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.59/2.86             (k5_lattices @ X0))
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v9_lattices @ X0))),
% 2.59/2.86      inference('sup-', [status(thm)], ['96', '100'])).
% 2.59/2.86  thf('102', plain,
% 2.59/2.86      (![X0 : $i]:
% 2.59/2.86         (~ (v9_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.59/2.86             (k5_lattices @ X0))
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0))),
% 2.59/2.86      inference('simplify', [status(thm)], ['101'])).
% 2.59/2.86  thf('103', plain,
% 2.59/2.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.59/2.86         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.59/2.86          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 2.59/2.86              = (k15_lattice3 @ X0 @ X1))
% 2.59/2.86          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.59/2.86          | ~ (v9_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0))),
% 2.59/2.86      inference('simplify', [status(thm)], ['25'])).
% 2.59/2.86  thf('104', plain,
% 2.59/2.86      (![X0 : $i]:
% 2.59/2.86         ((v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v9_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v9_lattices @ X0)
% 2.59/2.86          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 2.59/2.86          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.59/2.86              (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.59/2.86      inference('sup-', [status(thm)], ['102', '103'])).
% 2.59/2.86  thf('105', plain,
% 2.59/2.86      (![X0 : $i]:
% 2.59/2.86         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.59/2.86            (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.59/2.86          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 2.59/2.86          | ~ (v9_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0))),
% 2.59/2.86      inference('simplify', [status(thm)], ['104'])).
% 2.59/2.86  thf('106', plain,
% 2.59/2.86      (![X0 : $i]:
% 2.59/2.86         ((v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v9_lattices @ X0)
% 2.59/2.86          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.59/2.86              (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.59/2.86      inference('sup-', [status(thm)], ['89', '105'])).
% 2.59/2.86  thf('107', plain,
% 2.59/2.86      (![X0 : $i]:
% 2.59/2.86         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 2.59/2.86            (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.59/2.86          | ~ (v9_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0))),
% 2.59/2.86      inference('simplify', [status(thm)], ['106'])).
% 2.59/2.86  thf('108', plain,
% 2.59/2.86      (![X0 : $i]:
% 2.59/2.86         (((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (v13_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v9_lattices @ X0))),
% 2.59/2.86      inference('sup+', [status(thm)], ['88', '107'])).
% 2.59/2.86  thf('109', plain,
% 2.59/2.86      (![X0 : $i]:
% 2.59/2.86         (~ (v9_lattices @ X0)
% 2.59/2.86          | ~ (v8_lattices @ X0)
% 2.59/2.86          | ~ (v6_lattices @ X0)
% 2.59/2.86          | ~ (v4_lattice3 @ X0)
% 2.59/2.86          | ~ (v10_lattices @ X0)
% 2.59/2.86          | ~ (v13_lattices @ X0)
% 2.59/2.86          | ~ (l1_lattices @ X0)
% 2.59/2.86          | ~ (l3_lattices @ X0)
% 2.59/2.86          | (v2_struct_0 @ X0)
% 2.59/2.86          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 2.59/2.86      inference('simplify', [status(thm)], ['108'])).
% 2.59/2.86  thf('110', plain,
% 2.59/2.86      (((v2_struct_0 @ sk_A)
% 2.59/2.86        | ~ (v10_lattices @ sk_A)
% 2.59/2.86        | ~ (v13_lattices @ sk_A)
% 2.59/2.86        | ~ (l3_lattices @ sk_A)
% 2.59/2.86        | ((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf('111', plain,
% 2.59/2.86      ((((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))
% 2.59/2.86         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.59/2.86      inference('split', [status(esa)], ['110'])).
% 2.59/2.86  thf('112', plain,
% 2.59/2.86      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 2.59/2.86         | (v2_struct_0 @ sk_A)
% 2.59/2.86         | ~ (l3_lattices @ sk_A)
% 2.59/2.86         | ~ (l1_lattices @ sk_A)
% 2.59/2.86         | ~ (v13_lattices @ sk_A)
% 2.59/2.86         | ~ (v10_lattices @ sk_A)
% 2.59/2.86         | ~ (v4_lattice3 @ sk_A)
% 2.59/2.86         | ~ (v6_lattices @ sk_A)
% 2.59/2.86         | ~ (v8_lattices @ sk_A)
% 2.59/2.86         | ~ (v9_lattices @ sk_A)))
% 2.59/2.86         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.59/2.86      inference('sup-', [status(thm)], ['109', '111'])).
% 2.59/2.86  thf('113', plain, ((l3_lattices @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf('114', plain, ((l1_lattices @ sk_A)),
% 2.59/2.86      inference('sup-', [status(thm)], ['57', '58'])).
% 2.59/2.86  thf('115', plain, ((v10_lattices @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf('116', plain, ((v4_lattice3 @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf('117', plain, ((v6_lattices @ sk_A)),
% 2.59/2.86      inference('demod', [status(thm)], ['64', '65', '66'])).
% 2.59/2.86  thf('118', plain, ((v8_lattices @ sk_A)),
% 2.59/2.86      inference('demod', [status(thm)], ['70', '71', '72'])).
% 2.59/2.86  thf('119', plain, ((v9_lattices @ sk_A)),
% 2.59/2.86      inference('demod', [status(thm)], ['76', '77', '78'])).
% 2.59/2.86  thf('120', plain,
% 2.59/2.86      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 2.59/2.86         | (v2_struct_0 @ sk_A)
% 2.59/2.86         | ~ (v13_lattices @ sk_A)))
% 2.59/2.86         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.59/2.86      inference('demod', [status(thm)],
% 2.59/2.86                ['112', '113', '114', '115', '116', '117', '118', '119'])).
% 2.59/2.86  thf('121', plain,
% 2.59/2.86      (((~ (v13_lattices @ sk_A) | (v2_struct_0 @ sk_A)))
% 2.59/2.86         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.59/2.86      inference('simplify', [status(thm)], ['120'])).
% 2.59/2.86  thf('122', plain, (~ (v2_struct_0 @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf('123', plain,
% 2.59/2.86      ((~ (v13_lattices @ sk_A))
% 2.59/2.86         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.59/2.86      inference('clc', [status(thm)], ['121', '122'])).
% 2.59/2.86  thf('124', plain,
% 2.59/2.86      (($false)
% 2.59/2.86         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 2.59/2.86      inference('sup-', [status(thm)], ['80', '123'])).
% 2.59/2.86  thf('125', plain, (((v2_struct_0 @ sk_A)) <= (((v2_struct_0 @ sk_A)))),
% 2.59/2.86      inference('split', [status(esa)], ['110'])).
% 2.59/2.86  thf('126', plain, (~ (v2_struct_0 @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf('127', plain, (~ ((v2_struct_0 @ sk_A))),
% 2.59/2.86      inference('sup-', [status(thm)], ['125', '126'])).
% 2.59/2.86  thf('128', plain, ((l3_lattices @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf('129', plain, ((~ (l3_lattices @ sk_A)) <= (~ ((l3_lattices @ sk_A)))),
% 2.59/2.86      inference('split', [status(esa)], ['110'])).
% 2.59/2.86  thf('130', plain, (((l3_lattices @ sk_A))),
% 2.59/2.86      inference('sup-', [status(thm)], ['128', '129'])).
% 2.59/2.86  thf('131', plain, ((v10_lattices @ sk_A)),
% 2.59/2.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.59/2.86  thf('132', plain, ((~ (v10_lattices @ sk_A)) <= (~ ((v10_lattices @ sk_A)))),
% 2.59/2.86      inference('split', [status(esa)], ['110'])).
% 2.59/2.86  thf('133', plain, (((v10_lattices @ sk_A))),
% 2.59/2.86      inference('sup-', [status(thm)], ['131', '132'])).
% 2.59/2.86  thf('134', plain, ((v13_lattices @ sk_A)),
% 2.59/2.86      inference('demod', [status(thm)],
% 2.59/2.86                ['55', '56', '59', '60', '61', '67', '73', '79'])).
% 2.59/2.86  thf('135', plain, ((~ (v13_lattices @ sk_A)) <= (~ ((v13_lattices @ sk_A)))),
% 2.59/2.86      inference('split', [status(esa)], ['110'])).
% 2.59/2.86  thf('136', plain, (((v13_lattices @ sk_A))),
% 2.59/2.86      inference('sup-', [status(thm)], ['134', '135'])).
% 2.59/2.86  thf('137', plain,
% 2.59/2.86      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))) | 
% 2.59/2.86       ~ ((v13_lattices @ sk_A)) | ~ ((v10_lattices @ sk_A)) | 
% 2.59/2.86       ~ ((l3_lattices @ sk_A)) | ((v2_struct_0 @ sk_A))),
% 2.59/2.86      inference('split', [status(esa)], ['110'])).
% 2.59/2.86  thf('138', plain,
% 2.59/2.86      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 2.59/2.86      inference('sat_resolution*', [status(thm)],
% 2.59/2.86                ['127', '130', '133', '136', '137'])).
% 2.59/2.86  thf('139', plain, ($false),
% 2.59/2.86      inference('simpl_trail', [status(thm)], ['124', '138'])).
% 2.59/2.86  
% 2.59/2.86  % SZS output end Refutation
% 2.59/2.86  
% 2.59/2.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
