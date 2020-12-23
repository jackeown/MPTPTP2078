%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qA27eegaQx

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:37 EST 2020

% Result     : Theorem 10.38s
% Output     : Refutation 10.38s
% Verified   : 
% Statistics : Number of formulae       :  207 ( 564 expanded)
%              Number of leaves         :   49 ( 177 expanded)
%              Depth                    :   24
%              Number of atoms          : 3097 (9917 expanded)
%              Number of equality atoms :   98 ( 310 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(a_2_5_lattice3_type,type,(
    a_2_5_lattice3: $i > $i > $i )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(a_2_6_lattice3_type,type,(
    a_2_6_lattice3: $i > $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

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
    ! [X38: $i,X40: $i] :
      ( ( ( k15_lattice3 @ X38 @ X40 )
        = ( k15_lattice3 @ X38 @ ( a_2_5_lattice3 @ X38 @ X40 ) ) )
      | ~ ( l3_lattices @ X38 )
      | ~ ( v4_lattice3 @ X38 )
      | ~ ( v10_lattices @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t47_lattice3])).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l3_lattices @ X26 )
      | ( v2_struct_0 @ X26 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X26 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) ),
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
    ! [X20: $i,X21: $i] :
      ( ( m1_subset_1 @ ( sk_C_2 @ X20 @ X21 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( v13_lattices @ X21 )
      | ~ ( l1_lattices @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
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
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X34 ) )
      | ( ( k15_lattice3 @ X34 @ ( k6_domain_1 @ ( u1_struct_0 @ X34 ) @ X33 ) )
        = X33 )
      | ~ ( l3_lattices @ X34 )
      | ~ ( v4_lattice3 @ X34 )
      | ~ ( v10_lattices @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ~ ( l3_lattices @ X26 )
      | ( v2_struct_0 @ X26 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X26 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('9',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l3_lattices @ X26 )
      | ( v2_struct_0 @ X26 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X26 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) ),
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

thf('10',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v6_lattices @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ( ( k2_lattices @ X23 @ X25 @ X24 )
        = ( k2_lattices @ X23 @ X24 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l1_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d6_lattices])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ X2 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) ) )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ X2 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) ) )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l3_lattices @ X26 )
      | ( v2_struct_0 @ X26 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X26 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('16',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
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

thf('17',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ X35 @ X36 )
      | ( r3_lattices @ X37 @ ( k15_lattice3 @ X37 @ X35 ) @ ( k15_lattice3 @ X37 @ X36 ) )
      | ~ ( l3_lattices @ X37 )
      | ~ ( v4_lattice3 @ X37 )
      | ~ ( v10_lattices @ X37 )
      | ( v2_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t46_lattice3])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l3_lattices @ X26 )
      | ( v2_struct_0 @ X26 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X26 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('20',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l3_lattices @ X26 )
      | ( v2_struct_0 @ X26 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X26 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) ),
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

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X15 ) )
      | ~ ( l3_lattices @ X15 )
      | ~ ( v9_lattices @ X15 )
      | ~ ( v8_lattices @ X15 )
      | ~ ( v6_lattices @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X15 ) )
      | ( r1_lattices @ X15 @ X14 @ X16 )
      | ~ ( r3_lattices @ X15 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('22',plain,(
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
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
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
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
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
    inference('sup-',[status(thm)],['18','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X1 )
      | ~ ( v8_lattices @ X1 )
      | ~ ( v6_lattices @ X1 )
      | ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l3_lattices @ X26 )
      | ( v2_struct_0 @ X26 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X26 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) ),
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

thf('29',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ~ ( r1_lattices @ X18 @ X17 @ X19 )
      | ( ( k2_lattices @ X18 @ X17 @ X19 )
        = X17 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X18 ) )
      | ~ ( l3_lattices @ X18 )
      | ~ ( v9_lattices @ X18 )
      | ~ ( v8_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('30',plain,(
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
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
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
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
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
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
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
    inference('sup-',[status(thm)],['15','33'])).

thf('35',plain,(
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
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
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
      | ( ( k2_lattices @ X0 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
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
    inference(simplify,[status(thm)],['34'])).

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
    ! [X38: $i,X40: $i] :
      ( ( ( k15_lattice3 @ X38 @ X40 )
        = ( k15_lattice3 @ X38 @ ( a_2_5_lattice3 @ X38 @ X40 ) ) )
      | ~ ( l3_lattices @ X38 )
      | ~ ( v4_lattice3 @ X38 )
      | ~ ( v10_lattices @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t47_lattice3])).

thf('45',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( l3_lattices @ X28 )
      | ~ ( v4_lattice3 @ X28 )
      | ~ ( v10_lattices @ X28 )
      | ( v2_struct_0 @ X28 )
      | ( r2_hidden @ ( sk_E @ X29 @ X28 @ X30 ) @ X29 )
      | ~ ( r2_hidden @ X30 @ ( a_2_5_lattice3 @ X28 @ X29 ) ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
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

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('52',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( a_2_5_lattice3 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X38: $i,X40: $i] :
      ( ( ( k15_lattice3 @ X38 @ X40 )
        = ( k15_lattice3 @ X38 @ ( a_2_5_lattice3 @ X38 @ X40 ) ) )
      | ~ ( l3_lattices @ X38 )
      | ~ ( v4_lattice3 @ X38 )
      | ~ ( v10_lattices @ X38 )
      | ( v2_struct_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t47_lattice3])).

thf('55',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l3_lattices @ X26 )
      | ( v2_struct_0 @ X26 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X26 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('56',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_lattices @ X21 @ ( sk_C_2 @ X20 @ X21 ) @ X20 )
       != X20 )
      | ( ( k2_lattices @ X21 @ X20 @ ( sk_C_2 @ X20 @ X21 ) )
       != X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X21 ) )
      | ( v13_lattices @ X21 )
      | ~ ( l1_lattices @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d13_lattices])).

thf('57',plain,(
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
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
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
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,(
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
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
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
    inference('sup-',[status(thm)],['53','60'])).

thf('62',plain,(
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
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
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
    inference('sup-',[status(thm)],['44','62'])).

thf('64',plain,(
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
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
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
    inference('sup-',[status(thm)],['43','64'])).

thf('66',plain,(
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
    inference('sup-',[status(thm)],['39','66'])).

thf('68',plain,(
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
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
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
    inference('sup-',[status(thm)],['0','68'])).

thf('70',plain,(
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
    inference(simplify,[status(thm)],['69'])).

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

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( v13_lattices @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('77',plain,(
    ! [X13: $i] :
      ( ( l1_lattices @ X13 )
      | ~ ( l3_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('78',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

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

thf('79',plain,(
    ! [X8: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ( v6_lattices @ X8 )
      | ~ ( l3_lattices @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X8: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ( v8_lattices @ X8 )
      | ~ ( l3_lattices @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X8: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ( v9_lattices @ X8 )
      | ~ ( l3_lattices @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['72','73','74','75','78','84','90','96'])).

thf('98',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( l3_lattices @ X26 )
      | ( v2_struct_0 @ X26 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X26 @ X27 ) @ ( u1_struct_0 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(dt_k5_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('99',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X12 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_lattices @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
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

thf('100',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v13_lattices @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( X10
       != ( k5_lattices @ X9 ) )
      | ( ( k2_lattices @ X9 @ X11 @ X10 )
        = X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d16_lattices])).

thf('101',plain,(
    ! [X9: $i,X11: $i] :
      ( ( v2_struct_0 @ X9 )
      | ~ ( l1_lattices @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ( ( k2_lattices @ X9 @ X11 @ ( k5_lattices @ X9 ) )
        = ( k5_lattices @ X9 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X9 ) @ ( u1_struct_0 @ X9 ) )
      | ~ ( v13_lattices @ X9 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','101'])).

thf('103',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['98','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X12 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_lattices @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('107',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X12 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_lattices @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('108',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X34 ) )
      | ( ( k15_lattice3 @ X34 @ ( k6_domain_1 @ ( u1_struct_0 @ X34 ) @ X33 ) )
        = X33 )
      | ~ ( l3_lattices @ X34 )
      | ~ ( v4_lattice3 @ X34 )
      | ~ ( v10_lattices @ X34 )
      | ( v2_struct_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t43_lattice3])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k5_lattices @ X0 ) ) )
        = ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k5_lattices @ X0 ) ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('112',plain,(
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
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X12 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_lattices @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('115',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('116',plain,(
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
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
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
    inference('sup-',[status(thm)],['113','117'])).

thf('119',plain,(
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
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('121',plain,(
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
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
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
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
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
    inference('sup-',[status(thm)],['106','122'])).

thf('124',plain,(
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
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
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
    inference('sup+',[status(thm)],['105','124'])).

thf('126',plain,(
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
    inference(simplify,[status(thm)],['125'])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['127'])).

thf('129',plain,
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
    inference('sup-',[status(thm)],['126','128'])).

thf('130',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('132',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('135',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('136',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('137',plain,
    ( ( ( ( k5_lattices @ sk_A )
       != ( k5_lattices @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v13_lattices @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['129','130','131','132','133','134','135','136'])).

thf('138',plain,
    ( ( ~ ( v13_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['138','139'])).

thf('141',plain,
    ( $false
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','140'])).

thf('142',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['127'])).

thf('143',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['142','143'])).

thf('145',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,
    ( ~ ( l3_lattices @ sk_A )
   <= ~ ( l3_lattices @ sk_A ) ),
    inference(split,[status(esa)],['127'])).

thf('147',plain,(
    l3_lattices @ sk_A ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ~ ( v10_lattices @ sk_A )
   <= ~ ( v10_lattices @ sk_A ) ),
    inference(split,[status(esa)],['127'])).

thf('150',plain,(
    v10_lattices @ sk_A ),
    inference('sup-',[status(thm)],['148','149'])).

thf('151',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['72','73','74','75','78','84','90','96'])).

thf('152',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ~ ( v13_lattices @ sk_A ) ),
    inference(split,[status(esa)],['127'])).

thf('153',plain,(
    v13_lattices @ sk_A ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['127'])).

thf('155',plain,(
    ( k5_lattices @ sk_A )
 != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ),
    inference('sat_resolution*',[status(thm)],['144','147','150','153','154'])).

thf('156',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['141','155'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qA27eegaQx
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:15:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 10.38/10.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.38/10.56  % Solved by: fo/fo7.sh
% 10.38/10.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.38/10.56  % done 5189 iterations in 10.093s
% 10.38/10.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.38/10.56  % SZS output start Refutation
% 10.38/10.56  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 10.38/10.56  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 10.38/10.56  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 10.38/10.56  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 10.38/10.56  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 10.38/10.56  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 10.38/10.56  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 10.38/10.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.38/10.56  thf(a_2_5_lattice3_type, type, a_2_5_lattice3: $i > $i > $i).
% 10.38/10.56  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 10.38/10.56  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 10.38/10.56  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 10.38/10.56  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 10.38/10.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.38/10.56  thf(sk_A_type, type, sk_A: $i).
% 10.38/10.56  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 10.38/10.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.38/10.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 10.38/10.56  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 10.38/10.56  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 10.38/10.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.38/10.56  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 10.38/10.56  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 10.38/10.56  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 10.38/10.56  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 10.38/10.56  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 10.38/10.56  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 10.38/10.56  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 10.38/10.56  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 10.38/10.56  thf(a_2_6_lattice3_type, type, a_2_6_lattice3: $i > $i > $i).
% 10.38/10.56  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 10.38/10.56  thf(t47_lattice3, axiom,
% 10.38/10.56    (![A:$i]:
% 10.38/10.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 10.38/10.56         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 10.38/10.56       ( ![B:$i]:
% 10.38/10.56         ( ( ( k16_lattice3 @ A @ B ) =
% 10.38/10.56             ( k16_lattice3 @ A @ ( a_2_6_lattice3 @ A @ B ) ) ) & 
% 10.38/10.56           ( ( k15_lattice3 @ A @ B ) =
% 10.38/10.56             ( k15_lattice3 @ A @ ( a_2_5_lattice3 @ A @ B ) ) ) ) ) ))).
% 10.38/10.56  thf('0', plain,
% 10.38/10.56      (![X38 : $i, X40 : $i]:
% 10.38/10.56         (((k15_lattice3 @ X38 @ X40)
% 10.38/10.56            = (k15_lattice3 @ X38 @ (a_2_5_lattice3 @ X38 @ X40)))
% 10.38/10.56          | ~ (l3_lattices @ X38)
% 10.38/10.56          | ~ (v4_lattice3 @ X38)
% 10.38/10.56          | ~ (v10_lattices @ X38)
% 10.38/10.56          | (v2_struct_0 @ X38))),
% 10.38/10.56      inference('cnf', [status(esa)], [t47_lattice3])).
% 10.38/10.56  thf(dt_k15_lattice3, axiom,
% 10.38/10.56    (![A:$i,B:$i]:
% 10.38/10.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 10.38/10.56       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 10.38/10.56  thf('1', plain,
% 10.38/10.56      (![X26 : $i, X27 : $i]:
% 10.38/10.56         (~ (l3_lattices @ X26)
% 10.38/10.56          | (v2_struct_0 @ X26)
% 10.38/10.56          | (m1_subset_1 @ (k15_lattice3 @ X26 @ X27) @ (u1_struct_0 @ X26)))),
% 10.38/10.56      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 10.38/10.56  thf(d13_lattices, axiom,
% 10.38/10.56    (![A:$i]:
% 10.38/10.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 10.38/10.56       ( ( v13_lattices @ A ) <=>
% 10.38/10.56         ( ?[B:$i]:
% 10.38/10.56           ( ( ![C:$i]:
% 10.38/10.56               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 10.38/10.56                 ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 10.38/10.56                   ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) & 
% 10.38/10.56             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 10.38/10.56  thf('2', plain,
% 10.38/10.56      (![X20 : $i, X21 : $i]:
% 10.38/10.56         ((m1_subset_1 @ (sk_C_2 @ X20 @ X21) @ (u1_struct_0 @ X21))
% 10.38/10.56          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 10.38/10.56          | (v13_lattices @ X21)
% 10.38/10.56          | ~ (l1_lattices @ X21)
% 10.38/10.56          | (v2_struct_0 @ X21))),
% 10.38/10.56      inference('cnf', [status(esa)], [d13_lattices])).
% 10.38/10.56  thf('3', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v13_lattices @ X0)
% 10.38/10.56          | (m1_subset_1 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 10.38/10.56             (u1_struct_0 @ X0)))),
% 10.38/10.56      inference('sup-', [status(thm)], ['1', '2'])).
% 10.38/10.56  thf('4', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         ((m1_subset_1 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 10.38/10.56           (u1_struct_0 @ X0))
% 10.38/10.56          | (v13_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['3'])).
% 10.38/10.56  thf(t43_lattice3, axiom,
% 10.38/10.56    (![A:$i]:
% 10.38/10.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 10.38/10.56         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 10.38/10.56       ( ![B:$i]:
% 10.38/10.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 10.38/10.56           ( ( ( k15_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 10.38/10.56               ( B ) ) & 
% 10.38/10.56             ( ( k16_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 10.38/10.56               ( B ) ) ) ) ) ))).
% 10.38/10.56  thf('5', plain,
% 10.38/10.56      (![X33 : $i, X34 : $i]:
% 10.38/10.56         (~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X34))
% 10.38/10.56          | ((k15_lattice3 @ X34 @ (k6_domain_1 @ (u1_struct_0 @ X34) @ X33))
% 10.38/10.56              = (X33))
% 10.38/10.56          | ~ (l3_lattices @ X34)
% 10.38/10.56          | ~ (v4_lattice3 @ X34)
% 10.38/10.56          | ~ (v10_lattices @ X34)
% 10.38/10.56          | (v2_struct_0 @ X34))),
% 10.38/10.56      inference('cnf', [status(esa)], [t43_lattice3])).
% 10.38/10.56  thf('6', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v13_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ((k15_lattice3 @ X0 @ 
% 10.38/10.56              (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 10.38/10.56               (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 10.38/10.56              = (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0)))),
% 10.38/10.56      inference('sup-', [status(thm)], ['4', '5'])).
% 10.38/10.56  thf('7', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         (((k15_lattice3 @ X0 @ 
% 10.38/10.56            (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 10.38/10.56             (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 10.38/10.56            = (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | (v13_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['6'])).
% 10.38/10.56  thf('8', plain,
% 10.38/10.56      (![X26 : $i, X27 : $i]:
% 10.38/10.56         (~ (l3_lattices @ X26)
% 10.38/10.56          | (v2_struct_0 @ X26)
% 10.38/10.56          | (m1_subset_1 @ (k15_lattice3 @ X26 @ X27) @ (u1_struct_0 @ X26)))),
% 10.38/10.56      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 10.38/10.56  thf('9', plain,
% 10.38/10.56      (![X26 : $i, X27 : $i]:
% 10.38/10.56         (~ (l3_lattices @ X26)
% 10.38/10.56          | (v2_struct_0 @ X26)
% 10.38/10.56          | (m1_subset_1 @ (k15_lattice3 @ X26 @ X27) @ (u1_struct_0 @ X26)))),
% 10.38/10.56      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 10.38/10.56  thf(d6_lattices, axiom,
% 10.38/10.56    (![A:$i]:
% 10.38/10.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 10.38/10.56       ( ( v6_lattices @ A ) <=>
% 10.38/10.56         ( ![B:$i]:
% 10.38/10.56           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 10.38/10.56             ( ![C:$i]:
% 10.38/10.56               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 10.38/10.56                 ( ( k2_lattices @ A @ B @ C ) = ( k2_lattices @ A @ C @ B ) ) ) ) ) ) ) ))).
% 10.38/10.56  thf('10', plain,
% 10.38/10.56      (![X23 : $i, X24 : $i, X25 : $i]:
% 10.38/10.56         (~ (v6_lattices @ X23)
% 10.38/10.56          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 10.38/10.56          | ((k2_lattices @ X23 @ X25 @ X24) = (k2_lattices @ X23 @ X24 @ X25))
% 10.38/10.56          | ~ (m1_subset_1 @ X25 @ (u1_struct_0 @ X23))
% 10.38/10.56          | ~ (l1_lattices @ X23)
% 10.38/10.56          | (v2_struct_0 @ X23))),
% 10.38/10.56      inference('cnf', [status(esa)], [d6_lattices])).
% 10.38/10.56  thf('11', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.38/10.56          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 10.38/10.56              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 10.38/10.56          | ~ (v6_lattices @ X0))),
% 10.38/10.56      inference('sup-', [status(thm)], ['9', '10'])).
% 10.38/10.56  thf('12', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.38/10.56         (~ (v6_lattices @ X0)
% 10.38/10.56          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 10.38/10.56              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 10.38/10.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['11'])).
% 10.38/10.56  thf('13', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 10.38/10.56              (k15_lattice3 @ X0 @ X2))
% 10.38/10.56              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 10.38/10.56                 (k15_lattice3 @ X0 @ X1)))
% 10.38/10.56          | ~ (v6_lattices @ X0))),
% 10.38/10.56      inference('sup-', [status(thm)], ['8', '12'])).
% 10.38/10.56  thf('14', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.38/10.56         (~ (v6_lattices @ X0)
% 10.38/10.56          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 10.38/10.56              (k15_lattice3 @ X0 @ X2))
% 10.38/10.56              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 10.38/10.56                 (k15_lattice3 @ X0 @ X1)))
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['13'])).
% 10.38/10.56  thf('15', plain,
% 10.38/10.56      (![X26 : $i, X27 : $i]:
% 10.38/10.56         (~ (l3_lattices @ X26)
% 10.38/10.56          | (v2_struct_0 @ X26)
% 10.38/10.56          | (m1_subset_1 @ (k15_lattice3 @ X26 @ X27) @ (u1_struct_0 @ X26)))),
% 10.38/10.56      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 10.38/10.56  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 10.38/10.56  thf('16', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 10.38/10.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 10.38/10.56  thf(t46_lattice3, axiom,
% 10.38/10.56    (![A:$i]:
% 10.38/10.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 10.38/10.56         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 10.38/10.56       ( ![B:$i,C:$i]:
% 10.38/10.56         ( ( r1_tarski @ B @ C ) =>
% 10.38/10.56           ( ( r3_lattices @
% 10.38/10.56               A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) & 
% 10.38/10.56             ( r3_lattices @
% 10.38/10.56               A @ ( k16_lattice3 @ A @ C ) @ ( k16_lattice3 @ A @ B ) ) ) ) ) ))).
% 10.38/10.56  thf('17', plain,
% 10.38/10.56      (![X35 : $i, X36 : $i, X37 : $i]:
% 10.38/10.56         (~ (r1_tarski @ X35 @ X36)
% 10.38/10.56          | (r3_lattices @ X37 @ (k15_lattice3 @ X37 @ X35) @ 
% 10.38/10.56             (k15_lattice3 @ X37 @ X36))
% 10.38/10.56          | ~ (l3_lattices @ X37)
% 10.38/10.56          | ~ (v4_lattice3 @ X37)
% 10.38/10.56          | ~ (v10_lattices @ X37)
% 10.38/10.56          | (v2_struct_0 @ X37))),
% 10.38/10.56      inference('cnf', [status(esa)], [t46_lattice3])).
% 10.38/10.56  thf('18', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X1)
% 10.38/10.56          | ~ (v10_lattices @ X1)
% 10.38/10.56          | ~ (v4_lattice3 @ X1)
% 10.38/10.56          | ~ (l3_lattices @ X1)
% 10.38/10.56          | (r3_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 10.38/10.56             (k15_lattice3 @ X1 @ X0)))),
% 10.38/10.56      inference('sup-', [status(thm)], ['16', '17'])).
% 10.38/10.56  thf('19', plain,
% 10.38/10.56      (![X26 : $i, X27 : $i]:
% 10.38/10.56         (~ (l3_lattices @ X26)
% 10.38/10.56          | (v2_struct_0 @ X26)
% 10.38/10.56          | (m1_subset_1 @ (k15_lattice3 @ X26 @ X27) @ (u1_struct_0 @ X26)))),
% 10.38/10.56      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 10.38/10.56  thf('20', plain,
% 10.38/10.56      (![X26 : $i, X27 : $i]:
% 10.38/10.56         (~ (l3_lattices @ X26)
% 10.38/10.56          | (v2_struct_0 @ X26)
% 10.38/10.56          | (m1_subset_1 @ (k15_lattice3 @ X26 @ X27) @ (u1_struct_0 @ X26)))),
% 10.38/10.56      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 10.38/10.56  thf(redefinition_r3_lattices, axiom,
% 10.38/10.56    (![A:$i,B:$i,C:$i]:
% 10.38/10.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 10.38/10.56         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 10.38/10.56         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 10.38/10.56         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 10.38/10.56       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 10.38/10.56  thf('21', plain,
% 10.38/10.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 10.38/10.56         (~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X15))
% 10.38/10.56          | ~ (l3_lattices @ X15)
% 10.38/10.56          | ~ (v9_lattices @ X15)
% 10.38/10.56          | ~ (v8_lattices @ X15)
% 10.38/10.56          | ~ (v6_lattices @ X15)
% 10.38/10.56          | (v2_struct_0 @ X15)
% 10.38/10.56          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X15))
% 10.38/10.56          | (r1_lattices @ X15 @ X14 @ X16)
% 10.38/10.56          | ~ (r3_lattices @ X15 @ X14 @ X16))),
% 10.38/10.56      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 10.38/10.56  thf('22', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 10.38/10.56          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 10.38/10.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0))),
% 10.38/10.56      inference('sup-', [status(thm)], ['20', '21'])).
% 10.38/10.56  thf('23', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.38/10.56         (~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.38/10.56          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 10.38/10.56          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['22'])).
% 10.38/10.56  thf('24', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 10.38/10.56               (k15_lattice3 @ X0 @ X1))
% 10.38/10.56          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 10.38/10.56             (k15_lattice3 @ X0 @ X1))
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v9_lattices @ X0))),
% 10.38/10.56      inference('sup-', [status(thm)], ['19', '23'])).
% 10.38/10.56  thf('25', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.38/10.56         (~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 10.38/10.56             (k15_lattice3 @ X0 @ X1))
% 10.38/10.56          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 10.38/10.56               (k15_lattice3 @ X0 @ X1))
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['24'])).
% 10.38/10.56  thf('26', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         (~ (l3_lattices @ X1)
% 10.38/10.56          | ~ (v4_lattice3 @ X1)
% 10.38/10.56          | ~ (v10_lattices @ X1)
% 10.38/10.56          | (v2_struct_0 @ X1)
% 10.38/10.56          | (v2_struct_0 @ X1)
% 10.38/10.56          | ~ (l3_lattices @ X1)
% 10.38/10.56          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 10.38/10.56             (k15_lattice3 @ X1 @ X0))
% 10.38/10.56          | ~ (v6_lattices @ X1)
% 10.38/10.56          | ~ (v8_lattices @ X1)
% 10.38/10.56          | ~ (v9_lattices @ X1))),
% 10.38/10.56      inference('sup-', [status(thm)], ['18', '25'])).
% 10.38/10.56  thf('27', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         (~ (v9_lattices @ X1)
% 10.38/10.56          | ~ (v8_lattices @ X1)
% 10.38/10.56          | ~ (v6_lattices @ X1)
% 10.38/10.56          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 10.38/10.56             (k15_lattice3 @ X1 @ X0))
% 10.38/10.56          | (v2_struct_0 @ X1)
% 10.38/10.56          | ~ (v10_lattices @ X1)
% 10.38/10.56          | ~ (v4_lattice3 @ X1)
% 10.38/10.56          | ~ (l3_lattices @ X1))),
% 10.38/10.56      inference('simplify', [status(thm)], ['26'])).
% 10.38/10.56  thf('28', plain,
% 10.38/10.56      (![X26 : $i, X27 : $i]:
% 10.38/10.56         (~ (l3_lattices @ X26)
% 10.38/10.56          | (v2_struct_0 @ X26)
% 10.38/10.56          | (m1_subset_1 @ (k15_lattice3 @ X26 @ X27) @ (u1_struct_0 @ X26)))),
% 10.38/10.56      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 10.38/10.56  thf(t21_lattices, axiom,
% 10.38/10.56    (![A:$i]:
% 10.38/10.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 10.38/10.56         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 10.38/10.56       ( ![B:$i]:
% 10.38/10.56         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 10.38/10.56           ( ![C:$i]:
% 10.38/10.56             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 10.38/10.56               ( ( r1_lattices @ A @ B @ C ) <=>
% 10.38/10.56                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 10.38/10.56  thf('29', plain,
% 10.38/10.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 10.38/10.56         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 10.38/10.56          | ~ (r1_lattices @ X18 @ X17 @ X19)
% 10.38/10.56          | ((k2_lattices @ X18 @ X17 @ X19) = (X17))
% 10.38/10.56          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X18))
% 10.38/10.56          | ~ (l3_lattices @ X18)
% 10.38/10.56          | ~ (v9_lattices @ X18)
% 10.38/10.56          | ~ (v8_lattices @ X18)
% 10.38/10.56          | (v2_struct_0 @ X18))),
% 10.38/10.56      inference('cnf', [status(esa)], [t21_lattices])).
% 10.38/10.56  thf('30', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.38/10.56          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 10.38/10.56              = (k15_lattice3 @ X0 @ X1))
% 10.38/10.56          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 10.38/10.56      inference('sup-', [status(thm)], ['28', '29'])).
% 10.38/10.56  thf('31', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.38/10.56         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 10.38/10.56          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 10.38/10.56              = (k15_lattice3 @ X0 @ X1))
% 10.38/10.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.38/10.56          | ~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['30'])).
% 10.38/10.56  thf('32', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         (~ (l3_lattices @ X1)
% 10.38/10.56          | ~ (v4_lattice3 @ X1)
% 10.38/10.56          | ~ (v10_lattices @ X1)
% 10.38/10.56          | (v2_struct_0 @ X1)
% 10.38/10.56          | ~ (v6_lattices @ X1)
% 10.38/10.56          | ~ (v8_lattices @ X1)
% 10.38/10.56          | ~ (v9_lattices @ X1)
% 10.38/10.56          | (v2_struct_0 @ X1)
% 10.38/10.56          | ~ (l3_lattices @ X1)
% 10.38/10.56          | ~ (v8_lattices @ X1)
% 10.38/10.56          | ~ (v9_lattices @ X1)
% 10.38/10.56          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 10.38/10.56          | ((k2_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 10.38/10.56              (k15_lattice3 @ X1 @ X0)) = (k15_lattice3 @ X1 @ k1_xboole_0)))),
% 10.38/10.56      inference('sup-', [status(thm)], ['27', '31'])).
% 10.38/10.56  thf('33', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         (((k2_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 10.38/10.56            (k15_lattice3 @ X1 @ X0)) = (k15_lattice3 @ X1 @ k1_xboole_0))
% 10.38/10.56          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 10.38/10.56          | ~ (v9_lattices @ X1)
% 10.38/10.56          | ~ (v8_lattices @ X1)
% 10.38/10.56          | ~ (v6_lattices @ X1)
% 10.38/10.56          | (v2_struct_0 @ X1)
% 10.38/10.56          | ~ (v10_lattices @ X1)
% 10.38/10.56          | ~ (v4_lattice3 @ X1)
% 10.38/10.56          | ~ (l3_lattices @ X1))),
% 10.38/10.56      inference('simplify', [status(thm)], ['32'])).
% 10.38/10.56  thf('34', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v9_lattices @ X0)
% 10.38/10.56          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 10.38/10.56              (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 10.38/10.56      inference('sup-', [status(thm)], ['15', '33'])).
% 10.38/10.56  thf('35', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 10.38/10.56            (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 10.38/10.56          | ~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['34'])).
% 10.38/10.56  thf('36', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 10.38/10.56            (k15_lattice3 @ X0 @ k1_xboole_0))
% 10.38/10.56            = (k15_lattice3 @ X0 @ k1_xboole_0))
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v9_lattices @ X0))),
% 10.38/10.56      inference('sup+', [status(thm)], ['14', '35'])).
% 10.38/10.56  thf('37', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         (~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 10.38/10.56              (k15_lattice3 @ X0 @ k1_xboole_0))
% 10.38/10.56              = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 10.38/10.56      inference('simplify', [status(thm)], ['36'])).
% 10.38/10.56  thf('38', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         (((k2_lattices @ X0 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 10.38/10.56            (k15_lattice3 @ X0 @ k1_xboole_0))
% 10.38/10.56            = (k15_lattice3 @ X0 @ k1_xboole_0))
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v13_lattices @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v9_lattices @ X0))),
% 10.38/10.56      inference('sup+', [status(thm)], ['7', '37'])).
% 10.38/10.56  thf('39', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         (~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | (v13_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ((k2_lattices @ X0 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 10.38/10.56              (k15_lattice3 @ X0 @ k1_xboole_0))
% 10.38/10.56              = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 10.38/10.56      inference('simplify', [status(thm)], ['38'])).
% 10.38/10.56  thf('40', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         (((k15_lattice3 @ X0 @ 
% 10.38/10.56            (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 10.38/10.56             (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 10.38/10.56            = (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | (v13_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['6'])).
% 10.38/10.56  thf('41', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 10.38/10.56            (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 10.38/10.56          | ~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['34'])).
% 10.38/10.56  thf('42', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 10.38/10.56            (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 10.38/10.56            = (k15_lattice3 @ X0 @ k1_xboole_0))
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v13_lattices @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v9_lattices @ X0))),
% 10.38/10.56      inference('sup+', [status(thm)], ['40', '41'])).
% 10.38/10.56  thf('43', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         (~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | (v13_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 10.38/10.56              (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 10.38/10.56              = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 10.38/10.56      inference('simplify', [status(thm)], ['42'])).
% 10.38/10.56  thf('44', plain,
% 10.38/10.56      (![X38 : $i, X40 : $i]:
% 10.38/10.56         (((k15_lattice3 @ X38 @ X40)
% 10.38/10.56            = (k15_lattice3 @ X38 @ (a_2_5_lattice3 @ X38 @ X40)))
% 10.38/10.56          | ~ (l3_lattices @ X38)
% 10.38/10.56          | ~ (v4_lattice3 @ X38)
% 10.38/10.56          | ~ (v10_lattices @ X38)
% 10.38/10.56          | (v2_struct_0 @ X38))),
% 10.38/10.56      inference('cnf', [status(esa)], [t47_lattice3])).
% 10.38/10.56  thf('45', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 10.38/10.56      inference('cnf', [status(esa)], [t2_xboole_1])).
% 10.38/10.56  thf(d3_tarski, axiom,
% 10.38/10.56    (![A:$i,B:$i]:
% 10.38/10.56     ( ( r1_tarski @ A @ B ) <=>
% 10.38/10.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 10.38/10.56  thf('46', plain,
% 10.38/10.56      (![X1 : $i, X3 : $i]:
% 10.38/10.56         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 10.38/10.56      inference('cnf', [status(esa)], [d3_tarski])).
% 10.38/10.56  thf(fraenkel_a_2_5_lattice3, axiom,
% 10.38/10.56    (![A:$i,B:$i,C:$i]:
% 10.38/10.56     ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 10.38/10.56         ( v4_lattice3 @ B ) & ( l3_lattices @ B ) ) =>
% 10.38/10.56       ( ( r2_hidden @ A @ ( a_2_5_lattice3 @ B @ C ) ) <=>
% 10.38/10.56         ( ?[D:$i]:
% 10.38/10.56           ( ( ?[E:$i]:
% 10.38/10.56               ( ( r2_hidden @ E @ C ) & ( r3_lattices @ B @ D @ E ) & 
% 10.38/10.56                 ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 10.38/10.56             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 10.38/10.56  thf('47', plain,
% 10.38/10.56      (![X28 : $i, X29 : $i, X30 : $i]:
% 10.38/10.56         (~ (l3_lattices @ X28)
% 10.38/10.56          | ~ (v4_lattice3 @ X28)
% 10.38/10.56          | ~ (v10_lattices @ X28)
% 10.38/10.56          | (v2_struct_0 @ X28)
% 10.38/10.56          | (r2_hidden @ (sk_E @ X29 @ X28 @ X30) @ X29)
% 10.38/10.56          | ~ (r2_hidden @ X30 @ (a_2_5_lattice3 @ X28 @ X29)))),
% 10.38/10.56      inference('cnf', [status(esa)], [fraenkel_a_2_5_lattice3])).
% 10.38/10.56  thf('48', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.38/10.56         ((r1_tarski @ (a_2_5_lattice3 @ X1 @ X0) @ X2)
% 10.38/10.56          | (r2_hidden @ 
% 10.38/10.56             (sk_E @ X0 @ X1 @ (sk_C @ X2 @ (a_2_5_lattice3 @ X1 @ X0))) @ X0)
% 10.38/10.56          | (v2_struct_0 @ X1)
% 10.38/10.56          | ~ (v10_lattices @ X1)
% 10.38/10.56          | ~ (v4_lattice3 @ X1)
% 10.38/10.56          | ~ (l3_lattices @ X1))),
% 10.38/10.56      inference('sup-', [status(thm)], ['46', '47'])).
% 10.38/10.56  thf(t7_ordinal1, axiom,
% 10.38/10.56    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 10.38/10.56  thf('49', plain,
% 10.38/10.56      (![X6 : $i, X7 : $i]: (~ (r2_hidden @ X6 @ X7) | ~ (r1_tarski @ X7 @ X6))),
% 10.38/10.56      inference('cnf', [status(esa)], [t7_ordinal1])).
% 10.38/10.56  thf('50', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.38/10.56         (~ (l3_lattices @ X1)
% 10.38/10.56          | ~ (v4_lattice3 @ X1)
% 10.38/10.56          | ~ (v10_lattices @ X1)
% 10.38/10.56          | (v2_struct_0 @ X1)
% 10.38/10.56          | (r1_tarski @ (a_2_5_lattice3 @ X1 @ X0) @ X2)
% 10.38/10.56          | ~ (r1_tarski @ X0 @ 
% 10.38/10.56               (sk_E @ X0 @ X1 @ (sk_C @ X2 @ (a_2_5_lattice3 @ X1 @ X0)))))),
% 10.38/10.56      inference('sup-', [status(thm)], ['48', '49'])).
% 10.38/10.56  thf('51', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         ((r1_tarski @ (a_2_5_lattice3 @ X0 @ k1_xboole_0) @ X1)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0))),
% 10.38/10.56      inference('sup-', [status(thm)], ['45', '50'])).
% 10.38/10.56  thf(t3_xboole_1, axiom,
% 10.38/10.56    (![A:$i]:
% 10.38/10.56     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 10.38/10.56  thf('52', plain,
% 10.38/10.56      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 10.38/10.56      inference('cnf', [status(esa)], [t3_xboole_1])).
% 10.38/10.56  thf('53', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         (~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ((a_2_5_lattice3 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 10.38/10.56      inference('sup-', [status(thm)], ['51', '52'])).
% 10.38/10.56  thf('54', plain,
% 10.38/10.56      (![X38 : $i, X40 : $i]:
% 10.38/10.56         (((k15_lattice3 @ X38 @ X40)
% 10.38/10.56            = (k15_lattice3 @ X38 @ (a_2_5_lattice3 @ X38 @ X40)))
% 10.38/10.56          | ~ (l3_lattices @ X38)
% 10.38/10.56          | ~ (v4_lattice3 @ X38)
% 10.38/10.56          | ~ (v10_lattices @ X38)
% 10.38/10.56          | (v2_struct_0 @ X38))),
% 10.38/10.56      inference('cnf', [status(esa)], [t47_lattice3])).
% 10.38/10.56  thf('55', plain,
% 10.38/10.56      (![X26 : $i, X27 : $i]:
% 10.38/10.56         (~ (l3_lattices @ X26)
% 10.38/10.56          | (v2_struct_0 @ X26)
% 10.38/10.56          | (m1_subset_1 @ (k15_lattice3 @ X26 @ X27) @ (u1_struct_0 @ X26)))),
% 10.38/10.56      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 10.38/10.56  thf('56', plain,
% 10.38/10.56      (![X20 : $i, X21 : $i]:
% 10.38/10.56         (((k2_lattices @ X21 @ (sk_C_2 @ X20 @ X21) @ X20) != (X20))
% 10.38/10.56          | ((k2_lattices @ X21 @ X20 @ (sk_C_2 @ X20 @ X21)) != (X20))
% 10.38/10.56          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X21))
% 10.38/10.56          | (v13_lattices @ X21)
% 10.38/10.56          | ~ (l1_lattices @ X21)
% 10.38/10.56          | (v2_struct_0 @ X21))),
% 10.38/10.56      inference('cnf', [status(esa)], [d13_lattices])).
% 10.38/10.56  thf('57', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v13_lattices @ X0)
% 10.38/10.56          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 10.38/10.56              (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 10.38/10.56              != (k15_lattice3 @ X0 @ X1))
% 10.38/10.56          | ((k2_lattices @ X0 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 10.38/10.56              (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1)))),
% 10.38/10.56      inference('sup-', [status(thm)], ['55', '56'])).
% 10.38/10.56  thf('58', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         (((k2_lattices @ X0 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 10.38/10.56            (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1))
% 10.38/10.56          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 10.38/10.56              (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 10.38/10.56              != (k15_lattice3 @ X0 @ X1))
% 10.38/10.56          | (v13_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['57'])).
% 10.38/10.56  thf('59', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         (((k2_lattices @ X1 @ (sk_C_2 @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 10.38/10.56            (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)))
% 10.38/10.56            != (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)))
% 10.38/10.56          | (v2_struct_0 @ X1)
% 10.38/10.56          | ~ (v10_lattices @ X1)
% 10.38/10.56          | ~ (v4_lattice3 @ X1)
% 10.38/10.56          | ~ (l3_lattices @ X1)
% 10.38/10.56          | (v2_struct_0 @ X1)
% 10.38/10.56          | ~ (l3_lattices @ X1)
% 10.38/10.56          | ~ (l1_lattices @ X1)
% 10.38/10.56          | (v13_lattices @ X1)
% 10.38/10.56          | ((k2_lattices @ X1 @ 
% 10.38/10.56              (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)) @ 
% 10.38/10.56              (sk_C_2 @ (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)) @ X1))
% 10.38/10.56              != (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0))))),
% 10.38/10.56      inference('sup-', [status(thm)], ['54', '58'])).
% 10.38/10.56  thf('60', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         (((k2_lattices @ X1 @ 
% 10.38/10.56            (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)) @ 
% 10.38/10.56            (sk_C_2 @ (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)) @ X1))
% 10.38/10.56            != (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)))
% 10.38/10.56          | (v13_lattices @ X1)
% 10.38/10.56          | ~ (l1_lattices @ X1)
% 10.38/10.56          | ~ (l3_lattices @ X1)
% 10.38/10.56          | ~ (v4_lattice3 @ X1)
% 10.38/10.56          | ~ (v10_lattices @ X1)
% 10.38/10.56          | (v2_struct_0 @ X1)
% 10.38/10.56          | ((k2_lattices @ X1 @ (sk_C_2 @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 10.38/10.56              (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)))
% 10.38/10.56              != (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0))))),
% 10.38/10.56      inference('simplify', [status(thm)], ['59'])).
% 10.38/10.56  thf('61', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 10.38/10.56            (sk_C_2 @ 
% 10.38/10.56             (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)) @ X0))
% 10.38/10.56            != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ((k2_lattices @ X0 @ 
% 10.38/10.56              (sk_C_2 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 10.38/10.56              (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 10.38/10.56              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v13_lattices @ X0))),
% 10.38/10.56      inference('sup-', [status(thm)], ['53', '60'])).
% 10.38/10.56  thf('62', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         ((v13_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ((k2_lattices @ X0 @ 
% 10.38/10.56              (sk_C_2 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 10.38/10.56              (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 10.38/10.56              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 10.38/10.56              (sk_C_2 @ 
% 10.38/10.56               (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)) @ X0))
% 10.38/10.56              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0))))),
% 10.38/10.56      inference('simplify', [status(thm)], ['61'])).
% 10.38/10.56  thf('63', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         (((k2_lattices @ X0 @ 
% 10.38/10.56            (sk_C_2 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 10.38/10.56            (k15_lattice3 @ X0 @ k1_xboole_0))
% 10.38/10.56            != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 10.38/10.56              (sk_C_2 @ 
% 10.38/10.56               (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)) @ X0))
% 10.38/10.56              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v13_lattices @ X0))),
% 10.38/10.56      inference('sup-', [status(thm)], ['44', '62'])).
% 10.38/10.56  thf('64', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         ((v13_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 10.38/10.56              (sk_C_2 @ 
% 10.38/10.56               (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)) @ X0))
% 10.38/10.56              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ((k2_lattices @ X0 @ 
% 10.38/10.56              (sk_C_2 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 10.38/10.56              (k15_lattice3 @ X0 @ k1_xboole_0))
% 10.38/10.56              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0))))),
% 10.38/10.56      inference('simplify', [status(thm)], ['63'])).
% 10.38/10.56  thf('65', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 10.38/10.56            != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v13_lattices @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v9_lattices @ X0)
% 10.38/10.56          | ((k2_lattices @ X0 @ 
% 10.38/10.56              (sk_C_2 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 10.38/10.56              (k15_lattice3 @ X0 @ k1_xboole_0))
% 10.38/10.56              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v13_lattices @ X0))),
% 10.38/10.56      inference('sup-', [status(thm)], ['43', '64'])).
% 10.38/10.56  thf('66', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         (((k2_lattices @ X0 @ 
% 10.38/10.56            (sk_C_2 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 10.38/10.56            (k15_lattice3 @ X0 @ k1_xboole_0))
% 10.38/10.56            != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 10.38/10.56          | ~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | (v13_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 10.38/10.56              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0))))),
% 10.38/10.56      inference('simplify', [status(thm)], ['65'])).
% 10.38/10.56  thf('67', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 10.38/10.56            != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v13_lattices @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v9_lattices @ X0)
% 10.38/10.56          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 10.38/10.56              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v13_lattices @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v9_lattices @ X0))),
% 10.38/10.56      inference('sup-', [status(thm)], ['39', '66'])).
% 10.38/10.56  thf('68', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         (~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | (v13_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 10.38/10.56              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0))))),
% 10.38/10.56      inference('simplify', [status(thm)], ['67'])).
% 10.38/10.56  thf('69', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 10.38/10.56            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v13_lattices @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v9_lattices @ X0))),
% 10.38/10.56      inference('sup-', [status(thm)], ['0', '68'])).
% 10.38/10.56  thf('70', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         (~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | (v13_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['69'])).
% 10.38/10.56  thf(t50_lattice3, conjecture,
% 10.38/10.56    (![A:$i]:
% 10.38/10.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 10.38/10.56         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 10.38/10.56       ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 10.38/10.56         ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 10.38/10.56         ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ))).
% 10.38/10.56  thf(zf_stmt_0, negated_conjecture,
% 10.38/10.56    (~( ![A:$i]:
% 10.38/10.56        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 10.38/10.56            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 10.38/10.56          ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 10.38/10.56            ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 10.38/10.56            ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ) )),
% 10.38/10.56    inference('cnf.neg', [status(esa)], [t50_lattice3])).
% 10.38/10.56  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('72', plain,
% 10.38/10.56      ((~ (v10_lattices @ sk_A)
% 10.38/10.56        | ~ (v4_lattice3 @ sk_A)
% 10.38/10.56        | ~ (l3_lattices @ sk_A)
% 10.38/10.56        | ~ (l1_lattices @ sk_A)
% 10.38/10.56        | (v13_lattices @ sk_A)
% 10.38/10.56        | ~ (v6_lattices @ sk_A)
% 10.38/10.56        | ~ (v8_lattices @ sk_A)
% 10.38/10.56        | ~ (v9_lattices @ sk_A))),
% 10.38/10.56      inference('sup-', [status(thm)], ['70', '71'])).
% 10.38/10.56  thf('73', plain, ((v10_lattices @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('74', plain, ((v4_lattice3 @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('75', plain, ((l3_lattices @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('76', plain, ((l3_lattices @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf(dt_l3_lattices, axiom,
% 10.38/10.56    (![A:$i]:
% 10.38/10.56     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 10.38/10.56  thf('77', plain,
% 10.38/10.56      (![X13 : $i]: ((l1_lattices @ X13) | ~ (l3_lattices @ X13))),
% 10.38/10.56      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 10.38/10.56  thf('78', plain, ((l1_lattices @ sk_A)),
% 10.38/10.56      inference('sup-', [status(thm)], ['76', '77'])).
% 10.38/10.56  thf(cc1_lattices, axiom,
% 10.38/10.56    (![A:$i]:
% 10.38/10.56     ( ( l3_lattices @ A ) =>
% 10.38/10.56       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 10.38/10.56         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 10.38/10.56           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 10.38/10.56           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 10.38/10.56  thf('79', plain,
% 10.38/10.56      (![X8 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X8)
% 10.38/10.56          | ~ (v10_lattices @ X8)
% 10.38/10.56          | (v6_lattices @ X8)
% 10.38/10.56          | ~ (l3_lattices @ X8))),
% 10.38/10.56      inference('cnf', [status(esa)], [cc1_lattices])).
% 10.38/10.56  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('81', plain,
% 10.38/10.56      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 10.38/10.56      inference('sup-', [status(thm)], ['79', '80'])).
% 10.38/10.56  thf('82', plain, ((l3_lattices @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('83', plain, ((v10_lattices @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('84', plain, ((v6_lattices @ sk_A)),
% 10.38/10.56      inference('demod', [status(thm)], ['81', '82', '83'])).
% 10.38/10.56  thf('85', plain,
% 10.38/10.56      (![X8 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X8)
% 10.38/10.56          | ~ (v10_lattices @ X8)
% 10.38/10.56          | (v8_lattices @ X8)
% 10.38/10.56          | ~ (l3_lattices @ X8))),
% 10.38/10.56      inference('cnf', [status(esa)], [cc1_lattices])).
% 10.38/10.56  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('87', plain,
% 10.38/10.56      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 10.38/10.56      inference('sup-', [status(thm)], ['85', '86'])).
% 10.38/10.56  thf('88', plain, ((l3_lattices @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('89', plain, ((v10_lattices @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('90', plain, ((v8_lattices @ sk_A)),
% 10.38/10.56      inference('demod', [status(thm)], ['87', '88', '89'])).
% 10.38/10.56  thf('91', plain,
% 10.38/10.56      (![X8 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X8)
% 10.38/10.56          | ~ (v10_lattices @ X8)
% 10.38/10.56          | (v9_lattices @ X8)
% 10.38/10.56          | ~ (l3_lattices @ X8))),
% 10.38/10.56      inference('cnf', [status(esa)], [cc1_lattices])).
% 10.38/10.56  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('93', plain,
% 10.38/10.56      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 10.38/10.56      inference('sup-', [status(thm)], ['91', '92'])).
% 10.38/10.56  thf('94', plain, ((l3_lattices @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('95', plain, ((v10_lattices @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('96', plain, ((v9_lattices @ sk_A)),
% 10.38/10.56      inference('demod', [status(thm)], ['93', '94', '95'])).
% 10.38/10.56  thf('97', plain, ((v13_lattices @ sk_A)),
% 10.38/10.56      inference('demod', [status(thm)],
% 10.38/10.56                ['72', '73', '74', '75', '78', '84', '90', '96'])).
% 10.38/10.56  thf('98', plain,
% 10.38/10.56      (![X26 : $i, X27 : $i]:
% 10.38/10.56         (~ (l3_lattices @ X26)
% 10.38/10.56          | (v2_struct_0 @ X26)
% 10.38/10.56          | (m1_subset_1 @ (k15_lattice3 @ X26 @ X27) @ (u1_struct_0 @ X26)))),
% 10.38/10.56      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 10.38/10.56  thf(dt_k5_lattices, axiom,
% 10.38/10.56    (![A:$i]:
% 10.38/10.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 10.38/10.56       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 10.38/10.56  thf('99', plain,
% 10.38/10.56      (![X12 : $i]:
% 10.38/10.56         ((m1_subset_1 @ (k5_lattices @ X12) @ (u1_struct_0 @ X12))
% 10.38/10.56          | ~ (l1_lattices @ X12)
% 10.38/10.56          | (v2_struct_0 @ X12))),
% 10.38/10.56      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 10.38/10.56  thf(d16_lattices, axiom,
% 10.38/10.56    (![A:$i]:
% 10.38/10.56     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 10.38/10.56       ( ( v13_lattices @ A ) =>
% 10.38/10.56         ( ![B:$i]:
% 10.38/10.56           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 10.38/10.56             ( ( ( B ) = ( k5_lattices @ A ) ) <=>
% 10.38/10.56               ( ![C:$i]:
% 10.38/10.56                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 10.38/10.56                   ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 10.38/10.56                     ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 10.38/10.56  thf('100', plain,
% 10.38/10.56      (![X9 : $i, X10 : $i, X11 : $i]:
% 10.38/10.56         (~ (v13_lattices @ X9)
% 10.38/10.56          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 10.38/10.56          | ((X10) != (k5_lattices @ X9))
% 10.38/10.56          | ((k2_lattices @ X9 @ X11 @ X10) = (X10))
% 10.38/10.56          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 10.38/10.56          | ~ (l1_lattices @ X9)
% 10.38/10.56          | (v2_struct_0 @ X9))),
% 10.38/10.56      inference('cnf', [status(esa)], [d16_lattices])).
% 10.38/10.56  thf('101', plain,
% 10.38/10.56      (![X9 : $i, X11 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X9)
% 10.38/10.56          | ~ (l1_lattices @ X9)
% 10.38/10.56          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 10.38/10.56          | ((k2_lattices @ X9 @ X11 @ (k5_lattices @ X9)) = (k5_lattices @ X9))
% 10.38/10.56          | ~ (m1_subset_1 @ (k5_lattices @ X9) @ (u1_struct_0 @ X9))
% 10.38/10.56          | ~ (v13_lattices @ X9))),
% 10.38/10.56      inference('simplify', [status(thm)], ['100'])).
% 10.38/10.56  thf('102', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (v13_lattices @ X0)
% 10.38/10.56          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 10.38/10.56          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('sup-', [status(thm)], ['99', '101'])).
% 10.38/10.56  thf('103', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 10.38/10.56          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 10.38/10.56          | ~ (v13_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['102'])).
% 10.38/10.56  thf('104', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (v13_lattices @ X0)
% 10.38/10.56          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 10.38/10.56              = (k5_lattices @ X0)))),
% 10.38/10.56      inference('sup-', [status(thm)], ['98', '103'])).
% 10.38/10.56  thf('105', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 10.38/10.56            = (k5_lattices @ X0))
% 10.38/10.56          | ~ (v13_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['104'])).
% 10.38/10.56  thf('106', plain,
% 10.38/10.56      (![X12 : $i]:
% 10.38/10.56         ((m1_subset_1 @ (k5_lattices @ X12) @ (u1_struct_0 @ X12))
% 10.38/10.56          | ~ (l1_lattices @ X12)
% 10.38/10.56          | (v2_struct_0 @ X12))),
% 10.38/10.56      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 10.38/10.56  thf('107', plain,
% 10.38/10.56      (![X12 : $i]:
% 10.38/10.56         ((m1_subset_1 @ (k5_lattices @ X12) @ (u1_struct_0 @ X12))
% 10.38/10.56          | ~ (l1_lattices @ X12)
% 10.38/10.56          | (v2_struct_0 @ X12))),
% 10.38/10.56      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 10.38/10.56  thf('108', plain,
% 10.38/10.56      (![X33 : $i, X34 : $i]:
% 10.38/10.56         (~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X34))
% 10.38/10.56          | ((k15_lattice3 @ X34 @ (k6_domain_1 @ (u1_struct_0 @ X34) @ X33))
% 10.38/10.56              = (X33))
% 10.38/10.56          | ~ (l3_lattices @ X34)
% 10.38/10.56          | ~ (v4_lattice3 @ X34)
% 10.38/10.56          | ~ (v10_lattices @ X34)
% 10.38/10.56          | (v2_struct_0 @ X34))),
% 10.38/10.56      inference('cnf', [status(esa)], [t43_lattice3])).
% 10.38/10.56  thf('109', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ((k15_lattice3 @ X0 @ 
% 10.38/10.56              (k6_domain_1 @ (u1_struct_0 @ X0) @ (k5_lattices @ X0)))
% 10.38/10.56              = (k5_lattices @ X0)))),
% 10.38/10.56      inference('sup-', [status(thm)], ['107', '108'])).
% 10.38/10.56  thf('110', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         (((k15_lattice3 @ X0 @ 
% 10.38/10.56            (k6_domain_1 @ (u1_struct_0 @ X0) @ (k5_lattices @ X0)))
% 10.38/10.56            = (k5_lattices @ X0))
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['109'])).
% 10.38/10.56  thf('111', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X1)
% 10.38/10.56          | ~ (v10_lattices @ X1)
% 10.38/10.56          | ~ (v4_lattice3 @ X1)
% 10.38/10.56          | ~ (l3_lattices @ X1)
% 10.38/10.56          | (r3_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 10.38/10.56             (k15_lattice3 @ X1 @ X0)))),
% 10.38/10.56      inference('sup-', [status(thm)], ['16', '17'])).
% 10.38/10.56  thf('112', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         ((r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 10.38/10.56           (k5_lattices @ X0))
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('sup+', [status(thm)], ['110', '111'])).
% 10.38/10.56  thf('113', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         (~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 10.38/10.56             (k5_lattices @ X0)))),
% 10.38/10.56      inference('simplify', [status(thm)], ['112'])).
% 10.38/10.56  thf('114', plain,
% 10.38/10.56      (![X12 : $i]:
% 10.38/10.56         ((m1_subset_1 @ (k5_lattices @ X12) @ (u1_struct_0 @ X12))
% 10.38/10.56          | ~ (l1_lattices @ X12)
% 10.38/10.56          | (v2_struct_0 @ X12))),
% 10.38/10.56      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 10.38/10.56  thf('115', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.38/10.56         (~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.38/10.56          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 10.38/10.56          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['22'])).
% 10.38/10.56  thf('116', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 10.38/10.56          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v9_lattices @ X0))),
% 10.38/10.56      inference('sup-', [status(thm)], ['114', '115'])).
% 10.38/10.56  thf('117', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i]:
% 10.38/10.56         (~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 10.38/10.56          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['116'])).
% 10.38/10.56  thf('118', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 10.38/10.56             (k5_lattices @ X0))
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v9_lattices @ X0))),
% 10.38/10.56      inference('sup-', [status(thm)], ['113', '117'])).
% 10.38/10.56  thf('119', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         (~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 10.38/10.56             (k5_lattices @ X0))
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['118'])).
% 10.38/10.56  thf('120', plain,
% 10.38/10.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.38/10.56         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 10.38/10.56          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 10.38/10.56              = (k15_lattice3 @ X0 @ X1))
% 10.38/10.56          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.38/10.56          | ~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['30'])).
% 10.38/10.56  thf('121', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v9_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 10.38/10.56          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 10.38/10.56              (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 10.38/10.56      inference('sup-', [status(thm)], ['119', '120'])).
% 10.38/10.56  thf('122', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 10.38/10.56            (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 10.38/10.56          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 10.38/10.56          | ~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['121'])).
% 10.38/10.56  thf('123', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         ((v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v9_lattices @ X0)
% 10.38/10.56          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 10.38/10.56              (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 10.38/10.56      inference('sup-', [status(thm)], ['106', '122'])).
% 10.38/10.56  thf('124', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 10.38/10.56            (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 10.38/10.56          | ~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0))),
% 10.38/10.56      inference('simplify', [status(thm)], ['123'])).
% 10.38/10.56  thf('125', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         (((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (v13_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v9_lattices @ X0))),
% 10.38/10.56      inference('sup+', [status(thm)], ['105', '124'])).
% 10.38/10.56  thf('126', plain,
% 10.38/10.56      (![X0 : $i]:
% 10.38/10.56         (~ (v9_lattices @ X0)
% 10.38/10.56          | ~ (v8_lattices @ X0)
% 10.38/10.56          | ~ (v6_lattices @ X0)
% 10.38/10.56          | ~ (v4_lattice3 @ X0)
% 10.38/10.56          | ~ (v10_lattices @ X0)
% 10.38/10.56          | ~ (v13_lattices @ X0)
% 10.38/10.56          | ~ (l1_lattices @ X0)
% 10.38/10.56          | ~ (l3_lattices @ X0)
% 10.38/10.56          | (v2_struct_0 @ X0)
% 10.38/10.56          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 10.38/10.56      inference('simplify', [status(thm)], ['125'])).
% 10.38/10.56  thf('127', plain,
% 10.38/10.56      (((v2_struct_0 @ sk_A)
% 10.38/10.56        | ~ (v10_lattices @ sk_A)
% 10.38/10.56        | ~ (v13_lattices @ sk_A)
% 10.38/10.56        | ~ (l3_lattices @ sk_A)
% 10.38/10.56        | ((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('128', plain,
% 10.38/10.56      ((((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))
% 10.38/10.56         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 10.38/10.56      inference('split', [status(esa)], ['127'])).
% 10.38/10.56  thf('129', plain,
% 10.38/10.56      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 10.38/10.56         | (v2_struct_0 @ sk_A)
% 10.38/10.56         | ~ (l3_lattices @ sk_A)
% 10.38/10.56         | ~ (l1_lattices @ sk_A)
% 10.38/10.56         | ~ (v13_lattices @ sk_A)
% 10.38/10.56         | ~ (v10_lattices @ sk_A)
% 10.38/10.56         | ~ (v4_lattice3 @ sk_A)
% 10.38/10.56         | ~ (v6_lattices @ sk_A)
% 10.38/10.56         | ~ (v8_lattices @ sk_A)
% 10.38/10.56         | ~ (v9_lattices @ sk_A)))
% 10.38/10.56         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 10.38/10.56      inference('sup-', [status(thm)], ['126', '128'])).
% 10.38/10.56  thf('130', plain, ((l3_lattices @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('131', plain, ((l1_lattices @ sk_A)),
% 10.38/10.56      inference('sup-', [status(thm)], ['76', '77'])).
% 10.38/10.56  thf('132', plain, ((v10_lattices @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('133', plain, ((v4_lattice3 @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('134', plain, ((v6_lattices @ sk_A)),
% 10.38/10.56      inference('demod', [status(thm)], ['81', '82', '83'])).
% 10.38/10.56  thf('135', plain, ((v8_lattices @ sk_A)),
% 10.38/10.56      inference('demod', [status(thm)], ['87', '88', '89'])).
% 10.38/10.56  thf('136', plain, ((v9_lattices @ sk_A)),
% 10.38/10.56      inference('demod', [status(thm)], ['93', '94', '95'])).
% 10.38/10.56  thf('137', plain,
% 10.38/10.56      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 10.38/10.56         | (v2_struct_0 @ sk_A)
% 10.38/10.56         | ~ (v13_lattices @ sk_A)))
% 10.38/10.56         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 10.38/10.56      inference('demod', [status(thm)],
% 10.38/10.56                ['129', '130', '131', '132', '133', '134', '135', '136'])).
% 10.38/10.56  thf('138', plain,
% 10.38/10.56      (((~ (v13_lattices @ sk_A) | (v2_struct_0 @ sk_A)))
% 10.38/10.56         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 10.38/10.56      inference('simplify', [status(thm)], ['137'])).
% 10.38/10.56  thf('139', plain, (~ (v2_struct_0 @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('140', plain,
% 10.38/10.56      ((~ (v13_lattices @ sk_A))
% 10.38/10.56         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 10.38/10.56      inference('clc', [status(thm)], ['138', '139'])).
% 10.38/10.56  thf('141', plain,
% 10.38/10.56      (($false)
% 10.38/10.56         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 10.38/10.56      inference('sup-', [status(thm)], ['97', '140'])).
% 10.38/10.56  thf('142', plain, (((v2_struct_0 @ sk_A)) <= (((v2_struct_0 @ sk_A)))),
% 10.38/10.56      inference('split', [status(esa)], ['127'])).
% 10.38/10.56  thf('143', plain, (~ (v2_struct_0 @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('144', plain, (~ ((v2_struct_0 @ sk_A))),
% 10.38/10.56      inference('sup-', [status(thm)], ['142', '143'])).
% 10.38/10.56  thf('145', plain, ((l3_lattices @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('146', plain, ((~ (l3_lattices @ sk_A)) <= (~ ((l3_lattices @ sk_A)))),
% 10.38/10.56      inference('split', [status(esa)], ['127'])).
% 10.38/10.56  thf('147', plain, (((l3_lattices @ sk_A))),
% 10.38/10.56      inference('sup-', [status(thm)], ['145', '146'])).
% 10.38/10.56  thf('148', plain, ((v10_lattices @ sk_A)),
% 10.38/10.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.38/10.56  thf('149', plain, ((~ (v10_lattices @ sk_A)) <= (~ ((v10_lattices @ sk_A)))),
% 10.38/10.56      inference('split', [status(esa)], ['127'])).
% 10.38/10.56  thf('150', plain, (((v10_lattices @ sk_A))),
% 10.38/10.56      inference('sup-', [status(thm)], ['148', '149'])).
% 10.38/10.56  thf('151', plain, ((v13_lattices @ sk_A)),
% 10.38/10.56      inference('demod', [status(thm)],
% 10.38/10.56                ['72', '73', '74', '75', '78', '84', '90', '96'])).
% 10.38/10.56  thf('152', plain, ((~ (v13_lattices @ sk_A)) <= (~ ((v13_lattices @ sk_A)))),
% 10.38/10.56      inference('split', [status(esa)], ['127'])).
% 10.38/10.56  thf('153', plain, (((v13_lattices @ sk_A))),
% 10.38/10.56      inference('sup-', [status(thm)], ['151', '152'])).
% 10.38/10.56  thf('154', plain,
% 10.38/10.56      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))) | 
% 10.38/10.56       ~ ((v13_lattices @ sk_A)) | ~ ((v10_lattices @ sk_A)) | 
% 10.38/10.56       ~ ((l3_lattices @ sk_A)) | ((v2_struct_0 @ sk_A))),
% 10.38/10.56      inference('split', [status(esa)], ['127'])).
% 10.38/10.56  thf('155', plain,
% 10.38/10.56      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 10.38/10.56      inference('sat_resolution*', [status(thm)],
% 10.38/10.56                ['144', '147', '150', '153', '154'])).
% 10.38/10.56  thf('156', plain, ($false),
% 10.38/10.56      inference('simpl_trail', [status(thm)], ['141', '155'])).
% 10.38/10.56  
% 10.38/10.56  % SZS output end Refutation
% 10.38/10.56  
% 10.42/10.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
