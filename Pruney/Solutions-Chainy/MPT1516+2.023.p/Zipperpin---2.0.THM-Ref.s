%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QAQw6xBFeT

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:37 EST 2020

% Result     : Theorem 4.42s
% Output     : Refutation 4.42s
% Verified   : 
% Statistics : Number of formulae       :  212 ( 539 expanded)
%              Number of leaves         :   44 ( 169 expanded)
%              Depth                    :   22
%              Number of atoms          : 3103 (8961 expanded)
%              Number of equality atoms :   93 ( 290 expanded)
%              Maximal formula depth    :   20 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

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

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( ( k15_lattice3 @ X27 @ ( k6_domain_1 @ ( u1_struct_0 @ X27 ) @ X26 ) )
        = X26 )
      | ~ ( l3_lattices @ X27 )
      | ~ ( v4_lattice3 @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t43_lattice3])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) ) )
        = ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) ) )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
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

thf('6',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ ( sk_D @ X30 @ X31 @ X29 ) @ X31 )
      | ( r3_lattices @ X29 @ ( k15_lattice3 @ X29 @ X31 ) @ ( k15_lattice3 @ X29 @ X30 ) )
      | ~ ( l3_lattices @ X29 )
      | ~ ( v4_lattice3 @ X29 )
      | ~ ( v10_lattices @ X29 )
      | ( v2_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t48_lattice3])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ~ ( r1_tarski @ X2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( r3_lattices @ X1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( k15_lattice3 @ X1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ ( sk_D @ X2 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
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

thf('12',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X16 ) )
      | ~ ( l3_lattices @ X16 )
      | ~ ( v9_lattices @ X16 )
      | ~ ( v8_lattices @ X16 )
      | ~ ( v6_lattices @ X16 )
      | ( v2_struct_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X16 ) )
      | ( r1_lattices @ X16 @ X15 @ X17 )
      | ~ ( r3_lattices @ X16 @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r3_lattices])).

thf('13',plain,(
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
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
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
    inference('sup-',[status(thm)],['10','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
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
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X1 )
      | ~ ( v8_lattices @ X1 )
      | ~ ( v6_lattices @ X1 )
      | ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(d3_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l2_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r1_lattices @ A @ B @ C )
              <=> ( ( k1_lattices @ A @ B @ C )
                  = C ) ) ) ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r1_lattices @ X8 @ X7 @ X9 )
      | ( ( k1_lattices @ X8 @ X7 @ X9 )
        = X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l2_lattices @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_lattices])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
        = X2 )
      | ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( ( k1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
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
      | ~ ( l2_lattices @ X1 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( ( k1_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) )
        = ( k15_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) )
        = ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( l2_lattices @ X1 )
      | ~ ( v9_lattices @ X1 )
      | ~ ( v8_lattices @ X1 )
      | ~ ( v6_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
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
      | ~ ( l2_lattices @ X0 )
      | ( ( k1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['4','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('28',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(d9_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( ( v9_lattices @ A )
      <=> ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) )
                  = B ) ) ) ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v9_lattices @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( ( k2_lattices @ X10 @ X12 @ ( k1_lattices @ X10 @ X12 @ X11 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_lattices])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X2 @ ( k1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) ) )
        = X2 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X2 @ ( k1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) ) )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ X2 ) ) )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ X2 ) ) )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) )
        = ( k15_lattice3 @ X1 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v6_lattices @ X1 )
      | ~ ( v8_lattices @ X1 )
      | ~ ( v9_lattices @ X1 )
      | ~ ( l2_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v9_lattices @ X1 ) ) ),
    inference('sup+',[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l2_lattices @ X1 )
      | ~ ( v9_lattices @ X1 )
      | ~ ( v8_lattices @ X1 )
      | ~ ( v6_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( ( k2_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) )
        = ( k15_lattice3 @ X1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) ) )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('37',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
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

thf('38',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( sk_C_2 @ X18 @ X19 ) @ ( u1_struct_0 @ X19 ) )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( v13_lattices @ X19 )
      | ~ ( l1_lattices @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d13_lattices])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( m1_subset_1 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( ( k15_lattice3 @ X27 @ ( k6_domain_1 @ ( u1_struct_0 @ X27 ) @ X26 ) )
        = X26 )
      | ~ ( l3_lattices @ X27 )
      | ~ ( v4_lattice3 @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t43_lattice3])).

thf('42',plain,(
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
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) )
        = ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ ( sk_C_2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) ) )
        = ( sk_C_2 @ ( k15_lattice3 @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ ( k15_lattice3 @ X1 @ X0 ) ) ) @ X1 ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l1_lattices @ X1 )
      | ( v13_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v13_lattices @ X1 )
      | ~ ( l1_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( ( k15_lattice3 @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ ( sk_C_2 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) ) )
        = ( sk_C_2 @ ( k15_lattice3 @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ ( k15_lattice3 @ X1 @ X0 ) ) ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) ) )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('48',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
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

thf('49',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v6_lattices @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X21 ) )
      | ( ( k2_lattices @ X21 @ X23 @ X22 )
        = ( k2_lattices @ X21 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ~ ( l1_lattices @ X21 )
      | ( v2_struct_0 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d6_lattices])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X2 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X2 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('55',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k2_lattices @ X19 @ ( sk_C_2 @ X18 @ X19 ) @ X18 )
       != X18 )
      | ( ( k2_lattices @ X19 @ X18 @ ( sk_C_2 @ X18 @ X19 ) )
       != X18 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( v13_lattices @ X19 )
      | ~ ( l1_lattices @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d13_lattices])).

thf('56',plain,(
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
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
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
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['53','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( sk_C_2 @ ( k15_lattice3 @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ ( k15_lattice3 @ X1 @ X0 ) ) ) @ X1 ) )
       != ( k15_lattice3 @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ ( k15_lattice3 @ X1 @ X0 ) ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l1_lattices @ X1 )
      | ( v13_lattices @ X1 )
      | ~ ( v6_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v6_lattices @ X1 )
      | ( v13_lattices @ X1 )
      | ~ ( l1_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( ( k2_lattices @ X1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( sk_C_2 @ ( k15_lattice3 @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ ( k15_lattice3 @ X1 @ X0 ) ) ) @ X1 ) )
       != ( k15_lattice3 @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ ( k15_lattice3 @ X1 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) ) )
       != ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C_2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) ) )
       != ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
       != ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
       != ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
       != ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

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

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( v13_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
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

thf('73',plain,(
    ! [X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v6_lattices @ X3 )
      | ~ ( l3_lattices @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('74',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,(
    ! [X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v8_lattices @ X3 )
      | ~ ( l3_lattices @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X3: $i] :
      ( ( v2_struct_0 @ X3 )
      | ~ ( v10_lattices @ X3 )
      | ( v9_lattices @ X3 )
      | ~ ( l3_lattices @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('92',plain,(
    ! [X14: $i] :
      ( ( l2_lattices @ X14 )
      | ~ ( l3_lattices @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('93',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X14: $i] :
      ( ( l1_lattices @ X14 )
      | ~ ( l3_lattices @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('96',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['69','70','71','72','78','84','90','93','96'])).

thf('98',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(dt_k5_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('99',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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

thf('101',plain,(
    ! [X4: $i,X6: $i] :
      ( ( v2_struct_0 @ X4 )
      | ~ ( l1_lattices @ X4 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X4 ) )
      | ( ( k2_lattices @ X4 @ X6 @ ( k5_lattices @ X4 ) )
        = ( k5_lattices @ X4 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X4 ) @ ( u1_struct_0 @ X4 ) )
      | ~ ( v13_lattices @ X4 ) ) ),
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
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('107',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('108',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X27 ) )
      | ( ( k15_lattice3 @ X27 @ ( k6_domain_1 @ ( u1_struct_0 @ X27 ) @ X26 ) )
        = X26 )
      | ~ ( l3_lattices @ X27 )
      | ~ ( v4_lattice3 @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
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
      ( ( r3_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('112',plain,(
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
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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
    inference(simplify,[status(thm)],['13'])).

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
      | ( ( k1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

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
      | ~ ( l2_lattices @ X0 )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
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
      | ~ ( l2_lattices @ X0 )
      | ( ( k1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['106','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( ( k1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( l2_lattices @ X0 )
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
    ! [X24: $i,X25: $i] :
      ( ~ ( l3_lattices @ X24 )
      | ( v2_struct_0 @ X24 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X24 @ X25 ) @ ( u1_struct_0 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('126',plain,(
    ! [X13: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X13 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_lattices @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('127',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v9_lattices @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ( ( k2_lattices @ X10 @ X12 @ ( k1_lattices @ X10 @ X12 @ X11 ) )
        = X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l3_lattices @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d9_lattices])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X1 @ ( k1_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) ) )
        = X1 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X1 @ ( k1_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) ) )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['128'])).

thf('130',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) ) )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) ) )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['124','131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
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
      | ~ ( v9_lattices @ X0 )
      | ~ ( l2_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['105','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ~ ( l2_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
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
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['136'])).

thf('138',plain,
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
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l2_lattices @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['135','137'])).

thf('139',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['94','95'])).

thf('141',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('144',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('145',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('146',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['91','92'])).

thf('147',plain,
    ( ( ( ( k5_lattices @ sk_A )
       != ( k5_lattices @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v13_lattices @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['138','139','140','141','142','143','144','145','146'])).

thf('148',plain,
    ( ( ~ ( v13_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,
    ( $false
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['97','150'])).

thf('152',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['136'])).

thf('153',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ~ ( l3_lattices @ sk_A )
   <= ~ ( l3_lattices @ sk_A ) ),
    inference(split,[status(esa)],['136'])).

thf('157',plain,(
    l3_lattices @ sk_A ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ~ ( v10_lattices @ sk_A )
   <= ~ ( v10_lattices @ sk_A ) ),
    inference(split,[status(esa)],['136'])).

thf('160',plain,(
    v10_lattices @ sk_A ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['69','70','71','72','78','84','90','93','96'])).

thf('162',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ~ ( v13_lattices @ sk_A ) ),
    inference(split,[status(esa)],['136'])).

thf('163',plain,(
    v13_lattices @ sk_A ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['136'])).

thf('165',plain,(
    ( k5_lattices @ sk_A )
 != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ),
    inference('sat_resolution*',[status(thm)],['154','157','160','163','164'])).

thf('166',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['151','165'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QAQw6xBFeT
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:34:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 4.42/4.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.42/4.60  % Solved by: fo/fo7.sh
% 4.42/4.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.42/4.60  % done 2358 iterations in 4.149s
% 4.42/4.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.42/4.60  % SZS output start Refutation
% 4.42/4.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.42/4.60  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 4.42/4.60  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 4.42/4.60  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 4.42/4.60  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 4.42/4.60  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 4.42/4.60  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 4.42/4.60  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 4.42/4.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.42/4.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 4.42/4.60  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 4.42/4.60  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 4.42/4.60  thf(sk_A_type, type, sk_A: $i).
% 4.42/4.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.42/4.60  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 4.42/4.60  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 4.42/4.60  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 4.42/4.60  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 4.42/4.60  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 4.42/4.60  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 4.42/4.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.42/4.60  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 4.42/4.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 4.42/4.60  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 4.42/4.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.42/4.60  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 4.42/4.60  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 4.42/4.60  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 4.42/4.60  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 4.42/4.60  thf(dt_k15_lattice3, axiom,
% 4.42/4.60    (![A:$i,B:$i]:
% 4.42/4.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 4.42/4.60       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 4.42/4.60  thf('0', plain,
% 4.42/4.60      (![X24 : $i, X25 : $i]:
% 4.42/4.60         (~ (l3_lattices @ X24)
% 4.42/4.60          | (v2_struct_0 @ X24)
% 4.42/4.60          | (m1_subset_1 @ (k15_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 4.42/4.60      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 4.42/4.60  thf(t43_lattice3, axiom,
% 4.42/4.60    (![A:$i]:
% 4.42/4.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 4.42/4.60         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 4.42/4.60       ( ![B:$i]:
% 4.42/4.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 4.42/4.60           ( ( ( k15_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 4.42/4.60               ( B ) ) & 
% 4.42/4.60             ( ( k16_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 4.42/4.60               ( B ) ) ) ) ) ))).
% 4.42/4.60  thf('1', plain,
% 4.42/4.60      (![X26 : $i, X27 : $i]:
% 4.42/4.60         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 4.42/4.60          | ((k15_lattice3 @ X27 @ (k6_domain_1 @ (u1_struct_0 @ X27) @ X26))
% 4.42/4.60              = (X26))
% 4.42/4.60          | ~ (l3_lattices @ X27)
% 4.42/4.60          | ~ (v4_lattice3 @ X27)
% 4.42/4.60          | ~ (v10_lattices @ X27)
% 4.42/4.60          | (v2_struct_0 @ X27))),
% 4.42/4.60      inference('cnf', [status(esa)], [t43_lattice3])).
% 4.42/4.60  thf('2', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ((k15_lattice3 @ X0 @ 
% 4.42/4.60              (k6_domain_1 @ (u1_struct_0 @ X0) @ (k15_lattice3 @ X0 @ X1)))
% 4.42/4.60              = (k15_lattice3 @ X0 @ X1)))),
% 4.42/4.60      inference('sup-', [status(thm)], ['0', '1'])).
% 4.42/4.60  thf('3', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (((k15_lattice3 @ X0 @ 
% 4.42/4.60            (k6_domain_1 @ (u1_struct_0 @ X0) @ (k15_lattice3 @ X0 @ X1)))
% 4.42/4.60            = (k15_lattice3 @ X0 @ X1))
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['2'])).
% 4.42/4.60  thf('4', plain,
% 4.42/4.60      (![X24 : $i, X25 : $i]:
% 4.42/4.60         (~ (l3_lattices @ X24)
% 4.42/4.60          | (v2_struct_0 @ X24)
% 4.42/4.60          | (m1_subset_1 @ (k15_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 4.42/4.60      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 4.42/4.60  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 4.42/4.60  thf('5', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 4.42/4.60      inference('cnf', [status(esa)], [t2_xboole_1])).
% 4.42/4.60  thf(t48_lattice3, axiom,
% 4.42/4.60    (![A:$i]:
% 4.42/4.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 4.42/4.60         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 4.42/4.60       ( ![B:$i,C:$i]:
% 4.42/4.60         ( ( ![D:$i]:
% 4.42/4.60             ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 4.42/4.60               ( ~( ( r2_hidden @ D @ B ) & 
% 4.42/4.60                    ( ![E:$i]:
% 4.42/4.60                      ( ( m1_subset_1 @ E @ ( u1_struct_0 @ A ) ) =>
% 4.42/4.60                        ( ~( ( r3_lattices @ A @ D @ E ) & 
% 4.42/4.60                             ( r2_hidden @ E @ C ) ) ) ) ) ) ) ) ) =>
% 4.42/4.60           ( r3_lattices @
% 4.42/4.60             A @ ( k15_lattice3 @ A @ B ) @ ( k15_lattice3 @ A @ C ) ) ) ) ))).
% 4.42/4.60  thf('6', plain,
% 4.42/4.60      (![X29 : $i, X30 : $i, X31 : $i]:
% 4.42/4.60         ((r2_hidden @ (sk_D @ X30 @ X31 @ X29) @ X31)
% 4.42/4.60          | (r3_lattices @ X29 @ (k15_lattice3 @ X29 @ X31) @ 
% 4.42/4.60             (k15_lattice3 @ X29 @ X30))
% 4.42/4.60          | ~ (l3_lattices @ X29)
% 4.42/4.60          | ~ (v4_lattice3 @ X29)
% 4.42/4.60          | ~ (v10_lattices @ X29)
% 4.42/4.60          | (v2_struct_0 @ X29))),
% 4.42/4.60      inference('cnf', [status(esa)], [t48_lattice3])).
% 4.42/4.60  thf(t7_ordinal1, axiom,
% 4.42/4.60    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 4.42/4.60  thf('7', plain,
% 4.42/4.60      (![X1 : $i, X2 : $i]: (~ (r2_hidden @ X1 @ X2) | ~ (r1_tarski @ X2 @ X1))),
% 4.42/4.60      inference('cnf', [status(esa)], [t7_ordinal1])).
% 4.42/4.60  thf('8', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X1)
% 4.42/4.60          | ~ (v10_lattices @ X1)
% 4.42/4.60          | ~ (v4_lattice3 @ X1)
% 4.42/4.60          | ~ (l3_lattices @ X1)
% 4.42/4.60          | (r3_lattices @ X1 @ (k15_lattice3 @ X1 @ X0) @ 
% 4.42/4.60             (k15_lattice3 @ X1 @ X2))
% 4.42/4.60          | ~ (r1_tarski @ X0 @ (sk_D @ X2 @ X0 @ X1)))),
% 4.42/4.60      inference('sup-', [status(thm)], ['6', '7'])).
% 4.42/4.60  thf('9', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         ((r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.42/4.60           (k15_lattice3 @ X0 @ X1))
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('sup-', [status(thm)], ['5', '8'])).
% 4.42/4.60  thf('10', plain,
% 4.42/4.60      (![X24 : $i, X25 : $i]:
% 4.42/4.60         (~ (l3_lattices @ X24)
% 4.42/4.60          | (v2_struct_0 @ X24)
% 4.42/4.60          | (m1_subset_1 @ (k15_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 4.42/4.60      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 4.42/4.60  thf('11', plain,
% 4.42/4.60      (![X24 : $i, X25 : $i]:
% 4.42/4.60         (~ (l3_lattices @ X24)
% 4.42/4.60          | (v2_struct_0 @ X24)
% 4.42/4.60          | (m1_subset_1 @ (k15_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 4.42/4.60      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 4.42/4.60  thf(redefinition_r3_lattices, axiom,
% 4.42/4.60    (![A:$i,B:$i,C:$i]:
% 4.42/4.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 4.42/4.60         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) & 
% 4.42/4.60         ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) & 
% 4.42/4.60         ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) ) =>
% 4.42/4.60       ( ( r3_lattices @ A @ B @ C ) <=> ( r1_lattices @ A @ B @ C ) ) ))).
% 4.42/4.60  thf('12', plain,
% 4.42/4.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 4.42/4.60         (~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X16))
% 4.42/4.60          | ~ (l3_lattices @ X16)
% 4.42/4.60          | ~ (v9_lattices @ X16)
% 4.42/4.60          | ~ (v8_lattices @ X16)
% 4.42/4.60          | ~ (v6_lattices @ X16)
% 4.42/4.60          | (v2_struct_0 @ X16)
% 4.42/4.60          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X16))
% 4.42/4.60          | (r1_lattices @ X16 @ X15 @ X17)
% 4.42/4.60          | ~ (r3_lattices @ X16 @ X15 @ X17))),
% 4.42/4.60      inference('cnf', [status(esa)], [redefinition_r3_lattices])).
% 4.42/4.60  thf('13', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 4.42/4.60          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 4.42/4.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v9_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0))),
% 4.42/4.60      inference('sup-', [status(thm)], ['11', '12'])).
% 4.42/4.60  thf('14', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.60         (~ (v9_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.42/4.60          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 4.42/4.60          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['13'])).
% 4.42/4.60  thf('15', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 4.42/4.60               (k15_lattice3 @ X0 @ X1))
% 4.42/4.60          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 4.42/4.60             (k15_lattice3 @ X0 @ X1))
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v9_lattices @ X0))),
% 4.42/4.60      inference('sup-', [status(thm)], ['10', '14'])).
% 4.42/4.60  thf('16', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.60         (~ (v9_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 4.42/4.60             (k15_lattice3 @ X0 @ X1))
% 4.42/4.60          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 4.42/4.60               (k15_lattice3 @ X0 @ X1))
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['15'])).
% 4.42/4.60  thf('17', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X1)
% 4.42/4.60          | ~ (v10_lattices @ X1)
% 4.42/4.60          | ~ (v4_lattice3 @ X1)
% 4.42/4.60          | ~ (l3_lattices @ X1)
% 4.42/4.60          | (v2_struct_0 @ X1)
% 4.42/4.60          | ~ (l3_lattices @ X1)
% 4.42/4.60          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 4.42/4.60             (k15_lattice3 @ X1 @ X0))
% 4.42/4.60          | ~ (v6_lattices @ X1)
% 4.42/4.60          | ~ (v8_lattices @ X1)
% 4.42/4.60          | ~ (v9_lattices @ X1))),
% 4.42/4.60      inference('sup-', [status(thm)], ['9', '16'])).
% 4.42/4.60  thf('18', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (~ (v9_lattices @ X1)
% 4.42/4.60          | ~ (v8_lattices @ X1)
% 4.42/4.60          | ~ (v6_lattices @ X1)
% 4.42/4.60          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 4.42/4.60             (k15_lattice3 @ X1 @ X0))
% 4.42/4.60          | ~ (l3_lattices @ X1)
% 4.42/4.60          | ~ (v4_lattice3 @ X1)
% 4.42/4.60          | ~ (v10_lattices @ X1)
% 4.42/4.60          | (v2_struct_0 @ X1))),
% 4.42/4.60      inference('simplify', [status(thm)], ['17'])).
% 4.42/4.60  thf('19', plain,
% 4.42/4.60      (![X24 : $i, X25 : $i]:
% 4.42/4.60         (~ (l3_lattices @ X24)
% 4.42/4.60          | (v2_struct_0 @ X24)
% 4.42/4.60          | (m1_subset_1 @ (k15_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 4.42/4.60      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 4.42/4.60  thf(d3_lattices, axiom,
% 4.42/4.60    (![A:$i]:
% 4.42/4.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l2_lattices @ A ) ) =>
% 4.42/4.60       ( ![B:$i]:
% 4.42/4.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 4.42/4.60           ( ![C:$i]:
% 4.42/4.60             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.42/4.60               ( ( r1_lattices @ A @ B @ C ) <=>
% 4.42/4.60                 ( ( k1_lattices @ A @ B @ C ) = ( C ) ) ) ) ) ) ) ))).
% 4.42/4.60  thf('20', plain,
% 4.42/4.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 4.42/4.60         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 4.42/4.60          | ~ (r1_lattices @ X8 @ X7 @ X9)
% 4.42/4.60          | ((k1_lattices @ X8 @ X7 @ X9) = (X9))
% 4.42/4.60          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 4.42/4.60          | ~ (l2_lattices @ X8)
% 4.42/4.60          | (v2_struct_0 @ X8))),
% 4.42/4.60      inference('cnf', [status(esa)], [d3_lattices])).
% 4.42/4.60  thf('21', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l2_lattices @ X0)
% 4.42/4.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.42/4.60          | ((k1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2) = (X2))
% 4.42/4.60          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 4.42/4.60      inference('sup-', [status(thm)], ['19', '20'])).
% 4.42/4.60  thf('22', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.60         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 4.42/4.60          | ((k1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2) = (X2))
% 4.42/4.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.42/4.60          | ~ (l2_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['21'])).
% 4.42/4.60  thf('23', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X1)
% 4.42/4.60          | ~ (v10_lattices @ X1)
% 4.42/4.60          | ~ (v4_lattice3 @ X1)
% 4.42/4.60          | ~ (l3_lattices @ X1)
% 4.42/4.60          | ~ (v6_lattices @ X1)
% 4.42/4.60          | ~ (v8_lattices @ X1)
% 4.42/4.60          | ~ (v9_lattices @ X1)
% 4.42/4.60          | (v2_struct_0 @ X1)
% 4.42/4.60          | ~ (l3_lattices @ X1)
% 4.42/4.60          | ~ (l2_lattices @ X1)
% 4.42/4.60          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 4.42/4.60          | ((k1_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 4.42/4.60              (k15_lattice3 @ X1 @ X0)) = (k15_lattice3 @ X1 @ X0)))),
% 4.42/4.60      inference('sup-', [status(thm)], ['18', '22'])).
% 4.42/4.60  thf('24', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (((k1_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 4.42/4.60            (k15_lattice3 @ X1 @ X0)) = (k15_lattice3 @ X1 @ X0))
% 4.42/4.60          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 4.42/4.60          | ~ (l2_lattices @ X1)
% 4.42/4.60          | ~ (v9_lattices @ X1)
% 4.42/4.60          | ~ (v8_lattices @ X1)
% 4.42/4.60          | ~ (v6_lattices @ X1)
% 4.42/4.60          | ~ (l3_lattices @ X1)
% 4.42/4.60          | ~ (v4_lattice3 @ X1)
% 4.42/4.60          | ~ (v10_lattices @ X1)
% 4.42/4.60          | (v2_struct_0 @ X1))),
% 4.42/4.60      inference('simplify', [status(thm)], ['23'])).
% 4.42/4.60  thf('25', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v9_lattices @ X0)
% 4.42/4.60          | ~ (l2_lattices @ X0)
% 4.42/4.60          | ((k1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.42/4.60              (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ X1)))),
% 4.42/4.60      inference('sup-', [status(thm)], ['4', '24'])).
% 4.42/4.60  thf('26', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (((k1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.42/4.60            (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ X1))
% 4.42/4.60          | ~ (l2_lattices @ X0)
% 4.42/4.60          | ~ (v9_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['25'])).
% 4.42/4.60  thf('27', plain,
% 4.42/4.60      (![X24 : $i, X25 : $i]:
% 4.42/4.60         (~ (l3_lattices @ X24)
% 4.42/4.60          | (v2_struct_0 @ X24)
% 4.42/4.60          | (m1_subset_1 @ (k15_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 4.42/4.60      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 4.42/4.60  thf('28', plain,
% 4.42/4.60      (![X24 : $i, X25 : $i]:
% 4.42/4.60         (~ (l3_lattices @ X24)
% 4.42/4.60          | (v2_struct_0 @ X24)
% 4.42/4.60          | (m1_subset_1 @ (k15_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 4.42/4.60      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 4.42/4.60  thf(d9_lattices, axiom,
% 4.42/4.60    (![A:$i]:
% 4.42/4.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 4.42/4.60       ( ( v9_lattices @ A ) <=>
% 4.42/4.60         ( ![B:$i]:
% 4.42/4.60           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 4.42/4.60             ( ![C:$i]:
% 4.42/4.60               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.42/4.60                 ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) =
% 4.42/4.60                   ( B ) ) ) ) ) ) ) ))).
% 4.42/4.60  thf('29', plain,
% 4.42/4.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 4.42/4.60         (~ (v9_lattices @ X10)
% 4.42/4.60          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 4.42/4.60          | ((k2_lattices @ X10 @ X12 @ (k1_lattices @ X10 @ X12 @ X11))
% 4.42/4.60              = (X12))
% 4.42/4.60          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 4.42/4.60          | ~ (l3_lattices @ X10)
% 4.42/4.60          | (v2_struct_0 @ X10))),
% 4.42/4.60      inference('cnf', [status(esa)], [d9_lattices])).
% 4.42/4.60  thf('30', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.42/4.60          | ((k2_lattices @ X0 @ X2 @ 
% 4.42/4.60              (k1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))) = (X2))
% 4.42/4.60          | ~ (v9_lattices @ X0))),
% 4.42/4.60      inference('sup-', [status(thm)], ['28', '29'])).
% 4.42/4.60  thf('31', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.60         (~ (v9_lattices @ X0)
% 4.42/4.60          | ((k2_lattices @ X0 @ X2 @ 
% 4.42/4.60              (k1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))) = (X2))
% 4.42/4.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['30'])).
% 4.42/4.60  thf('32', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 4.42/4.60              (k1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 4.42/4.60               (k15_lattice3 @ X0 @ X2)))
% 4.42/4.60              = (k15_lattice3 @ X0 @ X1))
% 4.42/4.60          | ~ (v9_lattices @ X0))),
% 4.42/4.60      inference('sup-', [status(thm)], ['27', '31'])).
% 4.42/4.60  thf('33', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.60         (~ (v9_lattices @ X0)
% 4.42/4.60          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 4.42/4.60              (k1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 4.42/4.60               (k15_lattice3 @ X0 @ X2)))
% 4.42/4.60              = (k15_lattice3 @ X0 @ X1))
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['32'])).
% 4.42/4.60  thf('34', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (((k2_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 4.42/4.60            (k15_lattice3 @ X1 @ X0)) = (k15_lattice3 @ X1 @ k1_xboole_0))
% 4.42/4.60          | (v2_struct_0 @ X1)
% 4.42/4.60          | ~ (l3_lattices @ X1)
% 4.42/4.60          | ~ (v10_lattices @ X1)
% 4.42/4.60          | ~ (v4_lattice3 @ X1)
% 4.42/4.60          | ~ (v6_lattices @ X1)
% 4.42/4.60          | ~ (v8_lattices @ X1)
% 4.42/4.60          | ~ (v9_lattices @ X1)
% 4.42/4.60          | ~ (l2_lattices @ X1)
% 4.42/4.60          | (v2_struct_0 @ X1)
% 4.42/4.60          | ~ (l3_lattices @ X1)
% 4.42/4.60          | ~ (v9_lattices @ X1))),
% 4.42/4.60      inference('sup+', [status(thm)], ['26', '33'])).
% 4.42/4.60  thf('35', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (~ (l2_lattices @ X1)
% 4.42/4.60          | ~ (v9_lattices @ X1)
% 4.42/4.60          | ~ (v8_lattices @ X1)
% 4.42/4.60          | ~ (v6_lattices @ X1)
% 4.42/4.60          | ~ (v4_lattice3 @ X1)
% 4.42/4.60          | ~ (v10_lattices @ X1)
% 4.42/4.60          | ~ (l3_lattices @ X1)
% 4.42/4.60          | (v2_struct_0 @ X1)
% 4.42/4.60          | ((k2_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 4.42/4.60              (k15_lattice3 @ X1 @ X0)) = (k15_lattice3 @ X1 @ k1_xboole_0)))),
% 4.42/4.60      inference('simplify', [status(thm)], ['34'])).
% 4.42/4.60  thf('36', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (((k15_lattice3 @ X0 @ 
% 4.42/4.60            (k6_domain_1 @ (u1_struct_0 @ X0) @ (k15_lattice3 @ X0 @ X1)))
% 4.42/4.60            = (k15_lattice3 @ X0 @ X1))
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['2'])).
% 4.42/4.60  thf('37', plain,
% 4.42/4.60      (![X24 : $i, X25 : $i]:
% 4.42/4.60         (~ (l3_lattices @ X24)
% 4.42/4.60          | (v2_struct_0 @ X24)
% 4.42/4.60          | (m1_subset_1 @ (k15_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 4.42/4.60      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 4.42/4.60  thf(d13_lattices, axiom,
% 4.42/4.60    (![A:$i]:
% 4.42/4.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 4.42/4.60       ( ( v13_lattices @ A ) <=>
% 4.42/4.60         ( ?[B:$i]:
% 4.42/4.60           ( ( ![C:$i]:
% 4.42/4.60               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.42/4.60                 ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 4.42/4.60                   ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) & 
% 4.42/4.60             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 4.42/4.60  thf('38', plain,
% 4.42/4.60      (![X18 : $i, X19 : $i]:
% 4.42/4.60         ((m1_subset_1 @ (sk_C_2 @ X18 @ X19) @ (u1_struct_0 @ X19))
% 4.42/4.60          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 4.42/4.60          | (v13_lattices @ X19)
% 4.42/4.60          | ~ (l1_lattices @ X19)
% 4.42/4.60          | (v2_struct_0 @ X19))),
% 4.42/4.60      inference('cnf', [status(esa)], [d13_lattices])).
% 4.42/4.60  thf('39', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v13_lattices @ X0)
% 4.42/4.60          | (m1_subset_1 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 4.42/4.60             (u1_struct_0 @ X0)))),
% 4.42/4.60      inference('sup-', [status(thm)], ['37', '38'])).
% 4.42/4.60  thf('40', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         ((m1_subset_1 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 4.42/4.60           (u1_struct_0 @ X0))
% 4.42/4.60          | (v13_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['39'])).
% 4.42/4.60  thf('41', plain,
% 4.42/4.60      (![X26 : $i, X27 : $i]:
% 4.42/4.60         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 4.42/4.60          | ((k15_lattice3 @ X27 @ (k6_domain_1 @ (u1_struct_0 @ X27) @ X26))
% 4.42/4.60              = (X26))
% 4.42/4.60          | ~ (l3_lattices @ X27)
% 4.42/4.60          | ~ (v4_lattice3 @ X27)
% 4.42/4.60          | ~ (v10_lattices @ X27)
% 4.42/4.60          | (v2_struct_0 @ X27))),
% 4.42/4.60      inference('cnf', [status(esa)], [t43_lattice3])).
% 4.42/4.60  thf('42', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v13_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ((k15_lattice3 @ X0 @ 
% 4.42/4.60              (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 4.42/4.60               (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 4.42/4.60              = (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0)))),
% 4.42/4.60      inference('sup-', [status(thm)], ['40', '41'])).
% 4.42/4.60  thf('43', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (((k15_lattice3 @ X0 @ 
% 4.42/4.60            (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 4.42/4.60             (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 4.42/4.60            = (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | (v13_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['42'])).
% 4.42/4.60  thf('44', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (((k15_lattice3 @ X1 @ 
% 4.42/4.60            (k6_domain_1 @ (u1_struct_0 @ X1) @ 
% 4.42/4.60             (sk_C_2 @ (k15_lattice3 @ X1 @ X0) @ X1)))
% 4.42/4.60            = (sk_C_2 @ 
% 4.42/4.60               (k15_lattice3 @ X1 @ 
% 4.42/4.60                (k6_domain_1 @ (u1_struct_0 @ X1) @ (k15_lattice3 @ X1 @ X0))) @ 
% 4.42/4.60               X1))
% 4.42/4.60          | (v2_struct_0 @ X1)
% 4.42/4.60          | ~ (l3_lattices @ X1)
% 4.42/4.60          | ~ (v10_lattices @ X1)
% 4.42/4.60          | ~ (v4_lattice3 @ X1)
% 4.42/4.60          | (v2_struct_0 @ X1)
% 4.42/4.60          | ~ (l3_lattices @ X1)
% 4.42/4.60          | ~ (l1_lattices @ X1)
% 4.42/4.60          | (v13_lattices @ X1)
% 4.42/4.60          | ~ (v10_lattices @ X1)
% 4.42/4.60          | ~ (v4_lattice3 @ X1))),
% 4.42/4.60      inference('sup+', [status(thm)], ['36', '43'])).
% 4.42/4.60  thf('45', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         ((v13_lattices @ X1)
% 4.42/4.60          | ~ (l1_lattices @ X1)
% 4.42/4.60          | ~ (v4_lattice3 @ X1)
% 4.42/4.60          | ~ (v10_lattices @ X1)
% 4.42/4.60          | ~ (l3_lattices @ X1)
% 4.42/4.60          | (v2_struct_0 @ X1)
% 4.42/4.60          | ((k15_lattice3 @ X1 @ 
% 4.42/4.60              (k6_domain_1 @ (u1_struct_0 @ X1) @ 
% 4.42/4.60               (sk_C_2 @ (k15_lattice3 @ X1 @ X0) @ X1)))
% 4.42/4.60              = (sk_C_2 @ 
% 4.42/4.60                 (k15_lattice3 @ X1 @ 
% 4.42/4.60                  (k6_domain_1 @ (u1_struct_0 @ X1) @ (k15_lattice3 @ X1 @ X0))) @ 
% 4.42/4.60                 X1)))),
% 4.42/4.60      inference('simplify', [status(thm)], ['44'])).
% 4.42/4.60  thf('46', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (((k15_lattice3 @ X0 @ 
% 4.42/4.60            (k6_domain_1 @ (u1_struct_0 @ X0) @ (k15_lattice3 @ X0 @ X1)))
% 4.42/4.60            = (k15_lattice3 @ X0 @ X1))
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['2'])).
% 4.42/4.60  thf('47', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         ((m1_subset_1 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 4.42/4.60           (u1_struct_0 @ X0))
% 4.42/4.60          | (v13_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['39'])).
% 4.42/4.60  thf('48', plain,
% 4.42/4.60      (![X24 : $i, X25 : $i]:
% 4.42/4.60         (~ (l3_lattices @ X24)
% 4.42/4.60          | (v2_struct_0 @ X24)
% 4.42/4.60          | (m1_subset_1 @ (k15_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 4.42/4.60      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 4.42/4.60  thf(d6_lattices, axiom,
% 4.42/4.60    (![A:$i]:
% 4.42/4.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 4.42/4.60       ( ( v6_lattices @ A ) <=>
% 4.42/4.60         ( ![B:$i]:
% 4.42/4.60           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 4.42/4.60             ( ![C:$i]:
% 4.42/4.60               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.42/4.60                 ( ( k2_lattices @ A @ B @ C ) = ( k2_lattices @ A @ C @ B ) ) ) ) ) ) ) ))).
% 4.42/4.60  thf('49', plain,
% 4.42/4.60      (![X21 : $i, X22 : $i, X23 : $i]:
% 4.42/4.60         (~ (v6_lattices @ X21)
% 4.42/4.60          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X21))
% 4.42/4.60          | ((k2_lattices @ X21 @ X23 @ X22) = (k2_lattices @ X21 @ X22 @ X23))
% 4.42/4.60          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 4.42/4.60          | ~ (l1_lattices @ X21)
% 4.42/4.60          | (v2_struct_0 @ X21))),
% 4.42/4.60      inference('cnf', [status(esa)], [d6_lattices])).
% 4.42/4.60  thf('50', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.42/4.60          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 4.42/4.60              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 4.42/4.60          | ~ (v6_lattices @ X0))),
% 4.42/4.60      inference('sup-', [status(thm)], ['48', '49'])).
% 4.42/4.60  thf('51', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.60         (~ (v6_lattices @ X0)
% 4.42/4.60          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 4.42/4.60              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 4.42/4.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['50'])).
% 4.42/4.60  thf('52', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v13_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ((k2_lattices @ X0 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 4.42/4.60              (k15_lattice3 @ X0 @ X2))
% 4.42/4.60              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 4.42/4.60                 (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 4.42/4.60          | ~ (v6_lattices @ X0))),
% 4.42/4.60      inference('sup-', [status(thm)], ['47', '51'])).
% 4.42/4.60  thf('53', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.60         (~ (v6_lattices @ X0)
% 4.42/4.60          | ((k2_lattices @ X0 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 4.42/4.60              (k15_lattice3 @ X0 @ X2))
% 4.42/4.60              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 4.42/4.60                 (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 4.42/4.60          | (v13_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['52'])).
% 4.42/4.60  thf('54', plain,
% 4.42/4.60      (![X24 : $i, X25 : $i]:
% 4.42/4.60         (~ (l3_lattices @ X24)
% 4.42/4.60          | (v2_struct_0 @ X24)
% 4.42/4.60          | (m1_subset_1 @ (k15_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 4.42/4.60      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 4.42/4.60  thf('55', plain,
% 4.42/4.60      (![X18 : $i, X19 : $i]:
% 4.42/4.60         (((k2_lattices @ X19 @ (sk_C_2 @ X18 @ X19) @ X18) != (X18))
% 4.42/4.60          | ((k2_lattices @ X19 @ X18 @ (sk_C_2 @ X18 @ X19)) != (X18))
% 4.42/4.60          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 4.42/4.60          | (v13_lattices @ X19)
% 4.42/4.60          | ~ (l1_lattices @ X19)
% 4.42/4.60          | (v2_struct_0 @ X19))),
% 4.42/4.60      inference('cnf', [status(esa)], [d13_lattices])).
% 4.42/4.60  thf('56', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v13_lattices @ X0)
% 4.42/4.60          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 4.42/4.60              (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 4.42/4.60              != (k15_lattice3 @ X0 @ X1))
% 4.42/4.60          | ((k2_lattices @ X0 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 4.42/4.60              (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1)))),
% 4.42/4.60      inference('sup-', [status(thm)], ['54', '55'])).
% 4.42/4.60  thf('57', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (((k2_lattices @ X0 @ (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 4.42/4.60            (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1))
% 4.42/4.60          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 4.42/4.60              (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 4.42/4.60              != (k15_lattice3 @ X0 @ X1))
% 4.42/4.60          | (v13_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['56'])).
% 4.42/4.60  thf('58', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 4.42/4.60            (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 4.42/4.60            != (k15_lattice3 @ X0 @ X1))
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v13_lattices @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v13_lattices @ X0)
% 4.42/4.60          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 4.42/4.60              (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 4.42/4.60              != (k15_lattice3 @ X0 @ X1)))),
% 4.42/4.60      inference('sup-', [status(thm)], ['53', '57'])).
% 4.42/4.60  thf('59', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (~ (v6_lattices @ X0)
% 4.42/4.60          | (v13_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 4.42/4.60              (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 4.42/4.60              != (k15_lattice3 @ X0 @ X1)))),
% 4.42/4.60      inference('simplify', [status(thm)], ['58'])).
% 4.42/4.60  thf('60', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (((k2_lattices @ X1 @ (k15_lattice3 @ X1 @ X0) @ 
% 4.42/4.60            (sk_C_2 @ 
% 4.42/4.60             (k15_lattice3 @ X1 @ 
% 4.42/4.60              (k6_domain_1 @ (u1_struct_0 @ X1) @ (k15_lattice3 @ X1 @ X0))) @ 
% 4.42/4.60             X1))
% 4.42/4.60            != (k15_lattice3 @ X1 @ 
% 4.42/4.60                (k6_domain_1 @ (u1_struct_0 @ X1) @ (k15_lattice3 @ X1 @ X0))))
% 4.42/4.60          | (v2_struct_0 @ X1)
% 4.42/4.60          | ~ (l3_lattices @ X1)
% 4.42/4.60          | ~ (v10_lattices @ X1)
% 4.42/4.60          | ~ (v4_lattice3 @ X1)
% 4.42/4.60          | (v2_struct_0 @ X1)
% 4.42/4.60          | ~ (l3_lattices @ X1)
% 4.42/4.60          | ~ (l1_lattices @ X1)
% 4.42/4.60          | (v13_lattices @ X1)
% 4.42/4.60          | ~ (v6_lattices @ X1))),
% 4.42/4.60      inference('sup-', [status(thm)], ['46', '59'])).
% 4.42/4.60  thf('61', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (~ (v6_lattices @ X1)
% 4.42/4.60          | (v13_lattices @ X1)
% 4.42/4.60          | ~ (l1_lattices @ X1)
% 4.42/4.60          | ~ (v4_lattice3 @ X1)
% 4.42/4.60          | ~ (v10_lattices @ X1)
% 4.42/4.60          | ~ (l3_lattices @ X1)
% 4.42/4.60          | (v2_struct_0 @ X1)
% 4.42/4.60          | ((k2_lattices @ X1 @ (k15_lattice3 @ X1 @ X0) @ 
% 4.42/4.60              (sk_C_2 @ 
% 4.42/4.60               (k15_lattice3 @ X1 @ 
% 4.42/4.60                (k6_domain_1 @ (u1_struct_0 @ X1) @ (k15_lattice3 @ X1 @ X0))) @ 
% 4.42/4.60               X1))
% 4.42/4.60              != (k15_lattice3 @ X1 @ 
% 4.42/4.60                  (k6_domain_1 @ (u1_struct_0 @ X1) @ (k15_lattice3 @ X1 @ X0)))))),
% 4.42/4.60      inference('simplify', [status(thm)], ['60'])).
% 4.42/4.60  thf('62', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 4.42/4.60            (k15_lattice3 @ X0 @ 
% 4.42/4.60             (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 4.42/4.60              (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))))
% 4.42/4.60            != (k15_lattice3 @ X0 @ 
% 4.42/4.60                (k6_domain_1 @ (u1_struct_0 @ X0) @ (k15_lattice3 @ X0 @ X1))))
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v13_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v13_lattices @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0))),
% 4.42/4.60      inference('sup-', [status(thm)], ['45', '61'])).
% 4.42/4.60  thf('63', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (~ (v6_lattices @ X0)
% 4.42/4.60          | (v13_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 4.42/4.60              (k15_lattice3 @ X0 @ 
% 4.42/4.60               (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 4.42/4.60                (sk_C_2 @ (k15_lattice3 @ X0 @ X1) @ X0))))
% 4.42/4.60              != (k15_lattice3 @ X0 @ 
% 4.42/4.60                  (k6_domain_1 @ (u1_struct_0 @ X0) @ (k15_lattice3 @ X0 @ X1)))))),
% 4.42/4.60      inference('simplify', [status(thm)], ['62'])).
% 4.42/4.60  thf('64', plain,
% 4.42/4.60      (![X0 : $i]:
% 4.42/4.60         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 4.42/4.60            != (k15_lattice3 @ X0 @ 
% 4.42/4.60                (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 4.42/4.60                 (k15_lattice3 @ X0 @ k1_xboole_0))))
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v9_lattices @ X0)
% 4.42/4.60          | ~ (l2_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v13_lattices @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0))),
% 4.42/4.60      inference('sup-', [status(thm)], ['35', '63'])).
% 4.42/4.60  thf('65', plain,
% 4.42/4.60      (![X0 : $i]:
% 4.42/4.60         ((v13_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (l2_lattices @ X0)
% 4.42/4.60          | ~ (v9_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 4.42/4.60              != (k15_lattice3 @ X0 @ 
% 4.42/4.60                  (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 4.42/4.60                   (k15_lattice3 @ X0 @ k1_xboole_0)))))),
% 4.42/4.60      inference('simplify', [status(thm)], ['64'])).
% 4.42/4.60  thf('66', plain,
% 4.42/4.60      (![X0 : $i]:
% 4.42/4.60         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 4.42/4.60            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v9_lattices @ X0)
% 4.42/4.60          | ~ (l2_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v13_lattices @ X0))),
% 4.42/4.60      inference('sup-', [status(thm)], ['3', '65'])).
% 4.42/4.60  thf('67', plain,
% 4.42/4.60      (![X0 : $i]:
% 4.42/4.60         ((v13_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (l2_lattices @ X0)
% 4.42/4.60          | ~ (v9_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['66'])).
% 4.42/4.60  thf(t50_lattice3, conjecture,
% 4.42/4.60    (![A:$i]:
% 4.42/4.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 4.42/4.60         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 4.42/4.60       ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 4.42/4.60         ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 4.42/4.60         ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ))).
% 4.42/4.60  thf(zf_stmt_0, negated_conjecture,
% 4.42/4.60    (~( ![A:$i]:
% 4.42/4.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 4.42/4.60            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 4.42/4.60          ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 4.42/4.60            ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 4.42/4.60            ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ) )),
% 4.42/4.60    inference('cnf.neg', [status(esa)], [t50_lattice3])).
% 4.42/4.60  thf('68', plain, (~ (v2_struct_0 @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('69', plain,
% 4.42/4.60      ((~ (l3_lattices @ sk_A)
% 4.42/4.60        | ~ (v10_lattices @ sk_A)
% 4.42/4.60        | ~ (v4_lattice3 @ sk_A)
% 4.42/4.60        | ~ (v6_lattices @ sk_A)
% 4.42/4.60        | ~ (v8_lattices @ sk_A)
% 4.42/4.60        | ~ (v9_lattices @ sk_A)
% 4.42/4.60        | ~ (l2_lattices @ sk_A)
% 4.42/4.60        | ~ (l1_lattices @ sk_A)
% 4.42/4.60        | (v13_lattices @ sk_A))),
% 4.42/4.60      inference('sup-', [status(thm)], ['67', '68'])).
% 4.42/4.60  thf('70', plain, ((l3_lattices @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('71', plain, ((v10_lattices @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('72', plain, ((v4_lattice3 @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf(cc1_lattices, axiom,
% 4.42/4.60    (![A:$i]:
% 4.42/4.60     ( ( l3_lattices @ A ) =>
% 4.42/4.60       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 4.42/4.60         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 4.42/4.60           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 4.42/4.60           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 4.42/4.60  thf('73', plain,
% 4.42/4.60      (![X3 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X3)
% 4.42/4.60          | ~ (v10_lattices @ X3)
% 4.42/4.60          | (v6_lattices @ X3)
% 4.42/4.60          | ~ (l3_lattices @ X3))),
% 4.42/4.60      inference('cnf', [status(esa)], [cc1_lattices])).
% 4.42/4.60  thf('74', plain, (~ (v2_struct_0 @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('75', plain,
% 4.42/4.60      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 4.42/4.60      inference('sup-', [status(thm)], ['73', '74'])).
% 4.42/4.60  thf('76', plain, ((l3_lattices @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('77', plain, ((v10_lattices @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('78', plain, ((v6_lattices @ sk_A)),
% 4.42/4.60      inference('demod', [status(thm)], ['75', '76', '77'])).
% 4.42/4.60  thf('79', plain,
% 4.42/4.60      (![X3 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X3)
% 4.42/4.60          | ~ (v10_lattices @ X3)
% 4.42/4.60          | (v8_lattices @ X3)
% 4.42/4.60          | ~ (l3_lattices @ X3))),
% 4.42/4.60      inference('cnf', [status(esa)], [cc1_lattices])).
% 4.42/4.60  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('81', plain,
% 4.42/4.60      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 4.42/4.60      inference('sup-', [status(thm)], ['79', '80'])).
% 4.42/4.60  thf('82', plain, ((l3_lattices @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('83', plain, ((v10_lattices @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('84', plain, ((v8_lattices @ sk_A)),
% 4.42/4.60      inference('demod', [status(thm)], ['81', '82', '83'])).
% 4.42/4.60  thf('85', plain,
% 4.42/4.60      (![X3 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X3)
% 4.42/4.60          | ~ (v10_lattices @ X3)
% 4.42/4.60          | (v9_lattices @ X3)
% 4.42/4.60          | ~ (l3_lattices @ X3))),
% 4.42/4.60      inference('cnf', [status(esa)], [cc1_lattices])).
% 4.42/4.60  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('87', plain,
% 4.42/4.60      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 4.42/4.60      inference('sup-', [status(thm)], ['85', '86'])).
% 4.42/4.60  thf('88', plain, ((l3_lattices @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('89', plain, ((v10_lattices @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('90', plain, ((v9_lattices @ sk_A)),
% 4.42/4.60      inference('demod', [status(thm)], ['87', '88', '89'])).
% 4.42/4.60  thf('91', plain, ((l3_lattices @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf(dt_l3_lattices, axiom,
% 4.42/4.60    (![A:$i]:
% 4.42/4.60     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 4.42/4.60  thf('92', plain,
% 4.42/4.60      (![X14 : $i]: ((l2_lattices @ X14) | ~ (l3_lattices @ X14))),
% 4.42/4.60      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 4.42/4.60  thf('93', plain, ((l2_lattices @ sk_A)),
% 4.42/4.60      inference('sup-', [status(thm)], ['91', '92'])).
% 4.42/4.60  thf('94', plain, ((l3_lattices @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('95', plain,
% 4.42/4.60      (![X14 : $i]: ((l1_lattices @ X14) | ~ (l3_lattices @ X14))),
% 4.42/4.60      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 4.42/4.60  thf('96', plain, ((l1_lattices @ sk_A)),
% 4.42/4.60      inference('sup-', [status(thm)], ['94', '95'])).
% 4.42/4.60  thf('97', plain, ((v13_lattices @ sk_A)),
% 4.42/4.60      inference('demod', [status(thm)],
% 4.42/4.60                ['69', '70', '71', '72', '78', '84', '90', '93', '96'])).
% 4.42/4.60  thf('98', plain,
% 4.42/4.60      (![X24 : $i, X25 : $i]:
% 4.42/4.60         (~ (l3_lattices @ X24)
% 4.42/4.60          | (v2_struct_0 @ X24)
% 4.42/4.60          | (m1_subset_1 @ (k15_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 4.42/4.60      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 4.42/4.60  thf(dt_k5_lattices, axiom,
% 4.42/4.60    (![A:$i]:
% 4.42/4.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 4.42/4.60       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 4.42/4.60  thf('99', plain,
% 4.42/4.60      (![X13 : $i]:
% 4.42/4.60         ((m1_subset_1 @ (k5_lattices @ X13) @ (u1_struct_0 @ X13))
% 4.42/4.60          | ~ (l1_lattices @ X13)
% 4.42/4.60          | (v2_struct_0 @ X13))),
% 4.42/4.60      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 4.42/4.60  thf(d16_lattices, axiom,
% 4.42/4.60    (![A:$i]:
% 4.42/4.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 4.42/4.60       ( ( v13_lattices @ A ) =>
% 4.42/4.60         ( ![B:$i]:
% 4.42/4.60           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 4.42/4.60             ( ( ( B ) = ( k5_lattices @ A ) ) <=>
% 4.42/4.60               ( ![C:$i]:
% 4.42/4.60                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.42/4.60                   ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 4.42/4.60                     ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 4.42/4.60  thf('100', plain,
% 4.42/4.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 4.42/4.60         (~ (v13_lattices @ X4)
% 4.42/4.60          | ~ (m1_subset_1 @ X5 @ (u1_struct_0 @ X4))
% 4.42/4.60          | ((X5) != (k5_lattices @ X4))
% 4.42/4.60          | ((k2_lattices @ X4 @ X6 @ X5) = (X5))
% 4.42/4.60          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 4.42/4.60          | ~ (l1_lattices @ X4)
% 4.42/4.60          | (v2_struct_0 @ X4))),
% 4.42/4.60      inference('cnf', [status(esa)], [d16_lattices])).
% 4.42/4.60  thf('101', plain,
% 4.42/4.60      (![X4 : $i, X6 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X4)
% 4.42/4.60          | ~ (l1_lattices @ X4)
% 4.42/4.60          | ~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X4))
% 4.42/4.60          | ((k2_lattices @ X4 @ X6 @ (k5_lattices @ X4)) = (k5_lattices @ X4))
% 4.42/4.60          | ~ (m1_subset_1 @ (k5_lattices @ X4) @ (u1_struct_0 @ X4))
% 4.42/4.60          | ~ (v13_lattices @ X4))),
% 4.42/4.60      inference('simplify', [status(thm)], ['100'])).
% 4.42/4.60  thf('102', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (v13_lattices @ X0)
% 4.42/4.60          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 4.42/4.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('sup-', [status(thm)], ['99', '101'])).
% 4.42/4.60  thf('103', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 4.42/4.60          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 4.42/4.60          | ~ (v13_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['102'])).
% 4.42/4.60  thf('104', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (v13_lattices @ X0)
% 4.42/4.60          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 4.42/4.60              = (k5_lattices @ X0)))),
% 4.42/4.60      inference('sup-', [status(thm)], ['98', '103'])).
% 4.42/4.60  thf('105', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 4.42/4.60            = (k5_lattices @ X0))
% 4.42/4.60          | ~ (v13_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['104'])).
% 4.42/4.60  thf('106', plain,
% 4.42/4.60      (![X13 : $i]:
% 4.42/4.60         ((m1_subset_1 @ (k5_lattices @ X13) @ (u1_struct_0 @ X13))
% 4.42/4.60          | ~ (l1_lattices @ X13)
% 4.42/4.60          | (v2_struct_0 @ X13))),
% 4.42/4.60      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 4.42/4.60  thf('107', plain,
% 4.42/4.60      (![X13 : $i]:
% 4.42/4.60         ((m1_subset_1 @ (k5_lattices @ X13) @ (u1_struct_0 @ X13))
% 4.42/4.60          | ~ (l1_lattices @ X13)
% 4.42/4.60          | (v2_struct_0 @ X13))),
% 4.42/4.60      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 4.42/4.60  thf('108', plain,
% 4.42/4.60      (![X26 : $i, X27 : $i]:
% 4.42/4.60         (~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X27))
% 4.42/4.60          | ((k15_lattice3 @ X27 @ (k6_domain_1 @ (u1_struct_0 @ X27) @ X26))
% 4.42/4.60              = (X26))
% 4.42/4.60          | ~ (l3_lattices @ X27)
% 4.42/4.60          | ~ (v4_lattice3 @ X27)
% 4.42/4.60          | ~ (v10_lattices @ X27)
% 4.42/4.60          | (v2_struct_0 @ X27))),
% 4.42/4.60      inference('cnf', [status(esa)], [t43_lattice3])).
% 4.42/4.60  thf('109', plain,
% 4.42/4.60      (![X0 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ((k15_lattice3 @ X0 @ 
% 4.42/4.60              (k6_domain_1 @ (u1_struct_0 @ X0) @ (k5_lattices @ X0)))
% 4.42/4.60              = (k5_lattices @ X0)))),
% 4.42/4.60      inference('sup-', [status(thm)], ['107', '108'])).
% 4.42/4.60  thf('110', plain,
% 4.42/4.60      (![X0 : $i]:
% 4.42/4.60         (((k15_lattice3 @ X0 @ 
% 4.42/4.60            (k6_domain_1 @ (u1_struct_0 @ X0) @ (k5_lattices @ X0)))
% 4.42/4.60            = (k5_lattices @ X0))
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['109'])).
% 4.42/4.60  thf('111', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         ((r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.42/4.60           (k15_lattice3 @ X0 @ X1))
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('sup-', [status(thm)], ['5', '8'])).
% 4.42/4.60  thf('112', plain,
% 4.42/4.60      (![X0 : $i]:
% 4.42/4.60         ((r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.42/4.60           (k5_lattices @ X0))
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0))),
% 4.42/4.60      inference('sup+', [status(thm)], ['110', '111'])).
% 4.42/4.60  thf('113', plain,
% 4.42/4.60      (![X0 : $i]:
% 4.42/4.60         (~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.42/4.60             (k5_lattices @ X0)))),
% 4.42/4.60      inference('simplify', [status(thm)], ['112'])).
% 4.42/4.60  thf('114', plain,
% 4.42/4.60      (![X13 : $i]:
% 4.42/4.60         ((m1_subset_1 @ (k5_lattices @ X13) @ (u1_struct_0 @ X13))
% 4.42/4.60          | ~ (l1_lattices @ X13)
% 4.42/4.60          | (v2_struct_0 @ X13))),
% 4.42/4.60      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 4.42/4.60  thf('115', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.60         (~ (v9_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.42/4.60          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 4.42/4.60          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['13'])).
% 4.42/4.60  thf('116', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 4.42/4.60          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v9_lattices @ X0))),
% 4.42/4.60      inference('sup-', [status(thm)], ['114', '115'])).
% 4.42/4.60  thf('117', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (~ (v9_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 4.42/4.60          | ~ (r3_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['116'])).
% 4.42/4.60  thf('118', plain,
% 4.42/4.60      (![X0 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.42/4.60             (k5_lattices @ X0))
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v9_lattices @ X0))),
% 4.42/4.60      inference('sup-', [status(thm)], ['113', '117'])).
% 4.42/4.60  thf('119', plain,
% 4.42/4.60      (![X0 : $i]:
% 4.42/4.60         (~ (v9_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.42/4.60             (k5_lattices @ X0))
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['118'])).
% 4.42/4.60  thf('120', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.42/4.60         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 4.42/4.60          | ((k1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2) = (X2))
% 4.42/4.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.42/4.60          | ~ (l2_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['21'])).
% 4.42/4.60  thf('121', plain,
% 4.42/4.60      (![X0 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v9_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (l2_lattices @ X0)
% 4.42/4.60          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 4.42/4.60          | ((k1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.42/4.60              (k5_lattices @ X0)) = (k5_lattices @ X0)))),
% 4.42/4.60      inference('sup-', [status(thm)], ['119', '120'])).
% 4.42/4.60  thf('122', plain,
% 4.42/4.60      (![X0 : $i]:
% 4.42/4.60         (((k1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.42/4.60            (k5_lattices @ X0)) = (k5_lattices @ X0))
% 4.42/4.60          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 4.42/4.60          | ~ (l2_lattices @ X0)
% 4.42/4.60          | ~ (v9_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['121'])).
% 4.42/4.60  thf('123', plain,
% 4.42/4.60      (![X0 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v9_lattices @ X0)
% 4.42/4.60          | ~ (l2_lattices @ X0)
% 4.42/4.60          | ((k1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.42/4.60              (k5_lattices @ X0)) = (k5_lattices @ X0)))),
% 4.42/4.60      inference('sup-', [status(thm)], ['106', '122'])).
% 4.42/4.60  thf('124', plain,
% 4.42/4.60      (![X0 : $i]:
% 4.42/4.60         (((k1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.42/4.60            (k5_lattices @ X0)) = (k5_lattices @ X0))
% 4.42/4.60          | ~ (l2_lattices @ X0)
% 4.42/4.60          | ~ (v9_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['123'])).
% 4.42/4.60  thf('125', plain,
% 4.42/4.60      (![X24 : $i, X25 : $i]:
% 4.42/4.60         (~ (l3_lattices @ X24)
% 4.42/4.60          | (v2_struct_0 @ X24)
% 4.42/4.60          | (m1_subset_1 @ (k15_lattice3 @ X24 @ X25) @ (u1_struct_0 @ X24)))),
% 4.42/4.60      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 4.42/4.60  thf('126', plain,
% 4.42/4.60      (![X13 : $i]:
% 4.42/4.60         ((m1_subset_1 @ (k5_lattices @ X13) @ (u1_struct_0 @ X13))
% 4.42/4.60          | ~ (l1_lattices @ X13)
% 4.42/4.60          | (v2_struct_0 @ X13))),
% 4.42/4.60      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 4.42/4.60  thf('127', plain,
% 4.42/4.60      (![X10 : $i, X11 : $i, X12 : $i]:
% 4.42/4.60         (~ (v9_lattices @ X10)
% 4.42/4.60          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 4.42/4.60          | ((k2_lattices @ X10 @ X12 @ (k1_lattices @ X10 @ X12 @ X11))
% 4.42/4.60              = (X12))
% 4.42/4.60          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X10))
% 4.42/4.60          | ~ (l3_lattices @ X10)
% 4.42/4.60          | (v2_struct_0 @ X10))),
% 4.42/4.60      inference('cnf', [status(esa)], [d9_lattices])).
% 4.42/4.60  thf('128', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 4.42/4.60          | ((k2_lattices @ X0 @ X1 @ 
% 4.42/4.60              (k1_lattices @ X0 @ X1 @ (k5_lattices @ X0))) = (X1))
% 4.42/4.60          | ~ (v9_lattices @ X0))),
% 4.42/4.60      inference('sup-', [status(thm)], ['126', '127'])).
% 4.42/4.60  thf('129', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (~ (v9_lattices @ X0)
% 4.42/4.60          | ((k2_lattices @ X0 @ X1 @ 
% 4.42/4.60              (k1_lattices @ X0 @ X1 @ (k5_lattices @ X0))) = (X1))
% 4.42/4.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['128'])).
% 4.42/4.60  thf('130', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         ((v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 4.42/4.60              (k1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0)))
% 4.42/4.60              = (k15_lattice3 @ X0 @ X1))
% 4.42/4.60          | ~ (v9_lattices @ X0))),
% 4.42/4.60      inference('sup-', [status(thm)], ['125', '129'])).
% 4.42/4.60  thf('131', plain,
% 4.42/4.60      (![X0 : $i, X1 : $i]:
% 4.42/4.60         (~ (v9_lattices @ X0)
% 4.42/4.60          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 4.42/4.60              (k1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0)))
% 4.42/4.60              = (k15_lattice3 @ X0 @ X1))
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0))),
% 4.42/4.60      inference('simplify', [status(thm)], ['130'])).
% 4.42/4.60  thf('132', plain,
% 4.42/4.60      (![X0 : $i]:
% 4.42/4.60         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.42/4.60            (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v9_lattices @ X0)
% 4.42/4.60          | ~ (l2_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (v9_lattices @ X0))),
% 4.42/4.60      inference('sup+', [status(thm)], ['124', '131'])).
% 4.42/4.60  thf('133', plain,
% 4.42/4.60      (![X0 : $i]:
% 4.42/4.60         (~ (l2_lattices @ X0)
% 4.42/4.60          | ~ (v9_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 4.42/4.60              (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 4.42/4.60      inference('simplify', [status(thm)], ['132'])).
% 4.42/4.60  thf('134', plain,
% 4.42/4.60      (![X0 : $i]:
% 4.42/4.60         (((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (v13_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v9_lattices @ X0)
% 4.42/4.60          | ~ (l2_lattices @ X0))),
% 4.42/4.60      inference('sup+', [status(thm)], ['105', '133'])).
% 4.42/4.60  thf('135', plain,
% 4.42/4.60      (![X0 : $i]:
% 4.42/4.60         (~ (l2_lattices @ X0)
% 4.42/4.60          | ~ (v9_lattices @ X0)
% 4.42/4.60          | ~ (v8_lattices @ X0)
% 4.42/4.60          | ~ (v6_lattices @ X0)
% 4.42/4.60          | ~ (v4_lattice3 @ X0)
% 4.42/4.60          | ~ (v10_lattices @ X0)
% 4.42/4.60          | ~ (v13_lattices @ X0)
% 4.42/4.60          | ~ (l1_lattices @ X0)
% 4.42/4.60          | ~ (l3_lattices @ X0)
% 4.42/4.60          | (v2_struct_0 @ X0)
% 4.42/4.60          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 4.42/4.60      inference('simplify', [status(thm)], ['134'])).
% 4.42/4.60  thf('136', plain,
% 4.42/4.60      (((v2_struct_0 @ sk_A)
% 4.42/4.60        | ~ (v10_lattices @ sk_A)
% 4.42/4.60        | ~ (v13_lattices @ sk_A)
% 4.42/4.60        | ~ (l3_lattices @ sk_A)
% 4.42/4.60        | ((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('137', plain,
% 4.42/4.60      ((((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))
% 4.42/4.60         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 4.42/4.60      inference('split', [status(esa)], ['136'])).
% 4.42/4.60  thf('138', plain,
% 4.42/4.60      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 4.42/4.60         | (v2_struct_0 @ sk_A)
% 4.42/4.60         | ~ (l3_lattices @ sk_A)
% 4.42/4.60         | ~ (l1_lattices @ sk_A)
% 4.42/4.60         | ~ (v13_lattices @ sk_A)
% 4.42/4.60         | ~ (v10_lattices @ sk_A)
% 4.42/4.60         | ~ (v4_lattice3 @ sk_A)
% 4.42/4.60         | ~ (v6_lattices @ sk_A)
% 4.42/4.60         | ~ (v8_lattices @ sk_A)
% 4.42/4.60         | ~ (v9_lattices @ sk_A)
% 4.42/4.60         | ~ (l2_lattices @ sk_A)))
% 4.42/4.60         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 4.42/4.60      inference('sup-', [status(thm)], ['135', '137'])).
% 4.42/4.60  thf('139', plain, ((l3_lattices @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('140', plain, ((l1_lattices @ sk_A)),
% 4.42/4.60      inference('sup-', [status(thm)], ['94', '95'])).
% 4.42/4.60  thf('141', plain, ((v10_lattices @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('142', plain, ((v4_lattice3 @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('143', plain, ((v6_lattices @ sk_A)),
% 4.42/4.60      inference('demod', [status(thm)], ['75', '76', '77'])).
% 4.42/4.60  thf('144', plain, ((v8_lattices @ sk_A)),
% 4.42/4.60      inference('demod', [status(thm)], ['81', '82', '83'])).
% 4.42/4.60  thf('145', plain, ((v9_lattices @ sk_A)),
% 4.42/4.60      inference('demod', [status(thm)], ['87', '88', '89'])).
% 4.42/4.60  thf('146', plain, ((l2_lattices @ sk_A)),
% 4.42/4.60      inference('sup-', [status(thm)], ['91', '92'])).
% 4.42/4.60  thf('147', plain,
% 4.42/4.60      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 4.42/4.60         | (v2_struct_0 @ sk_A)
% 4.42/4.60         | ~ (v13_lattices @ sk_A)))
% 4.42/4.60         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 4.42/4.60      inference('demod', [status(thm)],
% 4.42/4.60                ['138', '139', '140', '141', '142', '143', '144', '145', '146'])).
% 4.42/4.60  thf('148', plain,
% 4.42/4.60      (((~ (v13_lattices @ sk_A) | (v2_struct_0 @ sk_A)))
% 4.42/4.60         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 4.42/4.60      inference('simplify', [status(thm)], ['147'])).
% 4.42/4.60  thf('149', plain, (~ (v2_struct_0 @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('150', plain,
% 4.42/4.60      ((~ (v13_lattices @ sk_A))
% 4.42/4.60         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 4.42/4.60      inference('clc', [status(thm)], ['148', '149'])).
% 4.42/4.60  thf('151', plain,
% 4.42/4.60      (($false)
% 4.42/4.60         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 4.42/4.60      inference('sup-', [status(thm)], ['97', '150'])).
% 4.42/4.60  thf('152', plain, (((v2_struct_0 @ sk_A)) <= (((v2_struct_0 @ sk_A)))),
% 4.42/4.60      inference('split', [status(esa)], ['136'])).
% 4.42/4.60  thf('153', plain, (~ (v2_struct_0 @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('154', plain, (~ ((v2_struct_0 @ sk_A))),
% 4.42/4.60      inference('sup-', [status(thm)], ['152', '153'])).
% 4.42/4.60  thf('155', plain, ((l3_lattices @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('156', plain, ((~ (l3_lattices @ sk_A)) <= (~ ((l3_lattices @ sk_A)))),
% 4.42/4.60      inference('split', [status(esa)], ['136'])).
% 4.42/4.60  thf('157', plain, (((l3_lattices @ sk_A))),
% 4.42/4.60      inference('sup-', [status(thm)], ['155', '156'])).
% 4.42/4.60  thf('158', plain, ((v10_lattices @ sk_A)),
% 4.42/4.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.42/4.60  thf('159', plain, ((~ (v10_lattices @ sk_A)) <= (~ ((v10_lattices @ sk_A)))),
% 4.42/4.60      inference('split', [status(esa)], ['136'])).
% 4.42/4.60  thf('160', plain, (((v10_lattices @ sk_A))),
% 4.42/4.60      inference('sup-', [status(thm)], ['158', '159'])).
% 4.42/4.60  thf('161', plain, ((v13_lattices @ sk_A)),
% 4.42/4.60      inference('demod', [status(thm)],
% 4.42/4.60                ['69', '70', '71', '72', '78', '84', '90', '93', '96'])).
% 4.42/4.60  thf('162', plain, ((~ (v13_lattices @ sk_A)) <= (~ ((v13_lattices @ sk_A)))),
% 4.42/4.60      inference('split', [status(esa)], ['136'])).
% 4.42/4.60  thf('163', plain, (((v13_lattices @ sk_A))),
% 4.42/4.60      inference('sup-', [status(thm)], ['161', '162'])).
% 4.42/4.60  thf('164', plain,
% 4.42/4.60      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))) | 
% 4.42/4.60       ~ ((v13_lattices @ sk_A)) | ~ ((v10_lattices @ sk_A)) | 
% 4.42/4.60       ~ ((l3_lattices @ sk_A)) | ((v2_struct_0 @ sk_A))),
% 4.42/4.60      inference('split', [status(esa)], ['136'])).
% 4.42/4.60  thf('165', plain,
% 4.42/4.60      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 4.42/4.60      inference('sat_resolution*', [status(thm)],
% 4.42/4.60                ['154', '157', '160', '163', '164'])).
% 4.42/4.60  thf('166', plain, ($false),
% 4.42/4.60      inference('simpl_trail', [status(thm)], ['151', '165'])).
% 4.42/4.60  
% 4.42/4.60  % SZS output end Refutation
% 4.42/4.60  
% 4.42/4.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
