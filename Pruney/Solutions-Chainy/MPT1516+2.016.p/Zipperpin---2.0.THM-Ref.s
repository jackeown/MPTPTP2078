%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LHsBYnWRAS

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:36 EST 2020

% Result     : Theorem 46.47s
% Output     : Refutation 46.47s
% Verified   : 
% Statistics : Number of formulae       :  221 ( 671 expanded)
%              Number of leaves         :   53 ( 213 expanded)
%              Depth                    :   26
%              Number of atoms          : 3075 (10535 expanded)
%              Number of equality atoms :   99 ( 330 expanded)
%              Maximal formula depth    :   22 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(a_2_5_lattice3_type,type,(
    a_2_5_lattice3: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v13_lattices_type,type,(
    v13_lattices: $i > $o )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(a_2_6_lattice3_type,type,(
    a_2_6_lattice3: $i > $i > $i )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_lattices_type,type,(
    k5_lattices: $i > $i )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X46: $i,X48: $i] :
      ( ( ( k15_lattice3 @ X46 @ X48 )
        = ( k15_lattice3 @ X46 @ ( a_2_5_lattice3 @ X46 @ X48 ) ) )
      | ~ ( l3_lattices @ X46 )
      | ~ ( v4_lattice3 @ X46 )
      | ~ ( v10_lattices @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t47_lattice3])).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l3_lattices @ X34 )
      | ( v2_struct_0 @ X34 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X34 @ X35 ) @ ( u1_struct_0 @ X34 ) ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( sk_C_3 @ X19 @ X20 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( v13_lattices @ X20 )
      | ~ ( l1_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d13_lattices])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( m1_subset_1 @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( u1_struct_0 @ X0 ) )
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
    ! [X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( u1_struct_0 @ X42 ) )
      | ( ( k15_lattice3 @ X42 @ ( k6_domain_1 @ ( u1_struct_0 @ X42 ) @ X41 ) )
        = X41 )
      | ~ ( l3_lattices @ X42 )
      | ~ ( v4_lattice3 @ X42 )
      | ~ ( v10_lattices @ X42 )
      | ( v2_struct_0 @ X42 ) ) ),
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
      | ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) )
        = ( sk_C_3 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) )
        = ( sk_C_3 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l3_lattices @ X34 )
      | ( v2_struct_0 @ X34 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X34 @ X35 ) @ ( u1_struct_0 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('9',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l3_lattices @ X34 )
      | ( v2_struct_0 @ X34 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X34 @ X35 ) @ ( u1_struct_0 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

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

thf('10',plain,(
    ! [X22: $i,X23: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( r2_hidden @ ( sk_D @ X26 @ X22 @ X23 ) @ X26 )
      | ( r4_lattice3 @ X23 @ X22 @ X26 )
      | ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ X2 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('13',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('18',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X9: $i] :
      ( r1_xboole_0 @ X9 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('23',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('25',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l3_lattices @ X34 )
      | ( v2_struct_0 @ X34 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X34 @ X35 ) @ ( u1_struct_0 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('26',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l3_lattices @ X34 )
      | ( v2_struct_0 @ X34 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X34 @ X35 ) @ ( u1_struct_0 @ X34 ) ) ) ),
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

thf('27',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v2_struct_0 @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ~ ( v4_lattice3 @ X27 )
      | ~ ( l3_lattices @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( u1_struct_0 @ X27 ) )
      | ( X28
       != ( k15_lattice3 @ X27 @ X29 ) )
      | ~ ( r4_lattice3 @ X27 @ X30 @ X29 )
      | ( r1_lattices @ X27 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X27 ) )
      | ~ ( l3_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('28',plain,(
    ! [X27: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( u1_struct_0 @ X27 ) )
      | ( r1_lattices @ X27 @ ( k15_lattice3 @ X27 @ X29 ) @ X30 )
      | ~ ( r4_lattice3 @ X27 @ X30 @ X29 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X27 @ X29 ) @ ( u1_struct_0 @ X27 ) )
      | ~ ( l3_lattices @ X27 )
      | ~ ( v4_lattice3 @ X27 )
      | ~ ( v10_lattices @ X27 )
      | ( v2_struct_0 @ X27 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
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
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l3_lattices @ X34 )
      | ( v2_struct_0 @ X34 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X34 @ X35 ) @ ( u1_struct_0 @ X34 ) ) ) ),
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

thf('36',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X17 ) )
      | ~ ( r1_lattices @ X17 @ X16 @ X18 )
      | ( ( k2_lattices @ X17 @ X16 @ X18 )
        = X16 )
      | ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l3_lattices @ X17 )
      | ~ ( v9_lattices @ X17 )
      | ~ ( v8_lattices @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('37',plain,(
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
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v8_lattices @ X1 )
      | ~ ( v9_lattices @ X1 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ( ( k2_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) )
        = ( k15_lattice3 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['34','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X1 @ ( k15_lattice3 @ X1 @ k1_xboole_0 ) @ ( k15_lattice3 @ X1 @ X0 ) )
        = ( k15_lattice3 @ X1 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X1 @ X0 ) @ ( u1_struct_0 @ X1 ) )
      | ~ ( v9_lattices @ X1 )
      | ~ ( v8_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['8','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l3_lattices @ X34 )
      | ( v2_struct_0 @ X34 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X34 @ X35 ) @ ( u1_struct_0 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('44',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l3_lattices @ X34 )
      | ( v2_struct_0 @ X34 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X34 @ X35 ) @ ( u1_struct_0 @ X34 ) ) ) ),
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

thf('45',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v6_lattices @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( u1_struct_0 @ X31 ) )
      | ( ( k2_lattices @ X31 @ X33 @ X32 )
        = ( k2_lattices @ X31 @ X32 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( u1_struct_0 @ X31 ) )
      | ~ ( l1_lattices @ X31 )
      | ( v2_struct_0 @ X31 ) ) ),
    inference(cnf,[status(esa)],[d6_lattices])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ X2 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) ) )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ X2 ) )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X2 ) @ ( k15_lattice3 @ X0 @ X1 ) ) )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
        = ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
        = ( k2_lattices @ X0 @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) )
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
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
        = ( k2_lattices @ X0 @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k15_lattice3 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) ) )
        = ( sk_C_3 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
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
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
        = ( k15_lattice3 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X46: $i,X48: $i] :
      ( ( ( k15_lattice3 @ X46 @ X48 )
        = ( k15_lattice3 @ X46 @ ( a_2_5_lattice3 @ X46 @ X48 ) ) )
      | ~ ( l3_lattices @ X46 )
      | ~ ( v4_lattice3 @ X46 )
      | ~ ( v10_lattices @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t47_lattice3])).

thf('59',plain,(
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

thf('60',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( l3_lattices @ X36 )
      | ~ ( v4_lattice3 @ X36 )
      | ~ ( v10_lattices @ X36 )
      | ( v2_struct_0 @ X36 )
      | ( r2_hidden @ ( sk_E @ X37 @ X36 @ X38 ) @ X37 )
      | ~ ( r2_hidden @ X38 @ ( a_2_5_lattice3 @ X36 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_5_lattice3])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( a_2_5_lattice3 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E @ X0 @ X1 @ ( sk_C @ X2 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) ) @ X0 )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_tarski @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( a_2_5_lattice3 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X46: $i,X48: $i] :
      ( ( ( k15_lattice3 @ X46 @ X48 )
        = ( k15_lattice3 @ X46 @ ( a_2_5_lattice3 @ X46 @ X48 ) ) )
      | ~ ( l3_lattices @ X46 )
      | ~ ( v4_lattice3 @ X46 )
      | ~ ( v10_lattices @ X46 )
      | ( v2_struct_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t47_lattice3])).

thf('67',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l3_lattices @ X34 )
      | ( v2_struct_0 @ X34 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X34 @ X35 ) @ ( u1_struct_0 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('68',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_lattices @ X20 @ ( sk_C_3 @ X19 @ X20 ) @ X19 )
       != X19 )
      | ( ( k2_lattices @ X20 @ X19 @ ( sk_C_3 @ X19 @ X20 ) )
       != X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( v13_lattices @ X20 )
      | ~ ( l1_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d13_lattices])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( ( k2_lattices @ X0 @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
       != ( k15_lattice3 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) @ ( k15_lattice3 @ X0 @ X1 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ X1 ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ X1 ) )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X1 @ ( sk_C_3 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) )
       != ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) )
      | ( v2_struct_0 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( l1_lattices @ X1 )
      | ( v13_lattices @ X1 )
      | ( ( k2_lattices @ X1 @ ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) @ ( sk_C_3 @ ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) @ X1 ) )
       != ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X1 @ ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) @ ( sk_C_3 @ ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) @ X1 ) )
       != ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) )
      | ( v13_lattices @ X1 )
      | ~ ( l1_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 )
      | ( ( k2_lattices @ X1 @ ( sk_C_3 @ ( k15_lattice3 @ X1 @ X0 ) @ X1 ) @ ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) )
       != ( k15_lattice3 @ X1 @ ( a_2_5_lattice3 @ X1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_lattices @ X0 @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) @ X0 ) )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_lattices @ X0 @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ X0 @ ( sk_C_3 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ X0 ) @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v6_lattices @ X0 )
      | ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k15_lattice3 @ X0 @ k1_xboole_0 )
       != ( k15_lattice3 @ X0 @ ( a_2_5_lattice3 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
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
      | ~ ( v8_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v6_lattices @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v6_lattices @ X0 )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['81'])).

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

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ~ ( v10_lattices @ sk_A )
    | ~ ( v4_lattice3 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( l1_lattices @ sk_A )
    | ( v13_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( v6_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('89',plain,(
    ! [X15: $i] :
      ( ( l1_lattices @ X15 )
      | ~ ( l3_lattices @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('90',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['88','89'])).

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

thf('91',plain,(
    ! [X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v8_lattices @ X10 )
      | ~ ( l3_lattices @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v9_lattices @ X10 )
      | ~ ( l3_lattices @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,(
    ! [X10: $i] :
      ( ( v2_struct_0 @ X10 )
      | ~ ( v10_lattices @ X10 )
      | ( v6_lattices @ X10 )
      | ~ ( l3_lattices @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('104',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['84','85','86','87','90','96','102','108'])).

thf('110',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( l3_lattices @ X34 )
      | ( v2_struct_0 @ X34 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X34 @ X35 ) @ ( u1_struct_0 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(dt_k5_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_lattices @ A ) )
     => ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ) )).

thf('111',plain,(
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

thf('112',plain,(
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

thf('113',plain,(
    ! [X11: $i,X13: $i] :
      ( ( v2_struct_0 @ X11 )
      | ~ ( l1_lattices @ X11 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( ( k2_lattices @ X11 @ X13 @ ( k5_lattices @ X11 ) )
        = ( k5_lattices @ X11 ) )
      | ~ ( m1_subset_1 @ ( k5_lattices @ X11 ) @ ( u1_struct_0 @ X11 ) )
      | ~ ( v13_lattices @ X11 ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['111','113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_lattices @ X0 @ X1 @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( v13_lattices @ X0 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['110','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
        = ( k5_lattices @ X0 ) )
      | ~ ( v13_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('119',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('120',plain,(
    ! [X22: $i,X23: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ( r2_hidden @ ( sk_D @ X26 @ X22 @ X23 ) @ X26 )
      | ( r4_lattice3 @ X23 @ X22 @ X26 )
      | ~ ( l3_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k5_lattices @ X0 ) @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ ( k5_lattices @ X0 ) @ X0 ) @ X1 )
      | ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X14: $i] :
      ( ( m1_subset_1 @ ( k5_lattices @ X14 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_lattices @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_lattices])).

thf('126',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('127',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ ( k5_lattices @ X0 ) )
      | ~ ( r4_lattice3 @ X0 @ ( k5_lattices @ X0 ) @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,(
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
    inference('sup-',[status(thm)],['124','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ k1_xboole_0 ) @ ( k5_lattices @ X0 ) )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_lattices @ X0 )
      | ~ ( l3_lattices @ X0 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ( ( k2_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
        = ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( v9_lattices @ X0 )
      | ~ ( v8_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('132',plain,(
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
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
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
    inference(simplify,[status(thm)],['132'])).

thf('134',plain,(
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
    inference('sup-',[status(thm)],['118','133'])).

thf('135',plain,(
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
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,(
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
    inference('sup+',[status(thm)],['117','135'])).

thf('137',plain,(
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
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ~ ( v13_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(split,[status(esa)],['138'])).

thf('140',plain,
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
    inference('sup-',[status(thm)],['137','139'])).

thf('141',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['88','89'])).

thf('143',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('146',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('147',plain,
    ( ( ( ( k5_lattices @ sk_A )
       != ( k5_lattices @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v13_lattices @ sk_A ) )
   <= ( ( k5_lattices @ sk_A )
     != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['140','141','142','143','144','145','146'])).

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
    inference('sup-',[status(thm)],['109','150'])).

thf('152',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( v2_struct_0 @ sk_A ) ),
    inference(split,[status(esa)],['138'])).

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
    inference(split,[status(esa)],['138'])).

thf('157',plain,(
    l3_lattices @ sk_A ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ~ ( v10_lattices @ sk_A )
   <= ~ ( v10_lattices @ sk_A ) ),
    inference(split,[status(esa)],['138'])).

thf('160',plain,(
    v10_lattices @ sk_A ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,(
    v13_lattices @ sk_A ),
    inference(demod,[status(thm)],['84','85','86','87','90','96','102','108'])).

thf('162',plain,
    ( ~ ( v13_lattices @ sk_A )
   <= ~ ( v13_lattices @ sk_A ) ),
    inference(split,[status(esa)],['138'])).

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
    inference(split,[status(esa)],['138'])).

thf('165',plain,(
    ( k5_lattices @ sk_A )
 != ( k15_lattice3 @ sk_A @ k1_xboole_0 ) ),
    inference('sat_resolution*',[status(thm)],['154','157','160','163','164'])).

thf('166',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['151','165'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LHsBYnWRAS
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:52:14 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 46.47/46.67  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 46.47/46.67  % Solved by: fo/fo7.sh
% 46.47/46.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 46.47/46.67  % done 12544 iterations in 46.202s
% 46.47/46.67  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 46.47/46.67  % SZS output start Refutation
% 46.47/46.67  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 46.47/46.67  thf(a_2_5_lattice3_type, type, a_2_5_lattice3: $i > $i > $i).
% 46.47/46.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 46.47/46.67  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 46.47/46.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 46.47/46.67  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 46.47/46.67  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 46.47/46.67  thf(v13_lattices_type, type, v13_lattices: $i > $o).
% 46.47/46.67  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 46.47/46.67  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 46.47/46.67  thf(a_2_6_lattice3_type, type, a_2_6_lattice3: $i > $i > $i).
% 46.47/46.67  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 46.47/46.67  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 46.47/46.67  thf(r3_lattices_type, type, r3_lattices: $i > $i > $i > $o).
% 46.47/46.67  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 46.47/46.67  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 46.47/46.67  thf(sk_A_type, type, sk_A: $i).
% 46.47/46.67  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 46.47/46.67  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 46.47/46.67  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 46.47/46.67  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 46.47/46.67  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 46.47/46.67  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 46.47/46.67  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 46.47/46.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 46.47/46.67  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 46.47/46.67  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 46.47/46.67  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 46.47/46.67  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 46.47/46.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 46.47/46.67  thf(k5_lattices_type, type, k5_lattices: $i > $i).
% 46.47/46.67  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 46.47/46.67  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 46.47/46.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 46.47/46.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 46.47/46.67  thf(t47_lattice3, axiom,
% 46.47/46.67    (![A:$i]:
% 46.47/46.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 46.47/46.67         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 46.47/46.67       ( ![B:$i]:
% 46.47/46.67         ( ( ( k16_lattice3 @ A @ B ) =
% 46.47/46.67             ( k16_lattice3 @ A @ ( a_2_6_lattice3 @ A @ B ) ) ) & 
% 46.47/46.67           ( ( k15_lattice3 @ A @ B ) =
% 46.47/46.67             ( k15_lattice3 @ A @ ( a_2_5_lattice3 @ A @ B ) ) ) ) ) ))).
% 46.47/46.67  thf('0', plain,
% 46.47/46.67      (![X46 : $i, X48 : $i]:
% 46.47/46.67         (((k15_lattice3 @ X46 @ X48)
% 46.47/46.67            = (k15_lattice3 @ X46 @ (a_2_5_lattice3 @ X46 @ X48)))
% 46.47/46.67          | ~ (l3_lattices @ X46)
% 46.47/46.67          | ~ (v4_lattice3 @ X46)
% 46.47/46.67          | ~ (v10_lattices @ X46)
% 46.47/46.67          | (v2_struct_0 @ X46))),
% 46.47/46.67      inference('cnf', [status(esa)], [t47_lattice3])).
% 46.47/46.67  thf(dt_k15_lattice3, axiom,
% 46.47/46.67    (![A:$i,B:$i]:
% 46.47/46.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 46.47/46.67       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 46.47/46.67  thf('1', plain,
% 46.47/46.67      (![X34 : $i, X35 : $i]:
% 46.47/46.67         (~ (l3_lattices @ X34)
% 46.47/46.67          | (v2_struct_0 @ X34)
% 46.47/46.67          | (m1_subset_1 @ (k15_lattice3 @ X34 @ X35) @ (u1_struct_0 @ X34)))),
% 46.47/46.67      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 46.47/46.67  thf(d13_lattices, axiom,
% 46.47/46.67    (![A:$i]:
% 46.47/46.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 46.47/46.67       ( ( v13_lattices @ A ) <=>
% 46.47/46.67         ( ?[B:$i]:
% 46.47/46.67           ( ( ![C:$i]:
% 46.47/46.67               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 46.47/46.67                 ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 46.47/46.67                   ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) & 
% 46.47/46.67             ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) ) ) ) ))).
% 46.47/46.67  thf('2', plain,
% 46.47/46.67      (![X19 : $i, X20 : $i]:
% 46.47/46.67         ((m1_subset_1 @ (sk_C_3 @ X19 @ X20) @ (u1_struct_0 @ X20))
% 46.47/46.67          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 46.47/46.67          | (v13_lattices @ X20)
% 46.47/46.67          | ~ (l1_lattices @ X20)
% 46.47/46.67          | (v2_struct_0 @ X20))),
% 46.47/46.67      inference('cnf', [status(esa)], [d13_lattices])).
% 46.47/46.67  thf('3', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v13_lattices @ X0)
% 46.47/46.67          | (m1_subset_1 @ (sk_C_3 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 46.47/46.67             (u1_struct_0 @ X0)))),
% 46.47/46.67      inference('sup-', [status(thm)], ['1', '2'])).
% 46.47/46.67  thf('4', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         ((m1_subset_1 @ (sk_C_3 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 46.47/46.67           (u1_struct_0 @ X0))
% 46.47/46.67          | (v13_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['3'])).
% 46.47/46.67  thf(t43_lattice3, axiom,
% 46.47/46.67    (![A:$i]:
% 46.47/46.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 46.47/46.67         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 46.47/46.67       ( ![B:$i]:
% 46.47/46.67         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 46.47/46.67           ( ( ( k15_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 46.47/46.67               ( B ) ) & 
% 46.47/46.67             ( ( k16_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 46.47/46.67               ( B ) ) ) ) ) ))).
% 46.47/46.67  thf('5', plain,
% 46.47/46.67      (![X41 : $i, X42 : $i]:
% 46.47/46.67         (~ (m1_subset_1 @ X41 @ (u1_struct_0 @ X42))
% 46.47/46.67          | ((k15_lattice3 @ X42 @ (k6_domain_1 @ (u1_struct_0 @ X42) @ X41))
% 46.47/46.67              = (X41))
% 46.47/46.67          | ~ (l3_lattices @ X42)
% 46.47/46.67          | ~ (v4_lattice3 @ X42)
% 46.47/46.67          | ~ (v10_lattices @ X42)
% 46.47/46.67          | (v2_struct_0 @ X42))),
% 46.47/46.67      inference('cnf', [status(esa)], [t43_lattice3])).
% 46.47/46.67  thf('6', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v13_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ((k15_lattice3 @ X0 @ 
% 46.47/46.67              (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 46.47/46.67               (sk_C_3 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 46.47/46.67              = (sk_C_3 @ (k15_lattice3 @ X0 @ X1) @ X0)))),
% 46.47/46.67      inference('sup-', [status(thm)], ['4', '5'])).
% 46.47/46.67  thf('7', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         (((k15_lattice3 @ X0 @ 
% 46.47/46.67            (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 46.47/46.67             (sk_C_3 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 46.47/46.67            = (sk_C_3 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | (v13_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['6'])).
% 46.47/46.67  thf('8', plain,
% 46.47/46.67      (![X34 : $i, X35 : $i]:
% 46.47/46.67         (~ (l3_lattices @ X34)
% 46.47/46.67          | (v2_struct_0 @ X34)
% 46.47/46.67          | (m1_subset_1 @ (k15_lattice3 @ X34 @ X35) @ (u1_struct_0 @ X34)))),
% 46.47/46.67      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 46.47/46.67  thf('9', plain,
% 46.47/46.67      (![X34 : $i, X35 : $i]:
% 46.47/46.67         (~ (l3_lattices @ X34)
% 46.47/46.67          | (v2_struct_0 @ X34)
% 46.47/46.67          | (m1_subset_1 @ (k15_lattice3 @ X34 @ X35) @ (u1_struct_0 @ X34)))),
% 46.47/46.67      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 46.47/46.67  thf(d17_lattice3, axiom,
% 46.47/46.67    (![A:$i]:
% 46.47/46.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 46.47/46.67       ( ![B:$i]:
% 46.47/46.67         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 46.47/46.67           ( ![C:$i]:
% 46.47/46.67             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 46.47/46.67               ( ![D:$i]:
% 46.47/46.67                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 46.47/46.67                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 46.47/46.67  thf('10', plain,
% 46.47/46.67      (![X22 : $i, X23 : $i, X26 : $i]:
% 46.47/46.67         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 46.47/46.67          | (r2_hidden @ (sk_D @ X26 @ X22 @ X23) @ X26)
% 46.47/46.67          | (r4_lattice3 @ X23 @ X22 @ X26)
% 46.47/46.67          | ~ (l3_lattices @ X23)
% 46.47/46.67          | (v2_struct_0 @ X23))),
% 46.47/46.67      inference('cnf', [status(esa)], [d17_lattice3])).
% 46.47/46.67  thf('11', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 46.47/46.67          | (r2_hidden @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2))),
% 46.47/46.67      inference('sup-', [status(thm)], ['9', '10'])).
% 46.47/46.67  thf('12', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.47/46.67         ((r2_hidden @ (sk_D @ X2 @ (k15_lattice3 @ X0 @ X1) @ X0) @ X2)
% 46.47/46.67          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['11'])).
% 46.47/46.67  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 46.47/46.67  thf('13', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 46.47/46.67      inference('cnf', [status(esa)], [t65_xboole_1])).
% 46.47/46.67  thf(d3_tarski, axiom,
% 46.47/46.67    (![A:$i,B:$i]:
% 46.47/46.67     ( ( r1_tarski @ A @ B ) <=>
% 46.47/46.67       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 46.47/46.67  thf('14', plain,
% 46.47/46.67      (![X1 : $i, X3 : $i]:
% 46.47/46.67         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 46.47/46.67      inference('cnf', [status(esa)], [d3_tarski])).
% 46.47/46.67  thf(t4_xboole_0, axiom,
% 46.47/46.67    (![A:$i,B:$i]:
% 46.47/46.67     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 46.47/46.67            ( r1_xboole_0 @ A @ B ) ) ) & 
% 46.47/46.67       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 46.47/46.67            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 46.47/46.67  thf('15', plain,
% 46.47/46.67      (![X4 : $i, X6 : $i, X7 : $i]:
% 46.47/46.67         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 46.47/46.67          | ~ (r1_xboole_0 @ X4 @ X7))),
% 46.47/46.67      inference('cnf', [status(esa)], [t4_xboole_0])).
% 46.47/46.67  thf('16', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.47/46.67         ((r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 46.47/46.67          | ~ (r1_xboole_0 @ X1 @ X0))),
% 46.47/46.67      inference('sup-', [status(thm)], ['14', '15'])).
% 46.47/46.67  thf('17', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ X1)),
% 46.47/46.67      inference('sup-', [status(thm)], ['13', '16'])).
% 46.47/46.67  thf(t3_xboole_1, axiom,
% 46.47/46.67    (![A:$i]:
% 46.47/46.67     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 46.47/46.67  thf('18', plain,
% 46.47/46.67      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ k1_xboole_0))),
% 46.47/46.67      inference('cnf', [status(esa)], [t3_xboole_1])).
% 46.47/46.67  thf('19', plain,
% 46.47/46.67      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 46.47/46.67      inference('sup-', [status(thm)], ['17', '18'])).
% 46.47/46.67  thf('20', plain,
% 46.47/46.67      (![X4 : $i, X6 : $i, X7 : $i]:
% 46.47/46.67         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 46.47/46.67          | ~ (r1_xboole_0 @ X4 @ X7))),
% 46.47/46.67      inference('cnf', [status(esa)], [t4_xboole_0])).
% 46.47/46.67  thf('21', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 46.47/46.67      inference('sup-', [status(thm)], ['19', '20'])).
% 46.47/46.67  thf('22', plain, (![X9 : $i]: (r1_xboole_0 @ X9 @ k1_xboole_0)),
% 46.47/46.67      inference('cnf', [status(esa)], [t65_xboole_1])).
% 46.47/46.67  thf('23', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 46.47/46.67      inference('demod', [status(thm)], ['21', '22'])).
% 46.47/46.67  thf('24', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ k1_xboole_0))),
% 46.47/46.67      inference('sup-', [status(thm)], ['12', '23'])).
% 46.47/46.67  thf('25', plain,
% 46.47/46.67      (![X34 : $i, X35 : $i]:
% 46.47/46.67         (~ (l3_lattices @ X34)
% 46.47/46.67          | (v2_struct_0 @ X34)
% 46.47/46.67          | (m1_subset_1 @ (k15_lattice3 @ X34 @ X35) @ (u1_struct_0 @ X34)))),
% 46.47/46.67      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 46.47/46.67  thf('26', plain,
% 46.47/46.67      (![X34 : $i, X35 : $i]:
% 46.47/46.67         (~ (l3_lattices @ X34)
% 46.47/46.67          | (v2_struct_0 @ X34)
% 46.47/46.67          | (m1_subset_1 @ (k15_lattice3 @ X34 @ X35) @ (u1_struct_0 @ X34)))),
% 46.47/46.67      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 46.47/46.67  thf(d21_lattice3, axiom,
% 46.47/46.67    (![A:$i]:
% 46.47/46.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 46.47/46.67       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 46.47/46.67           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 46.47/46.67         ( ![B:$i,C:$i]:
% 46.47/46.67           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 46.47/46.67             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 46.47/46.67               ( ( r4_lattice3 @ A @ C @ B ) & 
% 46.47/46.67                 ( ![D:$i]:
% 46.47/46.67                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 46.47/46.67                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 46.47/46.67                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 46.47/46.67  thf('27', plain,
% 46.47/46.67      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X27)
% 46.47/46.67          | ~ (v10_lattices @ X27)
% 46.47/46.67          | ~ (v4_lattice3 @ X27)
% 46.47/46.67          | ~ (l3_lattices @ X27)
% 46.47/46.67          | ~ (m1_subset_1 @ X28 @ (u1_struct_0 @ X27))
% 46.47/46.67          | ((X28) != (k15_lattice3 @ X27 @ X29))
% 46.47/46.67          | ~ (r4_lattice3 @ X27 @ X30 @ X29)
% 46.47/46.67          | (r1_lattices @ X27 @ X28 @ X30)
% 46.47/46.67          | ~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X27))
% 46.47/46.67          | ~ (l3_lattices @ X27)
% 46.47/46.67          | (v2_struct_0 @ X27))),
% 46.47/46.67      inference('cnf', [status(esa)], [d21_lattice3])).
% 46.47/46.67  thf('28', plain,
% 46.47/46.67      (![X27 : $i, X29 : $i, X30 : $i]:
% 46.47/46.67         (~ (m1_subset_1 @ X30 @ (u1_struct_0 @ X27))
% 46.47/46.67          | (r1_lattices @ X27 @ (k15_lattice3 @ X27 @ X29) @ X30)
% 46.47/46.67          | ~ (r4_lattice3 @ X27 @ X30 @ X29)
% 46.47/46.67          | ~ (m1_subset_1 @ (k15_lattice3 @ X27 @ X29) @ (u1_struct_0 @ X27))
% 46.47/46.67          | ~ (l3_lattices @ X27)
% 46.47/46.67          | ~ (v4_lattice3 @ X27)
% 46.47/46.67          | ~ (v10_lattices @ X27)
% 46.47/46.67          | (v2_struct_0 @ X27))),
% 46.47/46.67      inference('simplify', [status(thm)], ['27'])).
% 46.47/46.67  thf('29', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 46.47/46.67          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 46.47/46.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 46.47/46.67      inference('sup-', [status(thm)], ['26', '28'])).
% 46.47/46.67  thf('30', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.47/46.67         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 46.47/46.67          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 46.47/46.67          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['29'])).
% 46.47/46.67  thf('31', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 46.47/46.67          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 46.47/46.67             (k15_lattice3 @ X0 @ X1)))),
% 46.47/46.67      inference('sup-', [status(thm)], ['25', '30'])).
% 46.47/46.67  thf('32', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.47/46.67         ((r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 46.47/46.67           (k15_lattice3 @ X0 @ X1))
% 46.47/46.67          | ~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['31'])).
% 46.47/46.67  thf('33', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         (~ (l3_lattices @ X1)
% 46.47/46.67          | (v2_struct_0 @ X1)
% 46.47/46.67          | (v2_struct_0 @ X1)
% 46.47/46.67          | ~ (l3_lattices @ X1)
% 46.47/46.67          | ~ (v10_lattices @ X1)
% 46.47/46.67          | ~ (v4_lattice3 @ X1)
% 46.47/46.67          | (r1_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 46.47/46.67             (k15_lattice3 @ X1 @ X0)))),
% 46.47/46.67      inference('sup-', [status(thm)], ['24', '32'])).
% 46.47/46.67  thf('34', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         ((r1_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 46.47/46.67           (k15_lattice3 @ X1 @ X0))
% 46.47/46.67          | ~ (v4_lattice3 @ X1)
% 46.47/46.67          | ~ (v10_lattices @ X1)
% 46.47/46.67          | (v2_struct_0 @ X1)
% 46.47/46.67          | ~ (l3_lattices @ X1))),
% 46.47/46.67      inference('simplify', [status(thm)], ['33'])).
% 46.47/46.67  thf('35', plain,
% 46.47/46.67      (![X34 : $i, X35 : $i]:
% 46.47/46.67         (~ (l3_lattices @ X34)
% 46.47/46.67          | (v2_struct_0 @ X34)
% 46.47/46.67          | (m1_subset_1 @ (k15_lattice3 @ X34 @ X35) @ (u1_struct_0 @ X34)))),
% 46.47/46.67      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 46.47/46.67  thf(t21_lattices, axiom,
% 46.47/46.67    (![A:$i]:
% 46.47/46.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 46.47/46.67         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 46.47/46.67       ( ![B:$i]:
% 46.47/46.67         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 46.47/46.67           ( ![C:$i]:
% 46.47/46.67             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 46.47/46.67               ( ( r1_lattices @ A @ B @ C ) <=>
% 46.47/46.67                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 46.47/46.67  thf('36', plain,
% 46.47/46.67      (![X16 : $i, X17 : $i, X18 : $i]:
% 46.47/46.67         (~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X17))
% 46.47/46.67          | ~ (r1_lattices @ X17 @ X16 @ X18)
% 46.47/46.67          | ((k2_lattices @ X17 @ X16 @ X18) = (X16))
% 46.47/46.67          | ~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X17))
% 46.47/46.67          | ~ (l3_lattices @ X17)
% 46.47/46.67          | ~ (v9_lattices @ X17)
% 46.47/46.67          | ~ (v8_lattices @ X17)
% 46.47/46.67          | (v2_struct_0 @ X17))),
% 46.47/46.67      inference('cnf', [status(esa)], [t21_lattices])).
% 46.47/46.67  thf('37', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v9_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 46.47/46.67          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 46.47/46.67              = (k15_lattice3 @ X0 @ X1))
% 46.47/46.67          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 46.47/46.67      inference('sup-', [status(thm)], ['35', '36'])).
% 46.47/46.67  thf('38', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.47/46.67         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 46.47/46.67          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 46.47/46.67              = (k15_lattice3 @ X0 @ X1))
% 46.47/46.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 46.47/46.67          | ~ (v9_lattices @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['37'])).
% 46.47/46.67  thf('39', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         (~ (l3_lattices @ X1)
% 46.47/46.67          | (v2_struct_0 @ X1)
% 46.47/46.67          | ~ (v10_lattices @ X1)
% 46.47/46.67          | ~ (v4_lattice3 @ X1)
% 46.47/46.67          | (v2_struct_0 @ X1)
% 46.47/46.67          | ~ (l3_lattices @ X1)
% 46.47/46.67          | ~ (v8_lattices @ X1)
% 46.47/46.67          | ~ (v9_lattices @ X1)
% 46.47/46.67          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 46.47/46.67          | ((k2_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 46.47/46.67              (k15_lattice3 @ X1 @ X0)) = (k15_lattice3 @ X1 @ k1_xboole_0)))),
% 46.47/46.67      inference('sup-', [status(thm)], ['34', '38'])).
% 46.47/46.67  thf('40', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         (((k2_lattices @ X1 @ (k15_lattice3 @ X1 @ k1_xboole_0) @ 
% 46.47/46.67            (k15_lattice3 @ X1 @ X0)) = (k15_lattice3 @ X1 @ k1_xboole_0))
% 46.47/46.67          | ~ (m1_subset_1 @ (k15_lattice3 @ X1 @ X0) @ (u1_struct_0 @ X1))
% 46.47/46.67          | ~ (v9_lattices @ X1)
% 46.47/46.67          | ~ (v8_lattices @ X1)
% 46.47/46.67          | ~ (v4_lattice3 @ X1)
% 46.47/46.67          | ~ (v10_lattices @ X1)
% 46.47/46.67          | (v2_struct_0 @ X1)
% 46.47/46.67          | ~ (l3_lattices @ X1))),
% 46.47/46.67      inference('simplify', [status(thm)], ['39'])).
% 46.47/46.67  thf('41', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v9_lattices @ X0)
% 46.47/46.67          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 46.47/46.67              (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 46.47/46.67      inference('sup-', [status(thm)], ['8', '40'])).
% 46.47/46.67  thf('42', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 46.47/46.67            (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 46.47/46.67          | ~ (v9_lattices @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['41'])).
% 46.47/46.67  thf('43', plain,
% 46.47/46.67      (![X34 : $i, X35 : $i]:
% 46.47/46.67         (~ (l3_lattices @ X34)
% 46.47/46.67          | (v2_struct_0 @ X34)
% 46.47/46.67          | (m1_subset_1 @ (k15_lattice3 @ X34 @ X35) @ (u1_struct_0 @ X34)))),
% 46.47/46.67      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 46.47/46.67  thf('44', plain,
% 46.47/46.67      (![X34 : $i, X35 : $i]:
% 46.47/46.67         (~ (l3_lattices @ X34)
% 46.47/46.67          | (v2_struct_0 @ X34)
% 46.47/46.67          | (m1_subset_1 @ (k15_lattice3 @ X34 @ X35) @ (u1_struct_0 @ X34)))),
% 46.47/46.67      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 46.47/46.67  thf(d6_lattices, axiom,
% 46.47/46.67    (![A:$i]:
% 46.47/46.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 46.47/46.67       ( ( v6_lattices @ A ) <=>
% 46.47/46.67         ( ![B:$i]:
% 46.47/46.67           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 46.47/46.67             ( ![C:$i]:
% 46.47/46.67               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 46.47/46.67                 ( ( k2_lattices @ A @ B @ C ) = ( k2_lattices @ A @ C @ B ) ) ) ) ) ) ) ))).
% 46.47/46.67  thf('45', plain,
% 46.47/46.67      (![X31 : $i, X32 : $i, X33 : $i]:
% 46.47/46.67         (~ (v6_lattices @ X31)
% 46.47/46.67          | ~ (m1_subset_1 @ X32 @ (u1_struct_0 @ X31))
% 46.47/46.67          | ((k2_lattices @ X31 @ X33 @ X32) = (k2_lattices @ X31 @ X32 @ X33))
% 46.47/46.67          | ~ (m1_subset_1 @ X33 @ (u1_struct_0 @ X31))
% 46.47/46.67          | ~ (l1_lattices @ X31)
% 46.47/46.67          | (v2_struct_0 @ X31))),
% 46.47/46.67      inference('cnf', [status(esa)], [d6_lattices])).
% 46.47/46.67  thf('46', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 46.47/46.67          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 46.47/46.67              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 46.47/46.67          | ~ (v6_lattices @ X0))),
% 46.47/46.67      inference('sup-', [status(thm)], ['44', '45'])).
% 46.47/46.67  thf('47', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.47/46.67         (~ (v6_lattices @ X0)
% 46.47/46.67          | ((k2_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 46.47/46.67              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))
% 46.47/46.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['46'])).
% 46.47/46.67  thf('48', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 46.47/46.67              (k15_lattice3 @ X0 @ X2))
% 46.47/46.67              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 46.47/46.67                 (k15_lattice3 @ X0 @ X1)))
% 46.47/46.67          | ~ (v6_lattices @ X0))),
% 46.47/46.67      inference('sup-', [status(thm)], ['43', '47'])).
% 46.47/46.67  thf('49', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.47/46.67         (~ (v6_lattices @ X0)
% 46.47/46.67          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 46.47/46.67              (k15_lattice3 @ X0 @ X2))
% 46.47/46.67              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X2) @ 
% 46.47/46.67                 (k15_lattice3 @ X0 @ X1)))
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['48'])).
% 46.47/46.67  thf('50', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 46.47/46.67            = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 46.47/46.67               (k15_lattice3 @ X0 @ k1_xboole_0)))
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v9_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (v6_lattices @ X0))),
% 46.47/46.67      inference('sup+', [status(thm)], ['42', '49'])).
% 46.47/46.67  thf('51', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         (~ (v6_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (v9_lattices @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 46.47/46.67              = (k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 46.47/46.67                 (k15_lattice3 @ X0 @ k1_xboole_0))))),
% 46.47/46.67      inference('simplify', [status(thm)], ['50'])).
% 46.47/46.67  thf('52', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 46.47/46.67            = (k2_lattices @ X0 @ (sk_C_3 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 46.47/46.67               (k15_lattice3 @ X0 @ k1_xboole_0)))
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v13_lattices @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v9_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (v6_lattices @ X0))),
% 46.47/46.67      inference('sup+', [status(thm)], ['7', '51'])).
% 46.47/46.67  thf('53', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         (~ (v6_lattices @ X0)
% 46.47/46.67          | ~ (v9_lattices @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | (v13_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 46.47/46.67              = (k2_lattices @ X0 @ (sk_C_3 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 46.47/46.67                 (k15_lattice3 @ X0 @ k1_xboole_0))))),
% 46.47/46.67      inference('simplify', [status(thm)], ['52'])).
% 46.47/46.67  thf('54', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         (((k15_lattice3 @ X0 @ 
% 46.47/46.67            (k6_domain_1 @ (u1_struct_0 @ X0) @ 
% 46.47/46.67             (sk_C_3 @ (k15_lattice3 @ X0 @ X1) @ X0)))
% 46.47/46.67            = (sk_C_3 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | (v13_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['6'])).
% 46.47/46.67  thf('55', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 46.47/46.67            (k15_lattice3 @ X0 @ X1)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 46.47/46.67          | ~ (v9_lattices @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['41'])).
% 46.47/46.67  thf('56', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 46.47/46.67            (sk_C_3 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 46.47/46.67            = (k15_lattice3 @ X0 @ k1_xboole_0))
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v13_lattices @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v9_lattices @ X0))),
% 46.47/46.67      inference('sup+', [status(thm)], ['54', '55'])).
% 46.47/46.67  thf('57', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         (~ (v9_lattices @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | (v13_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 46.47/46.67              (sk_C_3 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 46.47/46.67              = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 46.47/46.67      inference('simplify', [status(thm)], ['56'])).
% 46.47/46.67  thf('58', plain,
% 46.47/46.67      (![X46 : $i, X48 : $i]:
% 46.47/46.67         (((k15_lattice3 @ X46 @ X48)
% 46.47/46.67            = (k15_lattice3 @ X46 @ (a_2_5_lattice3 @ X46 @ X48)))
% 46.47/46.67          | ~ (l3_lattices @ X46)
% 46.47/46.67          | ~ (v4_lattice3 @ X46)
% 46.47/46.67          | ~ (v10_lattices @ X46)
% 46.47/46.67          | (v2_struct_0 @ X46))),
% 46.47/46.67      inference('cnf', [status(esa)], [t47_lattice3])).
% 46.47/46.67  thf('59', plain,
% 46.47/46.67      (![X1 : $i, X3 : $i]:
% 46.47/46.67         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 46.47/46.67      inference('cnf', [status(esa)], [d3_tarski])).
% 46.47/46.67  thf(fraenkel_a_2_5_lattice3, axiom,
% 46.47/46.67    (![A:$i,B:$i,C:$i]:
% 46.47/46.67     ( ( ( ~( v2_struct_0 @ B ) ) & ( v10_lattices @ B ) & 
% 46.47/46.67         ( v4_lattice3 @ B ) & ( l3_lattices @ B ) ) =>
% 46.47/46.67       ( ( r2_hidden @ A @ ( a_2_5_lattice3 @ B @ C ) ) <=>
% 46.47/46.67         ( ?[D:$i]:
% 46.47/46.67           ( ( ?[E:$i]:
% 46.47/46.67               ( ( r2_hidden @ E @ C ) & ( r3_lattices @ B @ D @ E ) & 
% 46.47/46.67                 ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) ) ) & 
% 46.47/46.67             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 46.47/46.67  thf('60', plain,
% 46.47/46.67      (![X36 : $i, X37 : $i, X38 : $i]:
% 46.47/46.67         (~ (l3_lattices @ X36)
% 46.47/46.67          | ~ (v4_lattice3 @ X36)
% 46.47/46.67          | ~ (v10_lattices @ X36)
% 46.47/46.67          | (v2_struct_0 @ X36)
% 46.47/46.67          | (r2_hidden @ (sk_E @ X37 @ X36 @ X38) @ X37)
% 46.47/46.67          | ~ (r2_hidden @ X38 @ (a_2_5_lattice3 @ X36 @ X37)))),
% 46.47/46.67      inference('cnf', [status(esa)], [fraenkel_a_2_5_lattice3])).
% 46.47/46.67  thf('61', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.47/46.67         ((r1_tarski @ (a_2_5_lattice3 @ X1 @ X0) @ X2)
% 46.47/46.67          | (r2_hidden @ 
% 46.47/46.67             (sk_E @ X0 @ X1 @ (sk_C @ X2 @ (a_2_5_lattice3 @ X1 @ X0))) @ X0)
% 46.47/46.67          | (v2_struct_0 @ X1)
% 46.47/46.67          | ~ (v10_lattices @ X1)
% 46.47/46.67          | ~ (v4_lattice3 @ X1)
% 46.47/46.67          | ~ (l3_lattices @ X1))),
% 46.47/46.67      inference('sup-', [status(thm)], ['59', '60'])).
% 46.47/46.67  thf('62', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 46.47/46.67      inference('demod', [status(thm)], ['21', '22'])).
% 46.47/46.67  thf('63', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         (~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | (r1_tarski @ (a_2_5_lattice3 @ X0 @ k1_xboole_0) @ X1))),
% 46.47/46.67      inference('sup-', [status(thm)], ['61', '62'])).
% 46.47/46.67  thf('64', plain,
% 46.47/46.67      (![X8 : $i]: (((X8) = (k1_xboole_0)) | ~ (r1_tarski @ X8 @ k1_xboole_0))),
% 46.47/46.67      inference('cnf', [status(esa)], [t3_xboole_1])).
% 46.47/46.67  thf('65', plain,
% 46.47/46.67      (![X0 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ((a_2_5_lattice3 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 46.47/46.67      inference('sup-', [status(thm)], ['63', '64'])).
% 46.47/46.67  thf('66', plain,
% 46.47/46.67      (![X46 : $i, X48 : $i]:
% 46.47/46.67         (((k15_lattice3 @ X46 @ X48)
% 46.47/46.67            = (k15_lattice3 @ X46 @ (a_2_5_lattice3 @ X46 @ X48)))
% 46.47/46.67          | ~ (l3_lattices @ X46)
% 46.47/46.67          | ~ (v4_lattice3 @ X46)
% 46.47/46.67          | ~ (v10_lattices @ X46)
% 46.47/46.67          | (v2_struct_0 @ X46))),
% 46.47/46.67      inference('cnf', [status(esa)], [t47_lattice3])).
% 46.47/46.67  thf('67', plain,
% 46.47/46.67      (![X34 : $i, X35 : $i]:
% 46.47/46.67         (~ (l3_lattices @ X34)
% 46.47/46.67          | (v2_struct_0 @ X34)
% 46.47/46.67          | (m1_subset_1 @ (k15_lattice3 @ X34 @ X35) @ (u1_struct_0 @ X34)))),
% 46.47/46.67      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 46.47/46.67  thf('68', plain,
% 46.47/46.67      (![X19 : $i, X20 : $i]:
% 46.47/46.67         (((k2_lattices @ X20 @ (sk_C_3 @ X19 @ X20) @ X19) != (X19))
% 46.47/46.67          | ((k2_lattices @ X20 @ X19 @ (sk_C_3 @ X19 @ X20)) != (X19))
% 46.47/46.67          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 46.47/46.67          | (v13_lattices @ X20)
% 46.47/46.67          | ~ (l1_lattices @ X20)
% 46.47/46.67          | (v2_struct_0 @ X20))),
% 46.47/46.67      inference('cnf', [status(esa)], [d13_lattices])).
% 46.47/46.67  thf('69', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v13_lattices @ X0)
% 46.47/46.67          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 46.47/46.67              (sk_C_3 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 46.47/46.67              != (k15_lattice3 @ X0 @ X1))
% 46.47/46.67          | ((k2_lattices @ X0 @ (sk_C_3 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 46.47/46.67              (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1)))),
% 46.47/46.67      inference('sup-', [status(thm)], ['67', '68'])).
% 46.47/46.67  thf('70', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         (((k2_lattices @ X0 @ (sk_C_3 @ (k15_lattice3 @ X0 @ X1) @ X0) @ 
% 46.47/46.67            (k15_lattice3 @ X0 @ X1)) != (k15_lattice3 @ X0 @ X1))
% 46.47/46.67          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ 
% 46.47/46.67              (sk_C_3 @ (k15_lattice3 @ X0 @ X1) @ X0))
% 46.47/46.67              != (k15_lattice3 @ X0 @ X1))
% 46.47/46.67          | (v13_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['69'])).
% 46.47/46.67  thf('71', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         (((k2_lattices @ X1 @ (sk_C_3 @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 46.47/46.67            (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)))
% 46.47/46.67            != (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)))
% 46.47/46.67          | (v2_struct_0 @ X1)
% 46.47/46.67          | ~ (v10_lattices @ X1)
% 46.47/46.67          | ~ (v4_lattice3 @ X1)
% 46.47/46.67          | ~ (l3_lattices @ X1)
% 46.47/46.67          | (v2_struct_0 @ X1)
% 46.47/46.67          | ~ (l3_lattices @ X1)
% 46.47/46.67          | ~ (l1_lattices @ X1)
% 46.47/46.67          | (v13_lattices @ X1)
% 46.47/46.67          | ((k2_lattices @ X1 @ 
% 46.47/46.67              (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)) @ 
% 46.47/46.67              (sk_C_3 @ (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)) @ X1))
% 46.47/46.67              != (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0))))),
% 46.47/46.67      inference('sup-', [status(thm)], ['66', '70'])).
% 46.47/46.67  thf('72', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         (((k2_lattices @ X1 @ 
% 46.47/46.67            (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)) @ 
% 46.47/46.67            (sk_C_3 @ (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)) @ X1))
% 46.47/46.67            != (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)))
% 46.47/46.67          | (v13_lattices @ X1)
% 46.47/46.67          | ~ (l1_lattices @ X1)
% 46.47/46.67          | ~ (l3_lattices @ X1)
% 46.47/46.67          | ~ (v4_lattice3 @ X1)
% 46.47/46.67          | ~ (v10_lattices @ X1)
% 46.47/46.67          | (v2_struct_0 @ X1)
% 46.47/46.67          | ((k2_lattices @ X1 @ (sk_C_3 @ (k15_lattice3 @ X1 @ X0) @ X1) @ 
% 46.47/46.67              (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0)))
% 46.47/46.67              != (k15_lattice3 @ X1 @ (a_2_5_lattice3 @ X1 @ X0))))),
% 46.47/46.67      inference('simplify', [status(thm)], ['71'])).
% 46.47/46.67  thf('73', plain,
% 46.47/46.67      (![X0 : $i]:
% 46.47/46.67         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 46.47/46.67            (sk_C_3 @ 
% 46.47/46.67             (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)) @ X0))
% 46.47/46.67            != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ((k2_lattices @ X0 @ 
% 46.47/46.67              (sk_C_3 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 46.47/46.67              (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 46.47/46.67              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v13_lattices @ X0))),
% 46.47/46.67      inference('sup-', [status(thm)], ['65', '72'])).
% 46.47/46.67  thf('74', plain,
% 46.47/46.67      (![X0 : $i]:
% 46.47/46.67         ((v13_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ((k2_lattices @ X0 @ 
% 46.47/46.67              (sk_C_3 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 46.47/46.67              (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 46.47/46.67              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 46.47/46.67              (sk_C_3 @ 
% 46.47/46.67               (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)) @ X0))
% 46.47/46.67              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0))))),
% 46.47/46.67      inference('simplify', [status(thm)], ['73'])).
% 46.47/46.67  thf('75', plain,
% 46.47/46.67      (![X0 : $i]:
% 46.47/46.67         (((k2_lattices @ X0 @ 
% 46.47/46.67            (sk_C_3 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 46.47/46.67            (k15_lattice3 @ X0 @ k1_xboole_0))
% 46.47/46.67            != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 46.47/46.67              (sk_C_3 @ 
% 46.47/46.67               (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)) @ X0))
% 46.47/46.67              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v13_lattices @ X0))),
% 46.47/46.67      inference('sup-', [status(thm)], ['58', '74'])).
% 46.47/46.67  thf('76', plain,
% 46.47/46.67      (![X0 : $i]:
% 46.47/46.67         ((v13_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 46.47/46.67              (sk_C_3 @ 
% 46.47/46.67               (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)) @ X0))
% 46.47/46.67              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ((k2_lattices @ X0 @ 
% 46.47/46.67              (sk_C_3 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 46.47/46.67              (k15_lattice3 @ X0 @ k1_xboole_0))
% 46.47/46.67              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0))))),
% 46.47/46.67      inference('simplify', [status(thm)], ['75'])).
% 46.47/46.67  thf('77', plain,
% 46.47/46.67      (![X0 : $i]:
% 46.47/46.67         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 46.47/46.67            != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v13_lattices @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v9_lattices @ X0)
% 46.47/46.67          | ((k2_lattices @ X0 @ 
% 46.47/46.67              (sk_C_3 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 46.47/46.67              (k15_lattice3 @ X0 @ k1_xboole_0))
% 46.47/46.67              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v13_lattices @ X0))),
% 46.47/46.67      inference('sup-', [status(thm)], ['57', '76'])).
% 46.47/46.67  thf('78', plain,
% 46.47/46.67      (![X0 : $i]:
% 46.47/46.67         (((k2_lattices @ X0 @ 
% 46.47/46.67            (sk_C_3 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ X0) @ 
% 46.47/46.67            (k15_lattice3 @ X0 @ k1_xboole_0))
% 46.47/46.67            != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 46.47/46.67          | ~ (v9_lattices @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | (v13_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 46.47/46.67              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0))))),
% 46.47/46.67      inference('simplify', [status(thm)], ['77'])).
% 46.47/46.67  thf('79', plain,
% 46.47/46.67      (![X0 : $i]:
% 46.47/46.67         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 46.47/46.67            != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v13_lattices @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v9_lattices @ X0)
% 46.47/46.67          | ~ (v6_lattices @ X0)
% 46.47/46.67          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 46.47/46.67              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0)))
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v13_lattices @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v9_lattices @ X0))),
% 46.47/46.67      inference('sup-', [status(thm)], ['53', '78'])).
% 46.47/46.67  thf('80', plain,
% 46.47/46.67      (![X0 : $i]:
% 46.47/46.67         (~ (v6_lattices @ X0)
% 46.47/46.67          | ~ (v9_lattices @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | (v13_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ((k15_lattice3 @ X0 @ k1_xboole_0)
% 46.47/46.67              != (k15_lattice3 @ X0 @ (a_2_5_lattice3 @ X0 @ k1_xboole_0))))),
% 46.47/46.67      inference('simplify', [status(thm)], ['79'])).
% 46.47/46.67  thf('81', plain,
% 46.47/46.67      (![X0 : $i]:
% 46.47/46.67         (((k15_lattice3 @ X0 @ k1_xboole_0)
% 46.47/46.67            != (k15_lattice3 @ X0 @ k1_xboole_0))
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v13_lattices @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v9_lattices @ X0)
% 46.47/46.67          | ~ (v6_lattices @ X0))),
% 46.47/46.67      inference('sup-', [status(thm)], ['0', '80'])).
% 46.47/46.67  thf('82', plain,
% 46.47/46.67      (![X0 : $i]:
% 46.47/46.67         (~ (v6_lattices @ X0)
% 46.47/46.67          | ~ (v9_lattices @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | (v13_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['81'])).
% 46.47/46.67  thf(t50_lattice3, conjecture,
% 46.47/46.67    (![A:$i]:
% 46.47/46.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 46.47/46.67         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 46.47/46.67       ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 46.47/46.67         ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 46.47/46.67         ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ))).
% 46.47/46.67  thf(zf_stmt_0, negated_conjecture,
% 46.47/46.67    (~( ![A:$i]:
% 46.47/46.67        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 46.47/46.67            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 46.47/46.67          ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 46.47/46.67            ( v13_lattices @ A ) & ( l3_lattices @ A ) & 
% 46.47/46.67            ( ( k5_lattices @ A ) = ( k15_lattice3 @ A @ k1_xboole_0 ) ) ) ) )),
% 46.47/46.67    inference('cnf.neg', [status(esa)], [t50_lattice3])).
% 46.47/46.67  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('84', plain,
% 46.47/46.67      ((~ (v10_lattices @ sk_A)
% 46.47/46.67        | ~ (v4_lattice3 @ sk_A)
% 46.47/46.67        | ~ (l3_lattices @ sk_A)
% 46.47/46.67        | ~ (l1_lattices @ sk_A)
% 46.47/46.67        | (v13_lattices @ sk_A)
% 46.47/46.67        | ~ (v8_lattices @ sk_A)
% 46.47/46.67        | ~ (v9_lattices @ sk_A)
% 46.47/46.67        | ~ (v6_lattices @ sk_A))),
% 46.47/46.67      inference('sup-', [status(thm)], ['82', '83'])).
% 46.47/46.67  thf('85', plain, ((v10_lattices @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('86', plain, ((v4_lattice3 @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('87', plain, ((l3_lattices @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('88', plain, ((l3_lattices @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf(dt_l3_lattices, axiom,
% 46.47/46.67    (![A:$i]:
% 46.47/46.67     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 46.47/46.67  thf('89', plain,
% 46.47/46.67      (![X15 : $i]: ((l1_lattices @ X15) | ~ (l3_lattices @ X15))),
% 46.47/46.67      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 46.47/46.67  thf('90', plain, ((l1_lattices @ sk_A)),
% 46.47/46.67      inference('sup-', [status(thm)], ['88', '89'])).
% 46.47/46.67  thf(cc1_lattices, axiom,
% 46.47/46.67    (![A:$i]:
% 46.47/46.67     ( ( l3_lattices @ A ) =>
% 46.47/46.67       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 46.47/46.67         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 46.47/46.67           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 46.47/46.67           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 46.47/46.67  thf('91', plain,
% 46.47/46.67      (![X10 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X10)
% 46.47/46.67          | ~ (v10_lattices @ X10)
% 46.47/46.67          | (v8_lattices @ X10)
% 46.47/46.67          | ~ (l3_lattices @ X10))),
% 46.47/46.67      inference('cnf', [status(esa)], [cc1_lattices])).
% 46.47/46.67  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('93', plain,
% 46.47/46.67      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 46.47/46.67      inference('sup-', [status(thm)], ['91', '92'])).
% 46.47/46.67  thf('94', plain, ((l3_lattices @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('95', plain, ((v10_lattices @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('96', plain, ((v8_lattices @ sk_A)),
% 46.47/46.67      inference('demod', [status(thm)], ['93', '94', '95'])).
% 46.47/46.67  thf('97', plain,
% 46.47/46.67      (![X10 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X10)
% 46.47/46.67          | ~ (v10_lattices @ X10)
% 46.47/46.67          | (v9_lattices @ X10)
% 46.47/46.67          | ~ (l3_lattices @ X10))),
% 46.47/46.67      inference('cnf', [status(esa)], [cc1_lattices])).
% 46.47/46.67  thf('98', plain, (~ (v2_struct_0 @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('99', plain,
% 46.47/46.67      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 46.47/46.67      inference('sup-', [status(thm)], ['97', '98'])).
% 46.47/46.67  thf('100', plain, ((l3_lattices @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('101', plain, ((v10_lattices @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('102', plain, ((v9_lattices @ sk_A)),
% 46.47/46.67      inference('demod', [status(thm)], ['99', '100', '101'])).
% 46.47/46.67  thf('103', plain,
% 46.47/46.67      (![X10 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X10)
% 46.47/46.67          | ~ (v10_lattices @ X10)
% 46.47/46.67          | (v6_lattices @ X10)
% 46.47/46.67          | ~ (l3_lattices @ X10))),
% 46.47/46.67      inference('cnf', [status(esa)], [cc1_lattices])).
% 46.47/46.67  thf('104', plain, (~ (v2_struct_0 @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('105', plain,
% 46.47/46.67      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 46.47/46.67      inference('sup-', [status(thm)], ['103', '104'])).
% 46.47/46.67  thf('106', plain, ((l3_lattices @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('107', plain, ((v10_lattices @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('108', plain, ((v6_lattices @ sk_A)),
% 46.47/46.67      inference('demod', [status(thm)], ['105', '106', '107'])).
% 46.47/46.67  thf('109', plain, ((v13_lattices @ sk_A)),
% 46.47/46.67      inference('demod', [status(thm)],
% 46.47/46.67                ['84', '85', '86', '87', '90', '96', '102', '108'])).
% 46.47/46.67  thf('110', plain,
% 46.47/46.67      (![X34 : $i, X35 : $i]:
% 46.47/46.67         (~ (l3_lattices @ X34)
% 46.47/46.67          | (v2_struct_0 @ X34)
% 46.47/46.67          | (m1_subset_1 @ (k15_lattice3 @ X34 @ X35) @ (u1_struct_0 @ X34)))),
% 46.47/46.67      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 46.47/46.67  thf(dt_k5_lattices, axiom,
% 46.47/46.67    (![A:$i]:
% 46.47/46.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 46.47/46.67       ( m1_subset_1 @ ( k5_lattices @ A ) @ ( u1_struct_0 @ A ) ) ))).
% 46.47/46.67  thf('111', plain,
% 46.47/46.67      (![X14 : $i]:
% 46.47/46.67         ((m1_subset_1 @ (k5_lattices @ X14) @ (u1_struct_0 @ X14))
% 46.47/46.67          | ~ (l1_lattices @ X14)
% 46.47/46.67          | (v2_struct_0 @ X14))),
% 46.47/46.67      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 46.47/46.67  thf(d16_lattices, axiom,
% 46.47/46.67    (![A:$i]:
% 46.47/46.67     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_lattices @ A ) ) =>
% 46.47/46.67       ( ( v13_lattices @ A ) =>
% 46.47/46.67         ( ![B:$i]:
% 46.47/46.67           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 46.47/46.67             ( ( ( B ) = ( k5_lattices @ A ) ) <=>
% 46.47/46.67               ( ![C:$i]:
% 46.47/46.67                 ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 46.47/46.67                   ( ( ( k2_lattices @ A @ B @ C ) = ( B ) ) & 
% 46.47/46.67                     ( ( k2_lattices @ A @ C @ B ) = ( B ) ) ) ) ) ) ) ) ) ))).
% 46.47/46.67  thf('112', plain,
% 46.47/46.67      (![X11 : $i, X12 : $i, X13 : $i]:
% 46.47/46.67         (~ (v13_lattices @ X11)
% 46.47/46.67          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 46.47/46.67          | ((X12) != (k5_lattices @ X11))
% 46.47/46.67          | ((k2_lattices @ X11 @ X13 @ X12) = (X12))
% 46.47/46.67          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 46.47/46.67          | ~ (l1_lattices @ X11)
% 46.47/46.67          | (v2_struct_0 @ X11))),
% 46.47/46.67      inference('cnf', [status(esa)], [d16_lattices])).
% 46.47/46.67  thf('113', plain,
% 46.47/46.67      (![X11 : $i, X13 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X11)
% 46.47/46.67          | ~ (l1_lattices @ X11)
% 46.47/46.67          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 46.47/46.67          | ((k2_lattices @ X11 @ X13 @ (k5_lattices @ X11))
% 46.47/46.67              = (k5_lattices @ X11))
% 46.47/46.67          | ~ (m1_subset_1 @ (k5_lattices @ X11) @ (u1_struct_0 @ X11))
% 46.47/46.67          | ~ (v13_lattices @ X11))),
% 46.47/46.67      inference('simplify', [status(thm)], ['112'])).
% 46.47/46.67  thf('114', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (v13_lattices @ X0)
% 46.47/46.67          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 46.47/46.67          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('sup-', [status(thm)], ['111', '113'])).
% 46.47/46.67  thf('115', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         (~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 46.47/46.67          | ((k2_lattices @ X0 @ X1 @ (k5_lattices @ X0)) = (k5_lattices @ X0))
% 46.47/46.67          | ~ (v13_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['114'])).
% 46.47/46.67  thf('116', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (v13_lattices @ X0)
% 46.47/46.67          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 46.47/46.67              = (k5_lattices @ X0)))),
% 46.47/46.67      inference('sup-', [status(thm)], ['110', '115'])).
% 46.47/46.67  thf('117', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 46.47/46.67            = (k5_lattices @ X0))
% 46.47/46.67          | ~ (v13_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['116'])).
% 46.47/46.67  thf('118', plain,
% 46.47/46.67      (![X14 : $i]:
% 46.47/46.67         ((m1_subset_1 @ (k5_lattices @ X14) @ (u1_struct_0 @ X14))
% 46.47/46.67          | ~ (l1_lattices @ X14)
% 46.47/46.67          | (v2_struct_0 @ X14))),
% 46.47/46.67      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 46.47/46.67  thf('119', plain,
% 46.47/46.67      (![X14 : $i]:
% 46.47/46.67         ((m1_subset_1 @ (k5_lattices @ X14) @ (u1_struct_0 @ X14))
% 46.47/46.67          | ~ (l1_lattices @ X14)
% 46.47/46.67          | (v2_struct_0 @ X14))),
% 46.47/46.67      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 46.47/46.67  thf('120', plain,
% 46.47/46.67      (![X22 : $i, X23 : $i, X26 : $i]:
% 46.47/46.67         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 46.47/46.67          | (r2_hidden @ (sk_D @ X26 @ X22 @ X23) @ X26)
% 46.47/46.67          | (r4_lattice3 @ X23 @ X22 @ X26)
% 46.47/46.67          | ~ (l3_lattices @ X23)
% 46.47/46.67          | (v2_struct_0 @ X23))),
% 46.47/46.67      inference('cnf', [status(esa)], [d17_lattice3])).
% 46.47/46.67  thf('121', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ X1)
% 46.47/46.67          | (r2_hidden @ (sk_D @ X1 @ (k5_lattices @ X0) @ X0) @ X1))),
% 46.47/46.67      inference('sup-', [status(thm)], ['119', '120'])).
% 46.47/46.67  thf('122', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         ((r2_hidden @ (sk_D @ X1 @ (k5_lattices @ X0) @ X0) @ X1)
% 46.47/46.67          | (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ X1)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['121'])).
% 46.47/46.67  thf('123', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 46.47/46.67      inference('demod', [status(thm)], ['21', '22'])).
% 46.47/46.67  thf('124', plain,
% 46.47/46.67      (![X0 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ k1_xboole_0))),
% 46.47/46.67      inference('sup-', [status(thm)], ['122', '123'])).
% 46.47/46.67  thf('125', plain,
% 46.47/46.67      (![X14 : $i]:
% 46.47/46.67         ((m1_subset_1 @ (k5_lattices @ X14) @ (u1_struct_0 @ X14))
% 46.47/46.67          | ~ (l1_lattices @ X14)
% 46.47/46.67          | (v2_struct_0 @ X14))),
% 46.47/46.67      inference('cnf', [status(esa)], [dt_k5_lattices])).
% 46.47/46.67  thf('126', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.47/46.67         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 46.47/46.67          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 46.47/46.67          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['29'])).
% 46.47/46.67  thf('127', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ X1)
% 46.47/46.67          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0)))),
% 46.47/46.67      inference('sup-', [status(thm)], ['125', '126'])).
% 46.47/46.67  thf('128', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i]:
% 46.47/46.67         ((r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ (k5_lattices @ X0))
% 46.47/46.67          | ~ (r4_lattice3 @ X0 @ (k5_lattices @ X0) @ X1)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['127'])).
% 46.47/46.67  thf('129', plain,
% 46.47/46.67      (![X0 : $i]:
% 46.47/46.67         (~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 46.47/46.67             (k5_lattices @ X0)))),
% 46.47/46.67      inference('sup-', [status(thm)], ['124', '128'])).
% 46.47/46.67  thf('130', plain,
% 46.47/46.67      (![X0 : $i]:
% 46.47/46.67         ((r1_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 46.47/46.67           (k5_lattices @ X0))
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['129'])).
% 46.47/46.67  thf('131', plain,
% 46.47/46.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 46.47/46.67         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 46.47/46.67          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 46.47/46.67              = (k15_lattice3 @ X0 @ X1))
% 46.47/46.67          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 46.47/46.67          | ~ (v9_lattices @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['37'])).
% 46.47/46.67  thf('132', plain,
% 46.47/46.67      (![X0 : $i]:
% 46.47/46.67         (~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v9_lattices @ X0)
% 46.47/46.67          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 46.47/46.67          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 46.47/46.67              (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 46.47/46.67      inference('sup-', [status(thm)], ['130', '131'])).
% 46.47/46.67  thf('133', plain,
% 46.47/46.67      (![X0 : $i]:
% 46.47/46.67         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 46.47/46.67            (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 46.47/46.67          | ~ (m1_subset_1 @ (k5_lattices @ X0) @ (u1_struct_0 @ X0))
% 46.47/46.67          | ~ (v9_lattices @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['132'])).
% 46.47/46.67  thf('134', plain,
% 46.47/46.67      (![X0 : $i]:
% 46.47/46.67         ((v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v9_lattices @ X0)
% 46.47/46.67          | ((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 46.47/46.67              (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 46.47/46.67      inference('sup-', [status(thm)], ['118', '133'])).
% 46.47/46.67  thf('135', plain,
% 46.47/46.67      (![X0 : $i]:
% 46.47/46.67         (((k2_lattices @ X0 @ (k15_lattice3 @ X0 @ k1_xboole_0) @ 
% 46.47/46.67            (k5_lattices @ X0)) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 46.47/46.67          | ~ (v9_lattices @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0))),
% 46.47/46.67      inference('simplify', [status(thm)], ['134'])).
% 46.47/46.67  thf('136', plain,
% 46.47/46.67      (![X0 : $i]:
% 46.47/46.67         (((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0))
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (v13_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v9_lattices @ X0))),
% 46.47/46.67      inference('sup+', [status(thm)], ['117', '135'])).
% 46.47/46.67  thf('137', plain,
% 46.47/46.67      (![X0 : $i]:
% 46.47/46.67         (~ (v9_lattices @ X0)
% 46.47/46.67          | ~ (v8_lattices @ X0)
% 46.47/46.67          | ~ (v4_lattice3 @ X0)
% 46.47/46.67          | ~ (v10_lattices @ X0)
% 46.47/46.67          | ~ (v13_lattices @ X0)
% 46.47/46.67          | ~ (l1_lattices @ X0)
% 46.47/46.67          | ~ (l3_lattices @ X0)
% 46.47/46.67          | (v2_struct_0 @ X0)
% 46.47/46.67          | ((k5_lattices @ X0) = (k15_lattice3 @ X0 @ k1_xboole_0)))),
% 46.47/46.67      inference('simplify', [status(thm)], ['136'])).
% 46.47/46.67  thf('138', plain,
% 46.47/46.67      (((v2_struct_0 @ sk_A)
% 46.47/46.67        | ~ (v10_lattices @ sk_A)
% 46.47/46.67        | ~ (v13_lattices @ sk_A)
% 46.47/46.67        | ~ (l3_lattices @ sk_A)
% 46.47/46.67        | ((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('139', plain,
% 46.47/46.67      ((((k5_lattices @ sk_A) != (k15_lattice3 @ sk_A @ k1_xboole_0)))
% 46.47/46.67         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 46.47/46.67      inference('split', [status(esa)], ['138'])).
% 46.47/46.67  thf('140', plain,
% 46.47/46.67      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 46.47/46.67         | (v2_struct_0 @ sk_A)
% 46.47/46.67         | ~ (l3_lattices @ sk_A)
% 46.47/46.67         | ~ (l1_lattices @ sk_A)
% 46.47/46.67         | ~ (v13_lattices @ sk_A)
% 46.47/46.67         | ~ (v10_lattices @ sk_A)
% 46.47/46.67         | ~ (v4_lattice3 @ sk_A)
% 46.47/46.67         | ~ (v8_lattices @ sk_A)
% 46.47/46.67         | ~ (v9_lattices @ sk_A)))
% 46.47/46.67         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 46.47/46.67      inference('sup-', [status(thm)], ['137', '139'])).
% 46.47/46.67  thf('141', plain, ((l3_lattices @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('142', plain, ((l1_lattices @ sk_A)),
% 46.47/46.67      inference('sup-', [status(thm)], ['88', '89'])).
% 46.47/46.67  thf('143', plain, ((v10_lattices @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('144', plain, ((v4_lattice3 @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('145', plain, ((v8_lattices @ sk_A)),
% 46.47/46.67      inference('demod', [status(thm)], ['93', '94', '95'])).
% 46.47/46.67  thf('146', plain, ((v9_lattices @ sk_A)),
% 46.47/46.67      inference('demod', [status(thm)], ['99', '100', '101'])).
% 46.47/46.67  thf('147', plain,
% 46.47/46.67      (((((k5_lattices @ sk_A) != (k5_lattices @ sk_A))
% 46.47/46.67         | (v2_struct_0 @ sk_A)
% 46.47/46.67         | ~ (v13_lattices @ sk_A)))
% 46.47/46.67         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 46.47/46.67      inference('demod', [status(thm)],
% 46.47/46.67                ['140', '141', '142', '143', '144', '145', '146'])).
% 46.47/46.67  thf('148', plain,
% 46.47/46.67      (((~ (v13_lattices @ sk_A) | (v2_struct_0 @ sk_A)))
% 46.47/46.67         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 46.47/46.67      inference('simplify', [status(thm)], ['147'])).
% 46.47/46.67  thf('149', plain, (~ (v2_struct_0 @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('150', plain,
% 46.47/46.67      ((~ (v13_lattices @ sk_A))
% 46.47/46.67         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 46.47/46.67      inference('clc', [status(thm)], ['148', '149'])).
% 46.47/46.67  thf('151', plain,
% 46.47/46.67      (($false)
% 46.47/46.67         <= (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))))),
% 46.47/46.67      inference('sup-', [status(thm)], ['109', '150'])).
% 46.47/46.67  thf('152', plain, (((v2_struct_0 @ sk_A)) <= (((v2_struct_0 @ sk_A)))),
% 46.47/46.67      inference('split', [status(esa)], ['138'])).
% 46.47/46.67  thf('153', plain, (~ (v2_struct_0 @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('154', plain, (~ ((v2_struct_0 @ sk_A))),
% 46.47/46.67      inference('sup-', [status(thm)], ['152', '153'])).
% 46.47/46.67  thf('155', plain, ((l3_lattices @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('156', plain, ((~ (l3_lattices @ sk_A)) <= (~ ((l3_lattices @ sk_A)))),
% 46.47/46.67      inference('split', [status(esa)], ['138'])).
% 46.47/46.67  thf('157', plain, (((l3_lattices @ sk_A))),
% 46.47/46.67      inference('sup-', [status(thm)], ['155', '156'])).
% 46.47/46.67  thf('158', plain, ((v10_lattices @ sk_A)),
% 46.47/46.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 46.47/46.67  thf('159', plain, ((~ (v10_lattices @ sk_A)) <= (~ ((v10_lattices @ sk_A)))),
% 46.47/46.67      inference('split', [status(esa)], ['138'])).
% 46.47/46.67  thf('160', plain, (((v10_lattices @ sk_A))),
% 46.47/46.67      inference('sup-', [status(thm)], ['158', '159'])).
% 46.47/46.67  thf('161', plain, ((v13_lattices @ sk_A)),
% 46.47/46.67      inference('demod', [status(thm)],
% 46.47/46.67                ['84', '85', '86', '87', '90', '96', '102', '108'])).
% 46.47/46.67  thf('162', plain, ((~ (v13_lattices @ sk_A)) <= (~ ((v13_lattices @ sk_A)))),
% 46.47/46.67      inference('split', [status(esa)], ['138'])).
% 46.47/46.67  thf('163', plain, (((v13_lattices @ sk_A))),
% 46.47/46.67      inference('sup-', [status(thm)], ['161', '162'])).
% 46.47/46.67  thf('164', plain,
% 46.47/46.67      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0))) | 
% 46.47/46.67       ~ ((v13_lattices @ sk_A)) | ~ ((v10_lattices @ sk_A)) | 
% 46.47/46.67       ~ ((l3_lattices @ sk_A)) | ((v2_struct_0 @ sk_A))),
% 46.47/46.67      inference('split', [status(esa)], ['138'])).
% 46.47/46.67  thf('165', plain,
% 46.47/46.67      (~ (((k5_lattices @ sk_A) = (k15_lattice3 @ sk_A @ k1_xboole_0)))),
% 46.47/46.67      inference('sat_resolution*', [status(thm)],
% 46.47/46.67                ['154', '157', '160', '163', '164'])).
% 46.47/46.67  thf('166', plain, ($false),
% 46.47/46.67      inference('simpl_trail', [status(thm)], ['151', '165'])).
% 46.47/46.67  
% 46.47/46.67  % SZS output end Refutation
% 46.47/46.67  
% 46.47/46.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
