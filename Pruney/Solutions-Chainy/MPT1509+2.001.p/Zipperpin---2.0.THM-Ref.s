%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LDbgitiDZ7

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:33 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :  233 ( 553 expanded)
%              Number of leaves         :   46 ( 176 expanded)
%              Depth                    :   27
%              Number of atoms          : 2008 (8652 expanded)
%              Number of equality atoms :   74 ( 509 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v9_lattices_type,type,(
    v9_lattices: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(k15_lattice3_type,type,(
    k15_lattice3: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r3_lattice3_type,type,(
    r3_lattice3: $i > $i > $i > $o )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_lattices_type,type,(
    v4_lattices: $i > $o )).

thf(v7_lattices_type,type,(
    v7_lattices: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v4_lattice3_type,type,(
    v4_lattice3: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_lattices_type,type,(
    k1_lattices: $i > $i > $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(v6_lattices_type,type,(
    v6_lattices: $i > $o )).

thf(v5_lattices_type,type,(
    v5_lattices: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_lattices_type,type,(
    r1_lattices: $i > $i > $i > $o )).

thf(k2_lattices_type,type,(
    k2_lattices: $i > $i > $i > $i )).

thf(v8_lattices_type,type,(
    v8_lattices: $i > $o )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(k16_lattice3_type,type,(
    k16_lattice3: $i > $i > $i )).

thf(r4_lattice3_type,type,(
    r4_lattice3: $i > $i > $i > $o )).

thf(t43_lattice3,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( v4_lattice3 @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( ( k15_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
                = B )
              & ( ( k16_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) )
                = B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_lattice3])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X6: $i,X7: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X7 @ X6 )
      | ( ( k6_domain_1 @ X6 @ X7 )
        = ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
      = ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k15_lattice3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
     != sk_B_2 )
    | ( ( k16_lattice3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
     != sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( ( k15_lattice3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
     != sk_B_2 )
   <= ( ( k15_lattice3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
     != sk_B_2 ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( ( ( k15_lattice3 @ sk_A @ ( k1_tarski @ sk_B_2 ) )
       != sk_B_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k15_lattice3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
     != sk_B_2 ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('9',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X20 ) )
      | ( ( k2_lattices @ X20 @ X19 @ X21 )
       != X19 )
      | ( r1_lattices @ X20 @ X19 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( u1_struct_0 @ X20 ) )
      | ~ ( l3_lattices @ X20 )
      | ~ ( v9_lattices @ X20 )
      | ~ ( v8_lattices @ X20 )
      | ( v2_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t21_lattices])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v8_lattices @ sk_A )
      | ~ ( v9_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B_2 @ X0 )
      | ( ( k2_lattices @ sk_A @ sk_B_2 @ X0 )
       != sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

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

thf('11',plain,(
    ! [X8: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ( v8_lattices @ X8 )
      | ~ ( l3_lattices @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v8_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X8: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ( v9_lattices @ X8 )
      | ~ ( l3_lattices @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v9_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r1_lattices @ sk_A @ sk_B_2 @ X0 )
      | ( ( k2_lattices @ sk_A @ sk_B_2 @ X0 )
       != sk_B_2 ) ) ),
    inference(demod,[status(thm)],['10','16','22','23'])).

thf('25',plain,
    ( ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_B_2 )
     != sk_B_2 )
    | ( r1_lattices @ sk_A @ sk_B_2 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('28',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v9_lattices @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ( ( k2_lattices @ X9 @ X11 @ ( k1_lattices @ X9 @ X11 @ X10 ) )
        = X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l3_lattices @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d9_lattices])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_B_2 ) )
        = X0 )
      | ~ ( v9_lattices @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_B_2 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k2_lattices @ sk_A @ X0 @ ( k1_lattices @ sk_A @ X0 @ sk_B_2 ) )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_lattices @ sk_A @ sk_B_2 @ ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t17_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v6_lattices @ A )
        & ( v8_lattices @ A )
        & ( v9_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k1_lattices @ A @ B @ B )
            = B ) ) ) )).

thf('37',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X18 ) )
      | ( ( k1_lattices @ X18 @ X17 @ X17 )
        = X17 )
      | ~ ( l3_lattices @ X18 )
      | ~ ( v9_lattices @ X18 )
      | ~ ( v8_lattices @ X18 )
      | ~ ( v6_lattices @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t17_lattices])).

thf('38',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v6_lattices @ sk_A )
    | ~ ( v8_lattices @ sk_A )
    | ~ ( v9_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 )
      = sk_B_2 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X8: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ( v6_lattices @ X8 )
      | ~ ( l3_lattices @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('40',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v6_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    v6_lattices @ sk_A ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    v8_lattices @ sk_A ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('46',plain,(
    v9_lattices @ sk_A ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('47',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 )
      = sk_B_2 ) ),
    inference(demod,[status(thm)],['38','44','45','46','47'])).

thf('49',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k1_lattices @ sk_A @ sk_B_2 @ sk_B_2 )
    = sk_B_2 ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k2_lattices @ sk_A @ sk_B_2 @ sk_B_2 )
    = sk_B_2 ),
    inference(demod,[status(thm)],['35','50'])).

thf('52',plain,
    ( ( sk_B_2 != sk_B_2 )
    | ( r1_lattices @ sk_A @ sk_B_2 @ sk_B_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['25','51'])).

thf('53',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    r1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d16_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( r3_lattice3 @ A @ B @ C )
            <=> ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) )
                 => ( ( r2_hidden @ D @ C )
                   => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) )).

thf('57',plain,(
    ! [X29: $i,X30: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ( r2_hidden @ ( sk_D @ X33 @ X29 @ X30 ) @ X33 )
      | ( r3_lattice3 @ X30 @ X29 @ X33 )
      | ~ ( l3_lattices @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B_2 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B_2 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B_2 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ sk_B_2 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ sk_B_2 @ sk_A ) @ X0 )
      | ( r3_lattice3 @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('63',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('64',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B_2 @ ( k1_tarski @ X0 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ sk_B_2 @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X29: $i,X30: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( u1_struct_0 @ X30 ) )
      | ~ ( r1_lattices @ X30 @ X29 @ ( sk_D @ X33 @ X29 @ X30 ) )
      | ( r3_lattice3 @ X30 @ X29 @ X33 )
      | ~ ( l3_lattices @ X30 )
      | ( v2_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d16_lattice3])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B_2 @ X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B_2 @ ( sk_D @ X0 @ sk_B_2 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r3_lattice3 @ sk_A @ sk_B_2 @ X0 )
      | ~ ( r1_lattices @ sk_A @ sk_B_2 @ ( sk_D @ X0 @ sk_B_2 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B_2 @ ( sk_D @ X0 @ sk_B_2 @ sk_A ) )
      | ( r3_lattice3 @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ sk_B_2 @ X0 )
      | ( r3_lattice3 @ sk_A @ sk_B_2 @ ( k1_tarski @ X0 ) )
      | ( r3_lattice3 @ sk_A @ sk_B_2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['65','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r3_lattice3 @ sk_A @ sk_B_2 @ ( k1_tarski @ X0 ) )
      | ~ ( r1_lattices @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    r3_lattice3 @ sk_A @ sk_B_2 @ ( k1_tarski @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['55','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t42_lattice3,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( v4_lattice3 @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( ( r2_hidden @ B @ C )
                & ( r3_lattice3 @ A @ B @ C ) )
             => ( ( k16_lattice3 @ A @ C )
                = B ) ) ) ) )).

thf('77',plain,(
    ! [X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( u1_struct_0 @ X49 ) )
      | ( ( k16_lattice3 @ X49 @ X50 )
        = X48 )
      | ~ ( r3_lattice3 @ X49 @ X48 @ X50 )
      | ~ ( r2_hidden @ X48 @ X50 )
      | ~ ( l3_lattices @ X49 )
      | ~ ( v4_lattice3 @ X49 )
      | ~ ( v10_lattices @ X49 )
      | ( v2_struct_0 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t42_lattice3])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( r2_hidden @ sk_B_2 @ X0 )
      | ~ ( r3_lattice3 @ sk_A @ sk_B_2 @ X0 )
      | ( ( k16_lattice3 @ sk_A @ X0 )
        = sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r2_hidden @ sk_B_2 @ X0 )
      | ~ ( r3_lattice3 @ sk_A @ sk_B_2 @ X0 )
      | ( ( k16_lattice3 @ sk_A @ X0 )
        = sk_B_2 ) ) ),
    inference(demod,[status(thm)],['78','79','80','81'])).

thf('83',plain,
    ( ( ( k16_lattice3 @ sk_A @ ( k1_tarski @ sk_B_2 ) )
      = sk_B_2 )
    | ~ ( r2_hidden @ sk_B_2 @ ( k1_tarski @ sk_B_2 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['75','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('85',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,
    ( ( ( k16_lattice3 @ sk_A @ ( k1_tarski @ sk_B_2 ) )
      = sk_B_2 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['83','85'])).

thf('87',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k16_lattice3 @ sk_A @ ( k1_tarski @ sk_B_2 ) )
    = sk_B_2 ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 )
      = ( k1_tarski @ sk_B_2 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('90',plain,
    ( ( ( k16_lattice3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
     != sk_B_2 )
   <= ( ( k16_lattice3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
     != sk_B_2 ) ),
    inference(split,[status(esa)],['4'])).

thf('91',plain,
    ( ( ( ( k16_lattice3 @ sk_A @ ( k1_tarski @ sk_B_2 ) )
       != sk_B_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k16_lattice3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
     != sk_B_2 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( sk_B_2 != sk_B_2 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ( k16_lattice3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
     != sk_B_2 ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ( k16_lattice3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
     != sk_B_2 ) ),
    inference(simplify,[status(thm)],['92'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('94',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('95',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ( k16_lattice3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
     != sk_B_2 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('97',plain,(
    ! [X13: $i] :
      ( ( l2_lattices @ X13 )
      | ~ ( l3_lattices @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('98',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['96','97'])).

thf(dt_l2_lattices,axiom,(
    ! [A: $i] :
      ( ( l2_lattices @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('99',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l2_lattices @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l2_lattices])).

thf('100',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ( k16_lattice3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
     != sk_B_2 ) ),
    inference(demod,[status(thm)],['95','100'])).

thf('102',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k16_lattice3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,
    ( ( ( k15_lattice3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
     != sk_B_2 )
    | ( ( k16_lattice3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
     != sk_B_2 ) ),
    inference(split,[status(esa)],['4'])).

thf('105',plain,(
    ( k15_lattice3 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_2 ) )
 != sk_B_2 ),
    inference('sat_resolution*',[status(thm)],['103','104'])).

thf('106',plain,
    ( ( ( k15_lattice3 @ sk_A @ ( k1_tarski @ sk_B_2 ) )
     != sk_B_2 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['6','105'])).

thf('107',plain,(
    r1_lattices @ sk_A @ sk_B_2 @ sk_B_2 ),
    inference(clc,[status(thm)],['53','54'])).

thf('108',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('109',plain,(
    ! [X34: $i,X35: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X35 ) )
      | ( r2_hidden @ ( sk_D_1 @ X38 @ X34 @ X35 ) @ X38 )
      | ( r4_lattice3 @ X35 @ X34 @ X38 )
      | ~ ( l3_lattices @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B_2 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B_2 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B_2 @ X0 )
      | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B_2 @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B_2 @ sk_A ) @ X0 )
      | ( r4_lattice3 @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B_2 @ ( k1_tarski @ X0 ) )
      | ( ( sk_D_1 @ ( k1_tarski @ X0 ) @ sk_B_2 @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    ! [X34: $i,X35: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X35 ) )
      | ~ ( r1_lattices @ X35 @ ( sk_D_1 @ X38 @ X34 @ X35 ) @ X34 )
      | ( r4_lattice3 @ X35 @ X34 @ X38 )
      | ~ ( l3_lattices @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B_2 @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B_2 @ sk_A ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r4_lattice3 @ sk_A @ sk_B_2 @ X0 )
      | ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B_2 @ sk_A ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ ( sk_D_1 @ X0 @ sk_B_2 @ sk_A ) @ sk_B_2 )
      | ( r4_lattice3 @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( r1_lattices @ sk_A @ X0 @ sk_B_2 )
      | ( r4_lattice3 @ sk_A @ sk_B_2 @ ( k1_tarski @ X0 ) )
      | ( r4_lattice3 @ sk_A @ sk_B_2 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['116','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( r4_lattice3 @ sk_A @ sk_B_2 @ ( k1_tarski @ X0 ) )
      | ~ ( r1_lattices @ sk_A @ X0 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['124'])).

thf('126',plain,(
    r4_lattice3 @ sk_A @ sk_B_2 @ ( k1_tarski @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['107','125'])).

thf('127',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k15_lattice3,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l3_lattices @ A ) )
     => ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ) )).

thf('128',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l3_lattices @ X46 )
      | ( v2_struct_0 @ X46 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X46 @ X47 ) @ ( u1_struct_0 @ X46 ) ) ) ),
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

thf('129',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( v10_lattices @ X39 )
      | ~ ( v4_lattice3 @ X39 )
      | ~ ( l3_lattices @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X39 ) )
      | ( X40
       != ( k15_lattice3 @ X39 @ X41 ) )
      | ~ ( r4_lattice3 @ X39 @ X42 @ X41 )
      | ( r1_lattices @ X39 @ X40 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X39 ) )
      | ~ ( l3_lattices @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('130',plain,(
    ! [X39: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( u1_struct_0 @ X39 ) )
      | ( r1_lattices @ X39 @ ( k15_lattice3 @ X39 @ X41 ) @ X42 )
      | ~ ( r4_lattice3 @ X39 @ X42 @ X41 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X39 @ X41 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( l3_lattices @ X39 )
      | ~ ( v4_lattice3 @ X39 )
      | ~ ( v10_lattices @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
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
    inference('sup-',[status(thm)],['128','130'])).

thf('132',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r4_lattice3 @ X0 @ X2 @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B_2 @ X0 )
      | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['127','132'])).

thf('134',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( r4_lattice3 @ sk_A @ sk_B_2 @ X0 )
      | ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['133','134','135','136'])).

thf('138',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ X0 ) @ sk_B_2 )
      | ~ ( r4_lattice3 @ sk_A @ sk_B_2 @ X0 ) ) ),
    inference(clc,[status(thm)],['137','138'])).

thf('140',plain,(
    r1_lattices @ sk_A @ ( k15_lattice3 @ sk_A @ ( k1_tarski @ sk_B_2 ) ) @ sk_B_2 ),
    inference('sup-',[status(thm)],['126','139'])).

thf('141',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l3_lattices @ X46 )
      | ( v2_struct_0 @ X46 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X46 @ X47 ) @ ( u1_struct_0 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf(t26_lattices,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v4_lattices @ A )
        & ( l2_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( ( r1_lattices @ A @ B @ C )
                  & ( r1_lattices @ A @ C @ B ) )
               => ( B = C ) ) ) ) ) )).

thf('142',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X23 ) )
      | ~ ( r1_lattices @ X23 @ X22 @ X24 )
      | ~ ( r1_lattices @ X23 @ X24 @ X22 )
      | ( X22 = X24 )
      | ~ ( m1_subset_1 @ X24 @ ( u1_struct_0 @ X23 ) )
      | ~ ( l2_lattices @ X23 )
      | ~ ( v4_lattices @ X23 )
      | ( v2_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t26_lattices])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( l2_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = X2 )
      | ~ ( r1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_lattices @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
      | ( ( k15_lattice3 @ X0 @ X1 )
        = X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l2_lattices @ X0 )
      | ~ ( v4_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ~ ( v4_lattices @ sk_A )
    | ~ ( l2_lattices @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k15_lattice3 @ sk_A @ ( k1_tarski @ sk_B_2 ) )
      = sk_B_2 )
    | ~ ( r1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['140','144'])).

thf('146',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X8: $i] :
      ( ( v2_struct_0 @ X8 )
      | ~ ( v10_lattices @ X8 )
      | ( v4_lattices @ X8 )
      | ~ ( l3_lattices @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc1_lattices])).

thf('148',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('149',plain,
    ( ~ ( l3_lattices @ sk_A )
    | ( v4_lattices @ sk_A )
    | ~ ( v10_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v4_lattices @ sk_A ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['96','97'])).

thf('154',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('156',plain,(
    m1_subset_1 @ sk_B_2 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l3_lattices @ X46 )
      | ( v2_struct_0 @ X46 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X46 @ X47 ) @ ( u1_struct_0 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('158',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( v2_struct_0 @ X39 )
      | ~ ( v10_lattices @ X39 )
      | ~ ( v4_lattice3 @ X39 )
      | ~ ( l3_lattices @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X39 ) )
      | ( X40
       != ( k15_lattice3 @ X39 @ X41 ) )
      | ( r4_lattice3 @ X39 @ X40 @ X41 )
      | ~ ( l3_lattices @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d21_lattice3])).

thf('159',plain,(
    ! [X39: $i,X41: $i] :
      ( ( r4_lattice3 @ X39 @ ( k15_lattice3 @ X39 @ X41 ) @ X41 )
      | ~ ( m1_subset_1 @ ( k15_lattice3 @ X39 @ X41 ) @ ( u1_struct_0 @ X39 ) )
      | ~ ( l3_lattices @ X39 )
      | ~ ( v4_lattice3 @ X39 )
      | ~ ( v10_lattices @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['157','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X1 )
      | ~ ( v4_lattice3 @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( l3_lattices @ X46 )
      | ( v2_struct_0 @ X46 )
      | ( m1_subset_1 @ ( k15_lattice3 @ X46 @ X47 ) @ ( u1_struct_0 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k15_lattice3])).

thf('163',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( u1_struct_0 @ X35 ) )
      | ~ ( r4_lattice3 @ X35 @ X34 @ X36 )
      | ~ ( r2_hidden @ X37 @ X36 )
      | ( r1_lattices @ X35 @ X37 @ X34 )
      | ~ ( m1_subset_1 @ X37 @ ( u1_struct_0 @ X35 ) )
      | ~ ( l3_lattices @ X35 )
      | ( v2_struct_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d17_lattice3])).

thf('164',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l3_lattices @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['162','163'])).

thf('165',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r4_lattice3 @ X0 @ ( k15_lattice3 @ X0 @ X1 ) @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ( r1_lattices @ X0 @ X2 @ ( k15_lattice3 @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( v4_lattice3 @ X1 )
      | ( v2_struct_0 @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ( r1_lattices @ X1 @ X2 @ ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['161','165'])).

thf('167',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ( r1_lattices @ X1 @ X2 @ ( k15_lattice3 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X1 ) )
      | ~ ( v4_lattice3 @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ~ ( l3_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['166'])).

thf('168',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( v4_lattice3 @ sk_A )
      | ( r1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['156','167'])).

thf('169',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('171',plain,(
    v4_lattice3 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ sk_B_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['168','169','170','171'])).

thf('173',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B_2 @ X0 )
      | ( r1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ X0 ) ) ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    r1_lattices @ sk_A @ sk_B_2 @ ( k15_lattice3 @ sk_A @ ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['155','174'])).

thf('176',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k15_lattice3 @ sk_A @ ( k1_tarski @ sk_B_2 ) )
      = sk_B_2 ) ),
    inference(demod,[status(thm)],['145','146','152','153','154','175'])).

thf('177',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( k15_lattice3 @ sk_A @ ( k1_tarski @ sk_B_2 ) )
    = sk_B_2 ),
    inference(clc,[status(thm)],['176','177'])).

thf('179',plain,
    ( ( sk_B_2 != sk_B_2 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['106','178'])).

thf('180',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('182',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['98','99'])).

thf('184',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['182','183'])).

thf('185',plain,(
    $false ),
    inference(demod,[status(thm)],['0','184'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.LDbgitiDZ7
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:16:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.53/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.53/0.75  % Solved by: fo/fo7.sh
% 0.53/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.75  % done 252 iterations in 0.271s
% 0.53/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.53/0.75  % SZS output start Refutation
% 0.53/0.75  thf(v9_lattices_type, type, v9_lattices: $i > $o).
% 0.53/0.75  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.53/0.75  thf(l1_lattices_type, type, l1_lattices: $i > $o).
% 0.53/0.75  thf(k15_lattice3_type, type, k15_lattice3: $i > $i > $i).
% 0.53/0.75  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.53/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.53/0.75  thf(r3_lattice3_type, type, r3_lattice3: $i > $i > $i > $o).
% 0.53/0.75  thf(l3_lattices_type, type, l3_lattices: $i > $o).
% 0.53/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.75  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.53/0.75  thf(v4_lattices_type, type, v4_lattices: $i > $o).
% 0.53/0.75  thf(v7_lattices_type, type, v7_lattices: $i > $o).
% 0.53/0.75  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.53/0.75  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.53/0.75  thf(v4_lattice3_type, type, v4_lattice3: $i > $o).
% 0.53/0.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.53/0.75  thf(k1_lattices_type, type, k1_lattices: $i > $i > $i > $i).
% 0.53/0.75  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.53/0.75  thf(l2_lattices_type, type, l2_lattices: $i > $o).
% 0.53/0.75  thf(v6_lattices_type, type, v6_lattices: $i > $o).
% 0.53/0.75  thf(v5_lattices_type, type, v5_lattices: $i > $o).
% 0.53/0.75  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.53/0.75  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.53/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.53/0.75  thf(r1_lattices_type, type, r1_lattices: $i > $i > $i > $o).
% 0.53/0.75  thf(k2_lattices_type, type, k2_lattices: $i > $i > $i > $i).
% 0.53/0.75  thf(v8_lattices_type, type, v8_lattices: $i > $o).
% 0.53/0.75  thf(v10_lattices_type, type, v10_lattices: $i > $o).
% 0.53/0.75  thf(k16_lattice3_type, type, k16_lattice3: $i > $i > $i).
% 0.53/0.75  thf(r4_lattice3_type, type, r4_lattice3: $i > $i > $i > $o).
% 0.53/0.75  thf(t43_lattice3, conjecture,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.53/0.75         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75           ( ( ( k15_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.53/0.75               ( B ) ) & 
% 0.53/0.75             ( ( k16_lattice3 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.53/0.75               ( B ) ) ) ) ) ))).
% 0.53/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.75    (~( ![A:$i]:
% 0.53/0.75        ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.53/0.75            ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.53/0.75          ( ![B:$i]:
% 0.53/0.75            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75              ( ( ( k15_lattice3 @
% 0.53/0.75                    A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.53/0.75                  ( B ) ) & 
% 0.53/0.75                ( ( k16_lattice3 @
% 0.53/0.75                    A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) =
% 0.53/0.75                  ( B ) ) ) ) ) ) )),
% 0.53/0.75    inference('cnf.neg', [status(esa)], [t43_lattice3])).
% 0.53/0.75  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('1', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(redefinition_k6_domain_1, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.53/0.75       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.53/0.75  thf('2', plain,
% 0.53/0.75      (![X6 : $i, X7 : $i]:
% 0.53/0.75         ((v1_xboole_0 @ X6)
% 0.53/0.75          | ~ (m1_subset_1 @ X7 @ X6)
% 0.53/0.75          | ((k6_domain_1 @ X6 @ X7) = (k1_tarski @ X7)))),
% 0.53/0.75      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.53/0.75  thf('3', plain,
% 0.53/0.75      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) = (k1_tarski @ sk_B_2))
% 0.53/0.75        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['1', '2'])).
% 0.53/0.75  thf('4', plain,
% 0.53/0.75      ((((k15_lattice3 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.53/0.75          != (sk_B_2))
% 0.53/0.75        | ((k16_lattice3 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.53/0.75            != (sk_B_2)))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('5', plain,
% 0.53/0.75      ((((k15_lattice3 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.53/0.75          != (sk_B_2)))
% 0.53/0.75         <= (~
% 0.53/0.75             (((k15_lattice3 @ sk_A @ 
% 0.53/0.75                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)) = (sk_B_2))))),
% 0.53/0.75      inference('split', [status(esa)], ['4'])).
% 0.53/0.75  thf('6', plain,
% 0.53/0.75      (((((k15_lattice3 @ sk_A @ (k1_tarski @ sk_B_2)) != (sk_B_2))
% 0.53/0.75         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.53/0.75         <= (~
% 0.53/0.75             (((k15_lattice3 @ sk_A @ 
% 0.53/0.75                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)) = (sk_B_2))))),
% 0.53/0.75      inference('sup-', [status(thm)], ['3', '5'])).
% 0.53/0.75  thf('7', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('8', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(t21_lattices, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v8_lattices @ A ) & 
% 0.53/0.75         ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75           ( ![C:$i]:
% 0.53/0.75             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75               ( ( r1_lattices @ A @ B @ C ) <=>
% 0.53/0.75                 ( ( k2_lattices @ A @ B @ C ) = ( B ) ) ) ) ) ) ) ))).
% 0.53/0.75  thf('9', plain,
% 0.53/0.75      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X20))
% 0.53/0.75          | ((k2_lattices @ X20 @ X19 @ X21) != (X19))
% 0.53/0.75          | (r1_lattices @ X20 @ X19 @ X21)
% 0.53/0.75          | ~ (m1_subset_1 @ X21 @ (u1_struct_0 @ X20))
% 0.53/0.75          | ~ (l3_lattices @ X20)
% 0.53/0.75          | ~ (v9_lattices @ X20)
% 0.53/0.75          | ~ (v8_lattices @ X20)
% 0.53/0.75          | (v2_struct_0 @ X20))),
% 0.53/0.75      inference('cnf', [status(esa)], [t21_lattices])).
% 0.53/0.75  thf('10', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (v8_lattices @ sk_A)
% 0.53/0.75          | ~ (v9_lattices @ sk_A)
% 0.53/0.75          | ~ (l3_lattices @ sk_A)
% 0.53/0.75          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.53/0.75          | (r1_lattices @ sk_A @ sk_B_2 @ X0)
% 0.53/0.75          | ((k2_lattices @ sk_A @ sk_B_2 @ X0) != (sk_B_2)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.53/0.75  thf(cc1_lattices, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( l3_lattices @ A ) =>
% 0.53/0.75       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) ) =>
% 0.53/0.75         ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & 
% 0.53/0.75           ( v5_lattices @ A ) & ( v6_lattices @ A ) & ( v7_lattices @ A ) & 
% 0.53/0.75           ( v8_lattices @ A ) & ( v9_lattices @ A ) ) ) ))).
% 0.53/0.75  thf('11', plain,
% 0.53/0.75      (![X8 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X8)
% 0.53/0.75          | ~ (v10_lattices @ X8)
% 0.53/0.75          | (v8_lattices @ X8)
% 0.53/0.75          | ~ (l3_lattices @ X8))),
% 0.53/0.75      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.53/0.75  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('13', plain,
% 0.53/0.75      ((~ (l3_lattices @ sk_A) | (v8_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['11', '12'])).
% 0.53/0.75  thf('14', plain, ((l3_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('15', plain, ((v10_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('16', plain, ((v8_lattices @ sk_A)),
% 0.53/0.75      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.53/0.75  thf('17', plain,
% 0.53/0.75      (![X8 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X8)
% 0.53/0.75          | ~ (v10_lattices @ X8)
% 0.53/0.75          | (v9_lattices @ X8)
% 0.53/0.75          | ~ (l3_lattices @ X8))),
% 0.53/0.75      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.53/0.75  thf('18', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('19', plain,
% 0.53/0.75      ((~ (l3_lattices @ sk_A) | (v9_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['17', '18'])).
% 0.53/0.75  thf('20', plain, ((l3_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('21', plain, ((v10_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('22', plain, ((v9_lattices @ sk_A)),
% 0.53/0.75      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.53/0.75  thf('23', plain, ((l3_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('24', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.53/0.75          | (r1_lattices @ sk_A @ sk_B_2 @ X0)
% 0.53/0.75          | ((k2_lattices @ sk_A @ sk_B_2 @ X0) != (sk_B_2)))),
% 0.53/0.75      inference('demod', [status(thm)], ['10', '16', '22', '23'])).
% 0.53/0.75  thf('25', plain,
% 0.53/0.75      ((((k2_lattices @ sk_A @ sk_B_2 @ sk_B_2) != (sk_B_2))
% 0.53/0.75        | (r1_lattices @ sk_A @ sk_B_2 @ sk_B_2)
% 0.53/0.75        | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['7', '24'])).
% 0.53/0.75  thf('26', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('27', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(d9_lattices, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.53/0.75       ( ( v9_lattices @ A ) <=>
% 0.53/0.75         ( ![B:$i]:
% 0.53/0.75           ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75             ( ![C:$i]:
% 0.53/0.75               ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75                 ( ( k2_lattices @ A @ B @ ( k1_lattices @ A @ B @ C ) ) =
% 0.53/0.75                   ( B ) ) ) ) ) ) ) ))).
% 0.53/0.75  thf('28', plain,
% 0.53/0.75      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.53/0.75         (~ (v9_lattices @ X9)
% 0.53/0.75          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 0.53/0.75          | ((k2_lattices @ X9 @ X11 @ (k1_lattices @ X9 @ X11 @ X10)) = (X11))
% 0.53/0.75          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X9))
% 0.53/0.75          | ~ (l3_lattices @ X9)
% 0.53/0.75          | (v2_struct_0 @ X9))),
% 0.53/0.75      inference('cnf', [status(esa)], [d9_lattices])).
% 0.53/0.75  thf('29', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (l3_lattices @ sk_A)
% 0.53/0.75          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.53/0.75          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_B_2))
% 0.53/0.75              = (X0))
% 0.53/0.75          | ~ (v9_lattices @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['27', '28'])).
% 0.53/0.75  thf('30', plain, ((l3_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('31', plain, ((v9_lattices @ sk_A)),
% 0.53/0.75      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.53/0.75  thf('32', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.53/0.75          | ((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_B_2))
% 0.53/0.75              = (X0)))),
% 0.53/0.75      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.53/0.75  thf('33', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('34', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (((k2_lattices @ sk_A @ X0 @ (k1_lattices @ sk_A @ X0 @ sk_B_2))
% 0.53/0.75            = (X0))
% 0.53/0.75          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('clc', [status(thm)], ['32', '33'])).
% 0.53/0.75  thf('35', plain,
% 0.53/0.75      (((k2_lattices @ sk_A @ sk_B_2 @ (k1_lattices @ sk_A @ sk_B_2 @ sk_B_2))
% 0.53/0.75         = (sk_B_2))),
% 0.53/0.75      inference('sup-', [status(thm)], ['26', '34'])).
% 0.53/0.75  thf('36', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(t17_lattices, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v6_lattices @ A ) & 
% 0.53/0.75         ( v8_lattices @ A ) & ( v9_lattices @ A ) & ( l3_lattices @ A ) ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75           ( ( k1_lattices @ A @ B @ B ) = ( B ) ) ) ) ))).
% 0.53/0.75  thf('37', plain,
% 0.53/0.75      (![X17 : $i, X18 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X18))
% 0.53/0.75          | ((k1_lattices @ X18 @ X17 @ X17) = (X17))
% 0.53/0.75          | ~ (l3_lattices @ X18)
% 0.53/0.75          | ~ (v9_lattices @ X18)
% 0.53/0.75          | ~ (v8_lattices @ X18)
% 0.53/0.75          | ~ (v6_lattices @ X18)
% 0.53/0.75          | (v2_struct_0 @ X18))),
% 0.53/0.75      inference('cnf', [status(esa)], [t17_lattices])).
% 0.53/0.75  thf('38', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_A)
% 0.53/0.75        | ~ (v6_lattices @ sk_A)
% 0.53/0.75        | ~ (v8_lattices @ sk_A)
% 0.53/0.75        | ~ (v9_lattices @ sk_A)
% 0.53/0.75        | ~ (l3_lattices @ sk_A)
% 0.53/0.75        | ((k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) = (sk_B_2)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['36', '37'])).
% 0.53/0.75  thf('39', plain,
% 0.53/0.75      (![X8 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X8)
% 0.53/0.75          | ~ (v10_lattices @ X8)
% 0.53/0.75          | (v6_lattices @ X8)
% 0.53/0.75          | ~ (l3_lattices @ X8))),
% 0.53/0.75      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.53/0.75  thf('40', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('41', plain,
% 0.53/0.75      ((~ (l3_lattices @ sk_A) | (v6_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['39', '40'])).
% 0.53/0.75  thf('42', plain, ((l3_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('43', plain, ((v10_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('44', plain, ((v6_lattices @ sk_A)),
% 0.53/0.75      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.53/0.75  thf('45', plain, ((v8_lattices @ sk_A)),
% 0.53/0.75      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.53/0.75  thf('46', plain, ((v9_lattices @ sk_A)),
% 0.53/0.75      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.53/0.75  thf('47', plain, ((l3_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('48', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_A)
% 0.53/0.75        | ((k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) = (sk_B_2)))),
% 0.53/0.75      inference('demod', [status(thm)], ['38', '44', '45', '46', '47'])).
% 0.53/0.75  thf('49', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('50', plain, (((k1_lattices @ sk_A @ sk_B_2 @ sk_B_2) = (sk_B_2))),
% 0.53/0.75      inference('clc', [status(thm)], ['48', '49'])).
% 0.53/0.75  thf('51', plain, (((k2_lattices @ sk_A @ sk_B_2 @ sk_B_2) = (sk_B_2))),
% 0.53/0.75      inference('demod', [status(thm)], ['35', '50'])).
% 0.53/0.75  thf('52', plain,
% 0.53/0.75      ((((sk_B_2) != (sk_B_2))
% 0.53/0.75        | (r1_lattices @ sk_A @ sk_B_2 @ sk_B_2)
% 0.53/0.75        | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('demod', [status(thm)], ['25', '51'])).
% 0.53/0.75  thf('53', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_A) | (r1_lattices @ sk_A @ sk_B_2 @ sk_B_2))),
% 0.53/0.75      inference('simplify', [status(thm)], ['52'])).
% 0.53/0.75  thf('54', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('55', plain, ((r1_lattices @ sk_A @ sk_B_2 @ sk_B_2)),
% 0.53/0.75      inference('clc', [status(thm)], ['53', '54'])).
% 0.53/0.75  thf('56', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(d16_lattice3, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75           ( ![C:$i]:
% 0.53/0.75             ( ( r3_lattice3 @ A @ B @ C ) <=>
% 0.53/0.75               ( ![D:$i]:
% 0.53/0.75                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.53/0.75  thf('57', plain,
% 0.53/0.75      (![X29 : $i, X30 : $i, X33 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 0.53/0.75          | (r2_hidden @ (sk_D @ X33 @ X29 @ X30) @ X33)
% 0.53/0.75          | (r3_lattice3 @ X30 @ X29 @ X33)
% 0.53/0.75          | ~ (l3_lattices @ X30)
% 0.53/0.75          | (v2_struct_0 @ X30))),
% 0.53/0.75      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.53/0.75  thf('58', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (l3_lattices @ sk_A)
% 0.53/0.75          | (r3_lattice3 @ sk_A @ sk_B_2 @ X0)
% 0.53/0.75          | (r2_hidden @ (sk_D @ X0 @ sk_B_2 @ sk_A) @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['56', '57'])).
% 0.53/0.75  thf('59', plain, ((l3_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('60', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | (r3_lattice3 @ sk_A @ sk_B_2 @ X0)
% 0.53/0.75          | (r2_hidden @ (sk_D @ X0 @ sk_B_2 @ sk_A) @ X0))),
% 0.53/0.75      inference('demod', [status(thm)], ['58', '59'])).
% 0.53/0.75  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('62', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r2_hidden @ (sk_D @ X0 @ sk_B_2 @ sk_A) @ X0)
% 0.53/0.75          | (r3_lattice3 @ sk_A @ sk_B_2 @ X0))),
% 0.53/0.75      inference('clc', [status(thm)], ['60', '61'])).
% 0.53/0.75  thf(d1_tarski, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.53/0.75       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.53/0.75  thf('63', plain,
% 0.53/0.75      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.53/0.75      inference('cnf', [status(esa)], [d1_tarski])).
% 0.53/0.75  thf('64', plain,
% 0.53/0.75      (![X0 : $i, X3 : $i]:
% 0.53/0.75         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.53/0.75      inference('simplify', [status(thm)], ['63'])).
% 0.53/0.75  thf('65', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r3_lattice3 @ sk_A @ sk_B_2 @ (k1_tarski @ X0))
% 0.53/0.75          | ((sk_D @ (k1_tarski @ X0) @ sk_B_2 @ sk_A) = (X0)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['62', '64'])).
% 0.53/0.75  thf('66', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('67', plain,
% 0.53/0.75      (![X29 : $i, X30 : $i, X33 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X29 @ (u1_struct_0 @ X30))
% 0.53/0.75          | ~ (r1_lattices @ X30 @ X29 @ (sk_D @ X33 @ X29 @ X30))
% 0.53/0.75          | (r3_lattice3 @ X30 @ X29 @ X33)
% 0.53/0.75          | ~ (l3_lattices @ X30)
% 0.53/0.75          | (v2_struct_0 @ X30))),
% 0.53/0.75      inference('cnf', [status(esa)], [d16_lattice3])).
% 0.53/0.75  thf('68', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (l3_lattices @ sk_A)
% 0.53/0.75          | (r3_lattice3 @ sk_A @ sk_B_2 @ X0)
% 0.53/0.75          | ~ (r1_lattices @ sk_A @ sk_B_2 @ (sk_D @ X0 @ sk_B_2 @ sk_A)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['66', '67'])).
% 0.53/0.75  thf('69', plain, ((l3_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('70', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | (r3_lattice3 @ sk_A @ sk_B_2 @ X0)
% 0.53/0.75          | ~ (r1_lattices @ sk_A @ sk_B_2 @ (sk_D @ X0 @ sk_B_2 @ sk_A)))),
% 0.53/0.75      inference('demod', [status(thm)], ['68', '69'])).
% 0.53/0.75  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('72', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (r1_lattices @ sk_A @ sk_B_2 @ (sk_D @ X0 @ sk_B_2 @ sk_A))
% 0.53/0.75          | (r3_lattice3 @ sk_A @ sk_B_2 @ X0))),
% 0.53/0.75      inference('clc', [status(thm)], ['70', '71'])).
% 0.53/0.75  thf('73', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (r1_lattices @ sk_A @ sk_B_2 @ X0)
% 0.53/0.75          | (r3_lattice3 @ sk_A @ sk_B_2 @ (k1_tarski @ X0))
% 0.53/0.75          | (r3_lattice3 @ sk_A @ sk_B_2 @ (k1_tarski @ X0)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['65', '72'])).
% 0.53/0.75  thf('74', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r3_lattice3 @ sk_A @ sk_B_2 @ (k1_tarski @ X0))
% 0.53/0.75          | ~ (r1_lattices @ sk_A @ sk_B_2 @ X0))),
% 0.53/0.75      inference('simplify', [status(thm)], ['73'])).
% 0.53/0.75  thf('75', plain, ((r3_lattice3 @ sk_A @ sk_B_2 @ (k1_tarski @ sk_B_2))),
% 0.53/0.75      inference('sup-', [status(thm)], ['55', '74'])).
% 0.53/0.75  thf('76', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(t42_lattice3, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.53/0.75         ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75           ( ![C:$i]:
% 0.53/0.75             ( ( ( r2_hidden @ B @ C ) & ( r3_lattice3 @ A @ B @ C ) ) =>
% 0.53/0.75               ( ( k16_lattice3 @ A @ C ) = ( B ) ) ) ) ) ) ))).
% 0.53/0.75  thf('77', plain,
% 0.53/0.75      (![X48 : $i, X49 : $i, X50 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X48 @ (u1_struct_0 @ X49))
% 0.53/0.75          | ((k16_lattice3 @ X49 @ X50) = (X48))
% 0.53/0.75          | ~ (r3_lattice3 @ X49 @ X48 @ X50)
% 0.53/0.75          | ~ (r2_hidden @ X48 @ X50)
% 0.53/0.75          | ~ (l3_lattices @ X49)
% 0.53/0.75          | ~ (v4_lattice3 @ X49)
% 0.53/0.75          | ~ (v10_lattices @ X49)
% 0.53/0.75          | (v2_struct_0 @ X49))),
% 0.53/0.75      inference('cnf', [status(esa)], [t42_lattice3])).
% 0.53/0.75  thf('78', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (v10_lattices @ sk_A)
% 0.53/0.75          | ~ (v4_lattice3 @ sk_A)
% 0.53/0.75          | ~ (l3_lattices @ sk_A)
% 0.53/0.75          | ~ (r2_hidden @ sk_B_2 @ X0)
% 0.53/0.75          | ~ (r3_lattice3 @ sk_A @ sk_B_2 @ X0)
% 0.53/0.75          | ((k16_lattice3 @ sk_A @ X0) = (sk_B_2)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['76', '77'])).
% 0.53/0.75  thf('79', plain, ((v10_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('80', plain, ((v4_lattice3 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('81', plain, ((l3_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('82', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (r2_hidden @ sk_B_2 @ X0)
% 0.53/0.75          | ~ (r3_lattice3 @ sk_A @ sk_B_2 @ X0)
% 0.53/0.75          | ((k16_lattice3 @ sk_A @ X0) = (sk_B_2)))),
% 0.53/0.75      inference('demod', [status(thm)], ['78', '79', '80', '81'])).
% 0.53/0.75  thf('83', plain,
% 0.53/0.75      ((((k16_lattice3 @ sk_A @ (k1_tarski @ sk_B_2)) = (sk_B_2))
% 0.53/0.75        | ~ (r2_hidden @ sk_B_2 @ (k1_tarski @ sk_B_2))
% 0.53/0.75        | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['75', '82'])).
% 0.53/0.75  thf('84', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.75         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.53/0.75      inference('cnf', [status(esa)], [d1_tarski])).
% 0.53/0.75  thf('85', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.53/0.75      inference('simplify', [status(thm)], ['84'])).
% 0.53/0.75  thf('86', plain,
% 0.53/0.75      ((((k16_lattice3 @ sk_A @ (k1_tarski @ sk_B_2)) = (sk_B_2))
% 0.53/0.75        | (v2_struct_0 @ sk_A))),
% 0.53/0.75      inference('demod', [status(thm)], ['83', '85'])).
% 0.53/0.75  thf('87', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('88', plain, (((k16_lattice3 @ sk_A @ (k1_tarski @ sk_B_2)) = (sk_B_2))),
% 0.53/0.75      inference('clc', [status(thm)], ['86', '87'])).
% 0.53/0.75  thf('89', plain,
% 0.53/0.75      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2) = (k1_tarski @ sk_B_2))
% 0.53/0.75        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['1', '2'])).
% 0.53/0.75  thf('90', plain,
% 0.53/0.75      ((((k16_lattice3 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.53/0.75          != (sk_B_2)))
% 0.53/0.75         <= (~
% 0.53/0.75             (((k16_lattice3 @ sk_A @ 
% 0.53/0.75                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)) = (sk_B_2))))),
% 0.53/0.75      inference('split', [status(esa)], ['4'])).
% 0.53/0.75  thf('91', plain,
% 0.53/0.75      (((((k16_lattice3 @ sk_A @ (k1_tarski @ sk_B_2)) != (sk_B_2))
% 0.53/0.75         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.53/0.75         <= (~
% 0.53/0.75             (((k16_lattice3 @ sk_A @ 
% 0.53/0.75                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)) = (sk_B_2))))),
% 0.53/0.75      inference('sup-', [status(thm)], ['89', '90'])).
% 0.53/0.75  thf('92', plain,
% 0.53/0.75      (((((sk_B_2) != (sk_B_2)) | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.53/0.75         <= (~
% 0.53/0.75             (((k16_lattice3 @ sk_A @ 
% 0.53/0.75                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)) = (sk_B_2))))),
% 0.53/0.75      inference('sup-', [status(thm)], ['88', '91'])).
% 0.53/0.75  thf('93', plain,
% 0.53/0.75      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.53/0.75         <= (~
% 0.53/0.75             (((k16_lattice3 @ sk_A @ 
% 0.53/0.75                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)) = (sk_B_2))))),
% 0.53/0.75      inference('simplify', [status(thm)], ['92'])).
% 0.53/0.75  thf(fc2_struct_0, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.53/0.75       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.53/0.75  thf('94', plain,
% 0.53/0.75      (![X5 : $i]:
% 0.53/0.75         (~ (v1_xboole_0 @ (u1_struct_0 @ X5))
% 0.53/0.75          | ~ (l1_struct_0 @ X5)
% 0.53/0.75          | (v2_struct_0 @ X5))),
% 0.53/0.75      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.53/0.75  thf('95', plain,
% 0.53/0.75      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.53/0.75         <= (~
% 0.53/0.75             (((k16_lattice3 @ sk_A @ 
% 0.53/0.75                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)) = (sk_B_2))))),
% 0.53/0.75      inference('sup-', [status(thm)], ['93', '94'])).
% 0.53/0.75  thf('96', plain, ((l3_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(dt_l3_lattices, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( l3_lattices @ A ) => ( ( l1_lattices @ A ) & ( l2_lattices @ A ) ) ))).
% 0.53/0.75  thf('97', plain,
% 0.53/0.75      (![X13 : $i]: ((l2_lattices @ X13) | ~ (l3_lattices @ X13))),
% 0.53/0.75      inference('cnf', [status(esa)], [dt_l3_lattices])).
% 0.53/0.75  thf('98', plain, ((l2_lattices @ sk_A)),
% 0.53/0.75      inference('sup-', [status(thm)], ['96', '97'])).
% 0.53/0.75  thf(dt_l2_lattices, axiom,
% 0.53/0.75    (![A:$i]: ( ( l2_lattices @ A ) => ( l1_struct_0 @ A ) ))).
% 0.53/0.75  thf('99', plain,
% 0.53/0.75      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l2_lattices @ X12))),
% 0.53/0.75      inference('cnf', [status(esa)], [dt_l2_lattices])).
% 0.53/0.75  thf('100', plain, ((l1_struct_0 @ sk_A)),
% 0.53/0.75      inference('sup-', [status(thm)], ['98', '99'])).
% 0.53/0.75  thf('101', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_A))
% 0.53/0.75         <= (~
% 0.53/0.75             (((k16_lattice3 @ sk_A @ 
% 0.53/0.75                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2)) = (sk_B_2))))),
% 0.53/0.75      inference('demod', [status(thm)], ['95', '100'])).
% 0.53/0.75  thf('102', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('103', plain,
% 0.53/0.75      ((((k16_lattice3 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.53/0.75          = (sk_B_2)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['101', '102'])).
% 0.53/0.75  thf('104', plain,
% 0.53/0.75      (~
% 0.53/0.75       (((k15_lattice3 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.53/0.75          = (sk_B_2))) | 
% 0.53/0.75       ~
% 0.53/0.75       (((k16_lattice3 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.53/0.75          = (sk_B_2)))),
% 0.53/0.75      inference('split', [status(esa)], ['4'])).
% 0.53/0.75  thf('105', plain,
% 0.53/0.75      (~
% 0.53/0.75       (((k15_lattice3 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B_2))
% 0.53/0.75          = (sk_B_2)))),
% 0.53/0.75      inference('sat_resolution*', [status(thm)], ['103', '104'])).
% 0.53/0.75  thf('106', plain,
% 0.53/0.75      ((((k15_lattice3 @ sk_A @ (k1_tarski @ sk_B_2)) != (sk_B_2))
% 0.53/0.75        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('simpl_trail', [status(thm)], ['6', '105'])).
% 0.53/0.75  thf('107', plain, ((r1_lattices @ sk_A @ sk_B_2 @ sk_B_2)),
% 0.53/0.75      inference('clc', [status(thm)], ['53', '54'])).
% 0.53/0.75  thf('108', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(d17_lattice3, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75           ( ![C:$i]:
% 0.53/0.75             ( ( r4_lattice3 @ A @ B @ C ) <=>
% 0.53/0.75               ( ![D:$i]:
% 0.53/0.75                 ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75                   ( ( r2_hidden @ D @ C ) => ( r1_lattices @ A @ D @ B ) ) ) ) ) ) ) ) ))).
% 0.53/0.75  thf('109', plain,
% 0.53/0.75      (![X34 : $i, X35 : $i, X38 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X35))
% 0.53/0.75          | (r2_hidden @ (sk_D_1 @ X38 @ X34 @ X35) @ X38)
% 0.53/0.75          | (r4_lattice3 @ X35 @ X34 @ X38)
% 0.53/0.75          | ~ (l3_lattices @ X35)
% 0.53/0.75          | (v2_struct_0 @ X35))),
% 0.53/0.75      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.53/0.75  thf('110', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (l3_lattices @ sk_A)
% 0.53/0.75          | (r4_lattice3 @ sk_A @ sk_B_2 @ X0)
% 0.53/0.75          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B_2 @ sk_A) @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['108', '109'])).
% 0.53/0.75  thf('111', plain, ((l3_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('112', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | (r4_lattice3 @ sk_A @ sk_B_2 @ X0)
% 0.53/0.75          | (r2_hidden @ (sk_D_1 @ X0 @ sk_B_2 @ sk_A) @ X0))),
% 0.53/0.75      inference('demod', [status(thm)], ['110', '111'])).
% 0.53/0.75  thf('113', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('114', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r2_hidden @ (sk_D_1 @ X0 @ sk_B_2 @ sk_A) @ X0)
% 0.53/0.75          | (r4_lattice3 @ sk_A @ sk_B_2 @ X0))),
% 0.53/0.75      inference('clc', [status(thm)], ['112', '113'])).
% 0.53/0.75  thf('115', plain,
% 0.53/0.75      (![X0 : $i, X3 : $i]:
% 0.53/0.75         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.53/0.75      inference('simplify', [status(thm)], ['63'])).
% 0.53/0.75  thf('116', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r4_lattice3 @ sk_A @ sk_B_2 @ (k1_tarski @ X0))
% 0.53/0.75          | ((sk_D_1 @ (k1_tarski @ X0) @ sk_B_2 @ sk_A) = (X0)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['114', '115'])).
% 0.53/0.75  thf('117', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('118', plain,
% 0.53/0.75      (![X34 : $i, X35 : $i, X38 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X35))
% 0.53/0.75          | ~ (r1_lattices @ X35 @ (sk_D_1 @ X38 @ X34 @ X35) @ X34)
% 0.53/0.75          | (r4_lattice3 @ X35 @ X34 @ X38)
% 0.53/0.75          | ~ (l3_lattices @ X35)
% 0.53/0.75          | (v2_struct_0 @ X35))),
% 0.53/0.75      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.53/0.75  thf('119', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (l3_lattices @ sk_A)
% 0.53/0.75          | (r4_lattice3 @ sk_A @ sk_B_2 @ X0)
% 0.53/0.75          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B_2 @ sk_A) @ sk_B_2))),
% 0.53/0.75      inference('sup-', [status(thm)], ['117', '118'])).
% 0.53/0.75  thf('120', plain, ((l3_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('121', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | (r4_lattice3 @ sk_A @ sk_B_2 @ X0)
% 0.53/0.75          | ~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B_2 @ sk_A) @ sk_B_2))),
% 0.53/0.75      inference('demod', [status(thm)], ['119', '120'])).
% 0.53/0.75  thf('122', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('123', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (r1_lattices @ sk_A @ (sk_D_1 @ X0 @ sk_B_2 @ sk_A) @ sk_B_2)
% 0.53/0.75          | (r4_lattice3 @ sk_A @ sk_B_2 @ X0))),
% 0.53/0.75      inference('clc', [status(thm)], ['121', '122'])).
% 0.53/0.75  thf('124', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (r1_lattices @ sk_A @ X0 @ sk_B_2)
% 0.53/0.75          | (r4_lattice3 @ sk_A @ sk_B_2 @ (k1_tarski @ X0))
% 0.53/0.75          | (r4_lattice3 @ sk_A @ sk_B_2 @ (k1_tarski @ X0)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['116', '123'])).
% 0.53/0.75  thf('125', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r4_lattice3 @ sk_A @ sk_B_2 @ (k1_tarski @ X0))
% 0.53/0.75          | ~ (r1_lattices @ sk_A @ X0 @ sk_B_2))),
% 0.53/0.75      inference('simplify', [status(thm)], ['124'])).
% 0.53/0.75  thf('126', plain, ((r4_lattice3 @ sk_A @ sk_B_2 @ (k1_tarski @ sk_B_2))),
% 0.53/0.75      inference('sup-', [status(thm)], ['107', '125'])).
% 0.53/0.75  thf('127', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf(dt_k15_lattice3, axiom,
% 0.53/0.75    (![A:$i,B:$i]:
% 0.53/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.53/0.75       ( m1_subset_1 @ ( k15_lattice3 @ A @ B ) @ ( u1_struct_0 @ A ) ) ))).
% 0.53/0.75  thf('128', plain,
% 0.53/0.75      (![X46 : $i, X47 : $i]:
% 0.53/0.75         (~ (l3_lattices @ X46)
% 0.53/0.75          | (v2_struct_0 @ X46)
% 0.53/0.75          | (m1_subset_1 @ (k15_lattice3 @ X46 @ X47) @ (u1_struct_0 @ X46)))),
% 0.53/0.75      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.53/0.75  thf(d21_lattice3, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( l3_lattices @ A ) ) =>
% 0.53/0.75       ( ( ( ~( v2_struct_0 @ A ) ) & ( v10_lattices @ A ) & 
% 0.53/0.75           ( v4_lattice3 @ A ) & ( l3_lattices @ A ) ) =>
% 0.53/0.75         ( ![B:$i,C:$i]:
% 0.53/0.75           ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75             ( ( ( C ) = ( k15_lattice3 @ A @ B ) ) <=>
% 0.53/0.75               ( ( r4_lattice3 @ A @ C @ B ) & 
% 0.53/0.75                 ( ![D:$i]:
% 0.53/0.75                   ( ( m1_subset_1 @ D @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75                     ( ( r4_lattice3 @ A @ D @ B ) =>
% 0.53/0.75                       ( r1_lattices @ A @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.53/0.75  thf('129', plain,
% 0.53/0.75      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X39)
% 0.53/0.75          | ~ (v10_lattices @ X39)
% 0.53/0.75          | ~ (v4_lattice3 @ X39)
% 0.53/0.75          | ~ (l3_lattices @ X39)
% 0.53/0.75          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X39))
% 0.53/0.75          | ((X40) != (k15_lattice3 @ X39 @ X41))
% 0.53/0.75          | ~ (r4_lattice3 @ X39 @ X42 @ X41)
% 0.53/0.75          | (r1_lattices @ X39 @ X40 @ X42)
% 0.53/0.75          | ~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X39))
% 0.53/0.75          | ~ (l3_lattices @ X39)
% 0.53/0.75          | (v2_struct_0 @ X39))),
% 0.53/0.75      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.53/0.75  thf('130', plain,
% 0.53/0.75      (![X39 : $i, X41 : $i, X42 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X42 @ (u1_struct_0 @ X39))
% 0.53/0.75          | (r1_lattices @ X39 @ (k15_lattice3 @ X39 @ X41) @ X42)
% 0.53/0.75          | ~ (r4_lattice3 @ X39 @ X42 @ X41)
% 0.53/0.75          | ~ (m1_subset_1 @ (k15_lattice3 @ X39 @ X41) @ (u1_struct_0 @ X39))
% 0.53/0.75          | ~ (l3_lattices @ X39)
% 0.53/0.75          | ~ (v4_lattice3 @ X39)
% 0.53/0.75          | ~ (v10_lattices @ X39)
% 0.53/0.75          | (v2_struct_0 @ X39))),
% 0.53/0.75      inference('simplify', [status(thm)], ['129'])).
% 0.53/0.75  thf('131', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X0)
% 0.53/0.75          | ~ (l3_lattices @ X0)
% 0.53/0.75          | (v2_struct_0 @ X0)
% 0.53/0.75          | ~ (v10_lattices @ X0)
% 0.53/0.75          | ~ (v4_lattice3 @ X0)
% 0.53/0.75          | ~ (l3_lattices @ X0)
% 0.53/0.75          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 0.53/0.75          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.53/0.75          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['128', '130'])).
% 0.53/0.75  thf('132', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.53/0.75          | (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.53/0.75          | ~ (r4_lattice3 @ X0 @ X2 @ X1)
% 0.53/0.75          | ~ (v4_lattice3 @ X0)
% 0.53/0.75          | ~ (v10_lattices @ X0)
% 0.53/0.75          | ~ (l3_lattices @ X0)
% 0.53/0.75          | (v2_struct_0 @ X0))),
% 0.53/0.75      inference('simplify', [status(thm)], ['131'])).
% 0.53/0.75  thf('133', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (l3_lattices @ sk_A)
% 0.53/0.75          | ~ (v10_lattices @ sk_A)
% 0.53/0.75          | ~ (v4_lattice3 @ sk_A)
% 0.53/0.75          | ~ (r4_lattice3 @ sk_A @ sk_B_2 @ X0)
% 0.53/0.75          | (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B_2))),
% 0.53/0.75      inference('sup-', [status(thm)], ['127', '132'])).
% 0.53/0.75  thf('134', plain, ((l3_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('135', plain, ((v10_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('136', plain, ((v4_lattice3 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('137', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (r4_lattice3 @ sk_A @ sk_B_2 @ X0)
% 0.53/0.75          | (r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B_2))),
% 0.53/0.75      inference('demod', [status(thm)], ['133', '134', '135', '136'])).
% 0.53/0.75  thf('138', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('139', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ X0) @ sk_B_2)
% 0.53/0.75          | ~ (r4_lattice3 @ sk_A @ sk_B_2 @ X0))),
% 0.53/0.75      inference('clc', [status(thm)], ['137', '138'])).
% 0.53/0.75  thf('140', plain,
% 0.53/0.75      ((r1_lattices @ sk_A @ (k15_lattice3 @ sk_A @ (k1_tarski @ sk_B_2)) @ 
% 0.53/0.75        sk_B_2)),
% 0.53/0.75      inference('sup-', [status(thm)], ['126', '139'])).
% 0.53/0.75  thf('141', plain,
% 0.53/0.75      (![X46 : $i, X47 : $i]:
% 0.53/0.75         (~ (l3_lattices @ X46)
% 0.53/0.75          | (v2_struct_0 @ X46)
% 0.53/0.75          | (m1_subset_1 @ (k15_lattice3 @ X46 @ X47) @ (u1_struct_0 @ X46)))),
% 0.53/0.75      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.53/0.75  thf(t26_lattices, axiom,
% 0.53/0.75    (![A:$i]:
% 0.53/0.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( v4_lattices @ A ) & ( l2_lattices @ A ) ) =>
% 0.53/0.75       ( ![B:$i]:
% 0.53/0.75         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75           ( ![C:$i]:
% 0.53/0.75             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.53/0.75               ( ( ( r1_lattices @ A @ B @ C ) & ( r1_lattices @ A @ C @ B ) ) =>
% 0.53/0.75                 ( ( B ) = ( C ) ) ) ) ) ) ) ))).
% 0.53/0.75  thf('142', plain,
% 0.53/0.75      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X23))
% 0.53/0.75          | ~ (r1_lattices @ X23 @ X22 @ X24)
% 0.53/0.75          | ~ (r1_lattices @ X23 @ X24 @ X22)
% 0.53/0.75          | ((X22) = (X24))
% 0.53/0.75          | ~ (m1_subset_1 @ X24 @ (u1_struct_0 @ X23))
% 0.53/0.75          | ~ (l2_lattices @ X23)
% 0.53/0.75          | ~ (v4_lattices @ X23)
% 0.53/0.75          | (v2_struct_0 @ X23))),
% 0.53/0.75      inference('cnf', [status(esa)], [t26_lattices])).
% 0.53/0.75  thf('143', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X0)
% 0.53/0.75          | ~ (l3_lattices @ X0)
% 0.53/0.75          | (v2_struct_0 @ X0)
% 0.53/0.75          | ~ (v4_lattices @ X0)
% 0.53/0.75          | ~ (l2_lattices @ X0)
% 0.53/0.75          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.53/0.75          | ((k15_lattice3 @ X0 @ X1) = (X2))
% 0.53/0.75          | ~ (r1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 0.53/0.75          | ~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2))),
% 0.53/0.75      inference('sup-', [status(thm)], ['141', '142'])).
% 0.53/0.75  thf('144', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.75         (~ (r1_lattices @ X0 @ (k15_lattice3 @ X0 @ X1) @ X2)
% 0.53/0.75          | ~ (r1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 0.53/0.75          | ((k15_lattice3 @ X0 @ X1) = (X2))
% 0.53/0.75          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.53/0.75          | ~ (l2_lattices @ X0)
% 0.53/0.75          | ~ (v4_lattices @ X0)
% 0.53/0.75          | ~ (l3_lattices @ X0)
% 0.53/0.75          | (v2_struct_0 @ X0))),
% 0.53/0.75      inference('simplify', [status(thm)], ['143'])).
% 0.53/0.75  thf('145', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_A)
% 0.53/0.75        | ~ (l3_lattices @ sk_A)
% 0.53/0.75        | ~ (v4_lattices @ sk_A)
% 0.53/0.75        | ~ (l2_lattices @ sk_A)
% 0.53/0.75        | ~ (m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))
% 0.53/0.75        | ((k15_lattice3 @ sk_A @ (k1_tarski @ sk_B_2)) = (sk_B_2))
% 0.53/0.75        | ~ (r1_lattices @ sk_A @ sk_B_2 @ 
% 0.53/0.75             (k15_lattice3 @ sk_A @ (k1_tarski @ sk_B_2))))),
% 0.53/0.75      inference('sup-', [status(thm)], ['140', '144'])).
% 0.53/0.75  thf('146', plain, ((l3_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('147', plain,
% 0.53/0.75      (![X8 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X8)
% 0.53/0.75          | ~ (v10_lattices @ X8)
% 0.53/0.75          | (v4_lattices @ X8)
% 0.53/0.75          | ~ (l3_lattices @ X8))),
% 0.53/0.75      inference('cnf', [status(esa)], [cc1_lattices])).
% 0.53/0.75  thf('148', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('149', plain,
% 0.53/0.75      ((~ (l3_lattices @ sk_A) | (v4_lattices @ sk_A) | ~ (v10_lattices @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['147', '148'])).
% 0.53/0.75  thf('150', plain, ((l3_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('151', plain, ((v10_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('152', plain, ((v4_lattices @ sk_A)),
% 0.53/0.75      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.53/0.75  thf('153', plain, ((l2_lattices @ sk_A)),
% 0.53/0.75      inference('sup-', [status(thm)], ['96', '97'])).
% 0.53/0.75  thf('154', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('155', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.53/0.75      inference('simplify', [status(thm)], ['84'])).
% 0.53/0.75  thf('156', plain, ((m1_subset_1 @ sk_B_2 @ (u1_struct_0 @ sk_A))),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('157', plain,
% 0.53/0.75      (![X46 : $i, X47 : $i]:
% 0.53/0.75         (~ (l3_lattices @ X46)
% 0.53/0.75          | (v2_struct_0 @ X46)
% 0.53/0.75          | (m1_subset_1 @ (k15_lattice3 @ X46 @ X47) @ (u1_struct_0 @ X46)))),
% 0.53/0.75      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.53/0.75  thf('158', plain,
% 0.53/0.75      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X39)
% 0.53/0.75          | ~ (v10_lattices @ X39)
% 0.53/0.75          | ~ (v4_lattice3 @ X39)
% 0.53/0.75          | ~ (l3_lattices @ X39)
% 0.53/0.75          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X39))
% 0.53/0.75          | ((X40) != (k15_lattice3 @ X39 @ X41))
% 0.53/0.75          | (r4_lattice3 @ X39 @ X40 @ X41)
% 0.53/0.75          | ~ (l3_lattices @ X39)
% 0.53/0.75          | (v2_struct_0 @ X39))),
% 0.53/0.75      inference('cnf', [status(esa)], [d21_lattice3])).
% 0.53/0.75  thf('159', plain,
% 0.53/0.75      (![X39 : $i, X41 : $i]:
% 0.53/0.75         ((r4_lattice3 @ X39 @ (k15_lattice3 @ X39 @ X41) @ X41)
% 0.53/0.75          | ~ (m1_subset_1 @ (k15_lattice3 @ X39 @ X41) @ (u1_struct_0 @ X39))
% 0.53/0.75          | ~ (l3_lattices @ X39)
% 0.53/0.75          | ~ (v4_lattice3 @ X39)
% 0.53/0.75          | ~ (v10_lattices @ X39)
% 0.53/0.75          | (v2_struct_0 @ X39))),
% 0.53/0.75      inference('simplify', [status(thm)], ['158'])).
% 0.53/0.75  thf('160', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X0)
% 0.53/0.75          | ~ (l3_lattices @ X0)
% 0.53/0.75          | (v2_struct_0 @ X0)
% 0.53/0.75          | ~ (v10_lattices @ X0)
% 0.53/0.75          | ~ (v4_lattice3 @ X0)
% 0.53/0.75          | ~ (l3_lattices @ X0)
% 0.53/0.75          | (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X1))),
% 0.53/0.75      inference('sup-', [status(thm)], ['157', '159'])).
% 0.53/0.75  thf('161', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i]:
% 0.53/0.75         ((r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X1)
% 0.53/0.75          | ~ (v4_lattice3 @ X0)
% 0.53/0.75          | ~ (v10_lattices @ X0)
% 0.53/0.75          | ~ (l3_lattices @ X0)
% 0.53/0.75          | (v2_struct_0 @ X0))),
% 0.53/0.75      inference('simplify', [status(thm)], ['160'])).
% 0.53/0.75  thf('162', plain,
% 0.53/0.75      (![X46 : $i, X47 : $i]:
% 0.53/0.75         (~ (l3_lattices @ X46)
% 0.53/0.75          | (v2_struct_0 @ X46)
% 0.53/0.75          | (m1_subset_1 @ (k15_lattice3 @ X46 @ X47) @ (u1_struct_0 @ X46)))),
% 0.53/0.75      inference('cnf', [status(esa)], [dt_k15_lattice3])).
% 0.53/0.75  thf('163', plain,
% 0.53/0.75      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.53/0.75         (~ (m1_subset_1 @ X34 @ (u1_struct_0 @ X35))
% 0.53/0.75          | ~ (r4_lattice3 @ X35 @ X34 @ X36)
% 0.53/0.75          | ~ (r2_hidden @ X37 @ X36)
% 0.53/0.75          | (r1_lattices @ X35 @ X37 @ X34)
% 0.53/0.75          | ~ (m1_subset_1 @ X37 @ (u1_struct_0 @ X35))
% 0.53/0.75          | ~ (l3_lattices @ X35)
% 0.53/0.75          | (v2_struct_0 @ X35))),
% 0.53/0.75      inference('cnf', [status(esa)], [d17_lattice3])).
% 0.53/0.75  thf('164', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X0)
% 0.53/0.75          | ~ (l3_lattices @ X0)
% 0.53/0.75          | (v2_struct_0 @ X0)
% 0.53/0.75          | ~ (l3_lattices @ X0)
% 0.53/0.75          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.53/0.75          | (r1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 0.53/0.75          | ~ (r2_hidden @ X2 @ X3)
% 0.53/0.75          | ~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X3))),
% 0.53/0.75      inference('sup-', [status(thm)], ['162', '163'])).
% 0.53/0.75  thf('165', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.53/0.75         (~ (r4_lattice3 @ X0 @ (k15_lattice3 @ X0 @ X1) @ X3)
% 0.53/0.75          | ~ (r2_hidden @ X2 @ X3)
% 0.53/0.75          | (r1_lattices @ X0 @ X2 @ (k15_lattice3 @ X0 @ X1))
% 0.53/0.75          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.53/0.75          | ~ (l3_lattices @ X0)
% 0.53/0.75          | (v2_struct_0 @ X0))),
% 0.53/0.75      inference('simplify', [status(thm)], ['164'])).
% 0.53/0.75  thf('166', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.75         ((v2_struct_0 @ X1)
% 0.53/0.75          | ~ (l3_lattices @ X1)
% 0.53/0.75          | ~ (v10_lattices @ X1)
% 0.53/0.75          | ~ (v4_lattice3 @ X1)
% 0.53/0.75          | (v2_struct_0 @ X1)
% 0.53/0.75          | ~ (l3_lattices @ X1)
% 0.53/0.75          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.53/0.75          | (r1_lattices @ X1 @ X2 @ (k15_lattice3 @ X1 @ X0))
% 0.53/0.75          | ~ (r2_hidden @ X2 @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['161', '165'])).
% 0.53/0.75  thf('167', plain,
% 0.53/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.75         (~ (r2_hidden @ X2 @ X0)
% 0.53/0.75          | (r1_lattices @ X1 @ X2 @ (k15_lattice3 @ X1 @ X0))
% 0.53/0.75          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X1))
% 0.53/0.75          | ~ (v4_lattice3 @ X1)
% 0.53/0.75          | ~ (v10_lattices @ X1)
% 0.53/0.75          | ~ (l3_lattices @ X1)
% 0.53/0.75          | (v2_struct_0 @ X1))),
% 0.53/0.75      inference('simplify', [status(thm)], ['166'])).
% 0.53/0.75  thf('168', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | ~ (l3_lattices @ sk_A)
% 0.53/0.75          | ~ (v10_lattices @ sk_A)
% 0.53/0.75          | ~ (v4_lattice3 @ sk_A)
% 0.53/0.75          | (r1_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ X0))
% 0.53/0.75          | ~ (r2_hidden @ sk_B_2 @ X0))),
% 0.53/0.75      inference('sup-', [status(thm)], ['156', '167'])).
% 0.53/0.75  thf('169', plain, ((l3_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('170', plain, ((v10_lattices @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('171', plain, ((v4_lattice3 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('172', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         ((v2_struct_0 @ sk_A)
% 0.53/0.75          | (r1_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ X0))
% 0.53/0.75          | ~ (r2_hidden @ sk_B_2 @ X0))),
% 0.53/0.75      inference('demod', [status(thm)], ['168', '169', '170', '171'])).
% 0.53/0.75  thf('173', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('174', plain,
% 0.53/0.75      (![X0 : $i]:
% 0.53/0.75         (~ (r2_hidden @ sk_B_2 @ X0)
% 0.53/0.75          | (r1_lattices @ sk_A @ sk_B_2 @ (k15_lattice3 @ sk_A @ X0)))),
% 0.53/0.75      inference('clc', [status(thm)], ['172', '173'])).
% 0.53/0.75  thf('175', plain,
% 0.53/0.75      ((r1_lattices @ sk_A @ sk_B_2 @ 
% 0.53/0.75        (k15_lattice3 @ sk_A @ (k1_tarski @ sk_B_2)))),
% 0.53/0.75      inference('sup-', [status(thm)], ['155', '174'])).
% 0.53/0.75  thf('176', plain,
% 0.53/0.75      (((v2_struct_0 @ sk_A)
% 0.53/0.75        | ((k15_lattice3 @ sk_A @ (k1_tarski @ sk_B_2)) = (sk_B_2)))),
% 0.53/0.75      inference('demod', [status(thm)],
% 0.53/0.75                ['145', '146', '152', '153', '154', '175'])).
% 0.53/0.75  thf('177', plain, (~ (v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.75  thf('178', plain,
% 0.53/0.75      (((k15_lattice3 @ sk_A @ (k1_tarski @ sk_B_2)) = (sk_B_2))),
% 0.53/0.75      inference('clc', [status(thm)], ['176', '177'])).
% 0.53/0.75  thf('179', plain,
% 0.53/0.75      ((((sk_B_2) != (sk_B_2)) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.53/0.75      inference('demod', [status(thm)], ['106', '178'])).
% 0.53/0.75  thf('180', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.53/0.75      inference('simplify', [status(thm)], ['179'])).
% 0.53/0.75  thf('181', plain,
% 0.53/0.75      (![X5 : $i]:
% 0.53/0.75         (~ (v1_xboole_0 @ (u1_struct_0 @ X5))
% 0.53/0.75          | ~ (l1_struct_0 @ X5)
% 0.53/0.75          | (v2_struct_0 @ X5))),
% 0.53/0.75      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.53/0.75  thf('182', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.53/0.75      inference('sup-', [status(thm)], ['180', '181'])).
% 0.53/0.75  thf('183', plain, ((l1_struct_0 @ sk_A)),
% 0.53/0.75      inference('sup-', [status(thm)], ['98', '99'])).
% 0.53/0.75  thf('184', plain, ((v2_struct_0 @ sk_A)),
% 0.53/0.75      inference('demod', [status(thm)], ['182', '183'])).
% 0.53/0.75  thf('185', plain, ($false), inference('demod', [status(thm)], ['0', '184'])).
% 0.53/0.75  
% 0.53/0.75  % SZS output end Refutation
% 0.53/0.75  
% 0.53/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
