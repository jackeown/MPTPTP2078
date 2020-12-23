%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1437+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bxB2LGKMwr

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:39 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 839 expanded)
%              Number of leaves         :   30 ( 229 expanded)
%              Depth                    :   30
%              Number of atoms          : 1467 (14917 expanded)
%              Number of equality atoms :   46 ( 187 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k8_filter_1_type,type,(
    k8_filter_1: $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_domain_1_type,type,(
    k1_domain_1: $i > $i > $i > $i > $i )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf('#_fresh_sk1_type',type,(
    '#_fresh_sk1': $i > $i )).

thf('#_fresh_sk2_type',type,(
    '#_fresh_sk2': $i > $i )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(a_1_0_filter_1_type,type,(
    a_1_0_filter_1: $i > $i )).

thf(dt_l1_lattices,axiom,(
    ! [A: $i] :
      ( ( l1_lattices @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( l1_struct_0 @ X1 )
      | ~ ( l1_lattices @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_lattices])).

thf(t32_filter_1,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ B @ C ) @ ( k8_filter_1 @ A ) )
              <=> ( r3_lattices @ A @ B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v10_lattices @ A )
          & ( l3_lattices @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ A ) @ ( u1_struct_0 @ A ) @ B @ C ) @ ( k8_filter_1 @ A ) )
                <=> ( r3_lattices @ A @ B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_filter_1])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_domain_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ C @ A )
        & ( m1_subset_1 @ D @ B ) )
     => ( ( k1_domain_1 @ A @ B @ C @ D )
        = ( k4_tarski @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ X10 )
      | ( ( k1_domain_1 @ X9 @ X10 @ X8 @ X11 )
        = ( k4_tarski @ X8 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_domain_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ sk_B @ X0 )
        = ( k4_tarski @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ X1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 )
      = ( k4_tarski @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,
    ( ( ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 )
      = ( k4_tarski @ sk_B @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r3_lattices @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
   <= ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( r3_lattices @ sk_A @ sk_B @ sk_C_1 )
   <= ( r3_lattices @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fraenkel_a_1_0_filter_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v10_lattices @ B )
        & ( l3_lattices @ B ) )
     => ( ( r2_hidden @ A @ ( a_1_0_filter_1 @ B ) )
      <=> ? [C: $i,D: $i] :
            ( ( r3_lattices @ B @ C @ D )
            & ( A
              = ( k1_domain_1 @ ( u1_struct_0 @ B ) @ ( u1_struct_0 @ B ) @ C @ D ) )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) )
            & ( m1_subset_1 @ C @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ( X7
       != ( k1_domain_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X5 ) @ X4 @ X6 ) )
      | ~ ( r3_lattices @ X5 @ X4 @ X6 )
      | ( r2_hidden @ X7 @ ( a_1_0_filter_1 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_1_0_filter_1])).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v2_struct_0 @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ~ ( l3_lattices @ X5 )
      | ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X5 ) @ X4 @ X6 ) @ ( a_1_0_filter_1 @ X5 ) )
      | ~ ( r3_lattices @ X5 @ X4 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X5 ) )
      | ~ ( m1_subset_1 @ X4 @ ( u1_struct_0 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_lattices @ sk_A @ X0 @ sk_C_1 )
      | ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 ) @ ( a_1_0_filter_1 @ sk_A ) )
      | ~ ( l3_lattices @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d8_filter_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ( ( k8_filter_1 @ A )
        = ( a_1_0_filter_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k8_filter_1 @ X0 )
        = ( a_1_0_filter_1 @ X0 ) )
      | ~ ( l3_lattices @ X0 )
      | ~ ( v10_lattices @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_filter_1])).

thf('19',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v10_lattices @ sk_A )
    | ( ( k8_filter_1 @ sk_A )
      = ( a_1_0_filter_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k8_filter_1 @ sk_A )
      = ( a_1_0_filter_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k8_filter_1 @ sk_A )
    = ( a_1_0_filter_1 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_lattices @ sk_A @ X0 @ sk_C_1 )
      | ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','23','24','25'])).

thf('27',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
    | ~ ( r3_lattices @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','26'])).

thf('28',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
   <= ( r3_lattices @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','29'])).

thf('31',plain,
    ( ~ ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('32',plain,
    ( ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
    | ~ ( r3_lattices @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
    | ( r3_lattices @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('34',plain,(
    r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['10','32','33'])).

thf('35',plain,(
    r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['8','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','35'])).

thf('37',plain,
    ( ( k8_filter_1 @ sk_A )
    = ( a_1_0_filter_1 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('38',plain,(
    ! [X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ ( a_1_0_filter_1 @ X5 ) )
      | ( X7
        = ( k1_domain_1 @ ( u1_struct_0 @ X5 ) @ ( u1_struct_0 @ X5 ) @ ( sk_C @ X5 @ X7 ) @ ( sk_D @ X5 @ X7 ) ) )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_1_0_filter_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( X0
        = ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_A @ X0 ) @ ( sk_D @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( X0
        = ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_A @ X0 ) @ ( sk_D @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_A @ X0 ) @ ( sk_D @ sk_A @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k4_tarski @ sk_B @ sk_C_1 )
      = ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,
    ( ( ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 )
      = ( k4_tarski @ sk_B @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('47',plain,
    ( ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
   <= ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('48',plain,
    ( ( k8_filter_1 @ sk_A )
    = ( a_1_0_filter_1 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('49',plain,(
    ! [X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ ( a_1_0_filter_1 @ X5 ) )
      | ( m1_subset_1 @ ( sk_D @ X5 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_1_0_filter_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_A @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,(
    r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['10','32','33'])).

thf('58',plain,(
    m1_subset_1 @ ( sk_D @ sk_A @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['46','58'])).

thf('60',plain,
    ( ( ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 )
      = ( k4_tarski @ sk_B @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('61',plain,
    ( ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
   <= ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('62',plain,
    ( ( k8_filter_1 @ sk_A )
    = ( a_1_0_filter_1 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('63',plain,(
    ! [X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ ( a_1_0_filter_1 @ X5 ) )
      | ( m1_subset_1 @ ( sk_C @ X5 @ X7 ) @ ( u1_struct_0 @ X5 ) )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_1_0_filter_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_A @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','69'])).

thf('71',plain,(
    r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['10','32','33'])).

thf('72',plain,(
    m1_subset_1 @ ( sk_C @ sk_A @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['60','72'])).

thf('74',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X8 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ X10 )
      | ( ( k1_domain_1 @ X9 @ X10 @ X8 @ X11 )
        = ( k4_tarski @ X8 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_domain_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ X0 )
        = ( k4_tarski @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ X1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 )
      | ( ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ X0 )
        = ( k4_tarski @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) )
      = ( k4_tarski @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','76'])).

thf('78',plain,
    ( ( ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) )
      = ( k4_tarski @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( ( k4_tarski @ sk_B @ sk_C_1 )
      = ( k4_tarski @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','78'])).

thf('80',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k4_tarski @ sk_B @ sk_C_1 )
      = ( k4_tarski @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf(t33_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k4_tarski @ A @ B )
        = ( k4_tarski @ C @ D ) )
     => ( ( A = C )
        & ( B = D ) ) ) )).

thf('81',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X15 = X14 )
      | ( ( k4_tarski @ X13 @ X15 )
       != ( k4_tarski @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('82',plain,(
    ! [X13: $i,X15: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X13 @ X15 ) )
      = X15 ) ),
    inference(inj_rec,[status(thm)],['81'])).

thf('83',plain,
    ( ( ( '#_fresh_sk2' @ ( k4_tarski @ sk_B @ sk_C_1 ) )
      = ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['80','82'])).

thf('84',plain,(
    ! [X13: $i,X15: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X13 @ X15 ) )
      = X15 ) ),
    inference(inj_rec,[status(thm)],['81'])).

thf('85',plain,
    ( ( sk_C_1
      = ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k4_tarski @ sk_B @ sk_C_1 )
      = ( k4_tarski @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('87',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X13 = X12 )
      | ( ( k4_tarski @ X13 @ X15 )
       != ( k4_tarski @ X12 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('88',plain,(
    ! [X13: $i,X15: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X13 @ X15 ) )
      = X13 ) ),
    inference(inj_rec,[status(thm)],['87'])).

thf('89',plain,
    ( ( ( '#_fresh_sk1' @ ( k4_tarski @ sk_B @ sk_C_1 ) )
      = ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['86','88'])).

thf('90',plain,(
    ! [X13: $i,X15: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X13 @ X15 ) )
      = X13 ) ),
    inference(inj_rec,[status(thm)],['87'])).

thf('91',plain,
    ( ( sk_B
      = ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','35'])).

thf('93',plain,
    ( ( k8_filter_1 @ sk_A )
    = ( a_1_0_filter_1 @ sk_A ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('94',plain,(
    ! [X5: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ ( a_1_0_filter_1 @ X5 ) )
      | ( r3_lattices @ X5 @ ( sk_C @ X5 @ X7 ) @ ( sk_D @ X5 @ X7 ) )
      | ~ ( l3_lattices @ X5 )
      | ~ ( v10_lattices @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_1_0_filter_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattices @ sk_A @ ( sk_C @ sk_A @ X0 ) @ ( sk_D @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattices @ sk_A @ ( sk_C @ sk_A @ X0 ) @ ( sk_D @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( sk_C @ sk_A @ X0 ) @ ( sk_D @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['92','100'])).

thf('102',plain,
    ( ( r3_lattices @ sk_A @ sk_B @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['91','101'])).

thf('103',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ sk_B @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,
    ( ( r3_lattices @ sk_A @ sk_B @ sk_C_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['85','103'])).

thf('105',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B @ sk_C_1 )
   <= ~ ( r3_lattices @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('107',plain,(
    ~ ( r3_lattices @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['10','32'])).

thf('108',plain,(
    ~ ( r3_lattices @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['106','107'])).

thf('109',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['105','108'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('110',plain,(
    ! [X3: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 )
      | ( v2_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('111',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ~ ( l1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( l1_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['0','113'])).

thf('115',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('116',plain,(
    ! [X2: $i] :
      ( ( l1_lattices @ X2 )
      | ~ ( l3_lattices @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('117',plain,(
    l1_lattices @ sk_A ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    $false ),
    inference(demod,[status(thm)],['114','117'])).


%------------------------------------------------------------------------------
