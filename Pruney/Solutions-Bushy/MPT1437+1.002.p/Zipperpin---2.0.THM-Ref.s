%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1437+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2WhMOOOHym

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:39 EST 2020

% Result     : Theorem 8.26s
% Output     : Refutation 8.26s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 824 expanded)
%              Number of leaves         :   30 ( 229 expanded)
%              Depth                    :   29
%              Number of atoms          : 1460 (14812 expanded)
%              Number of equality atoms :   45 ( 172 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf('#_fresh_sk2_type',type,(
    '#_fresh_sk2': $i > $i )).

thf(v10_lattices_type,type,(
    v10_lattices: $i > $o )).

thf(l1_lattices_type,type,(
    l1_lattices: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(l3_lattices_type,type,(
    l3_lattices: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_domain_1_type,type,(
    k1_domain_1: $i > $i > $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(a_1_0_filter_1_type,type,(
    a_1_0_filter_1: $i > $i )).

thf(r3_lattices_type,type,(
    r3_lattices: $i > $i > $i > $o )).

thf('#_fresh_sk1_type',type,(
    '#_fresh_sk1': $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l2_lattices_type,type,(
    l2_lattices: $i > $o )).

thf(k8_filter_1_type,type,(
    k8_filter_1: $i > $i )).

thf(dt_l2_lattices,axiom,(
    ! [A: $i] :
      ( ( l2_lattices @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( l1_struct_0 @ X2 )
      | ~ ( l2_lattices @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_l2_lattices])).

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
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ X10 )
      | ( v1_xboole_0 @ X11 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( ( k1_domain_1 @ X10 @ X11 @ X9 @ X12 )
        = ( k4_tarski @ X9 @ X12 ) ) ) ),
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
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ( X8
       != ( k1_domain_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X6 ) @ X5 @ X7 ) )
      | ~ ( r3_lattices @ X6 @ X5 @ X7 )
      | ( r2_hidden @ X8 @ ( a_1_0_filter_1 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_1_0_filter_1])).

thf('15',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v2_struct_0 @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ~ ( l3_lattices @ X6 )
      | ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X6 ) @ X5 @ X7 ) @ ( a_1_0_filter_1 @ X6 ) )
      | ~ ( r3_lattices @ X6 @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X6 ) )
      | ~ ( m1_subset_1 @ X5 @ ( u1_struct_0 @ X6 ) ) ) ),
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

thf(d8_filter_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v10_lattices @ A )
        & ( l3_lattices @ A ) )
     => ( ( k8_filter_1 @ A )
        = ( a_1_0_filter_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X1: $i] :
      ( ( ( k8_filter_1 @ X1 )
        = ( a_1_0_filter_1 @ X1 ) )
      | ~ ( l3_lattices @ X1 )
      | ~ ( v10_lattices @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d8_filter_1])).

thf('18',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ~ ( v10_lattices @ sk_A )
    | ~ ( l3_lattices @ sk_A )
    | ( ( k8_filter_1 @ sk_A )
      = ( a_1_0_filter_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( ( k8_filter_1 @ sk_A )
    = ( a_1_0_filter_1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r3_lattices @ sk_A @ X0 @ sk_C_1 )
      | ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ X0 @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','22','23','24'])).

thf('26',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
    | ~ ( r3_lattices @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['12','25'])).

thf('27',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
   <= ( r3_lattices @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
   <= ~ ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['9'])).

thf('31',plain,
    ( ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
    | ~ ( r3_lattices @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
    | ( r3_lattices @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['7'])).

thf('33',plain,(
    r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['10','31','32'])).

thf('34',plain,(
    r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['8','33'])).

thf('35',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','34'])).

thf('36',plain,
    ( ( k8_filter_1 @ sk_A )
    = ( a_1_0_filter_1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('37',plain,(
    ! [X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ ( a_1_0_filter_1 @ X6 ) )
      | ( X8
        = ( k1_domain_1 @ ( u1_struct_0 @ X6 ) @ ( u1_struct_0 @ X6 ) @ ( sk_C @ X6 @ X8 ) @ ( sk_D @ X6 @ X8 ) ) )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_1_0_filter_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( X0
        = ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_A @ X0 ) @ ( sk_D @ sk_A @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( X0
        = ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_A @ X0 ) @ ( sk_D @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_A @ X0 ) @ ( sk_D @ sk_A @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k4_tarski @ sk_B @ sk_C_1 )
      = ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,
    ( ( ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 )
      = ( k4_tarski @ sk_B @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('46',plain,
    ( ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
   <= ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('47',plain,
    ( ( k8_filter_1 @ sk_A )
    = ( a_1_0_filter_1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('48',plain,(
    ! [X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ ( a_1_0_filter_1 @ X6 ) )
      | ( m1_subset_1 @ ( sk_D @ X6 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_1_0_filter_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_D @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_A @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','54'])).

thf('56',plain,(
    r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['10','31','32'])).

thf('57',plain,(
    m1_subset_1 @ ( sk_D @ sk_A @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['45','57'])).

thf('59',plain,
    ( ( ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 )
      = ( k4_tarski @ sk_B @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('60',plain,
    ( ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
   <= ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['7'])).

thf('61',plain,
    ( ( k8_filter_1 @ sk_A )
    = ( a_1_0_filter_1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('62',plain,(
    ! [X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ ( a_1_0_filter_1 @ X6 ) )
      | ( m1_subset_1 @ ( sk_C @ X6 @ X8 ) @ ( u1_struct_0 @ X6 ) )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_1_0_filter_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_C @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ sk_A @ X0 ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_A @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) )
   <= ( r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','68'])).

thf('70',plain,(
    r2_hidden @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['10','31','32'])).

thf('71',plain,(
    m1_subset_1 @ ( sk_C @ sk_A @ ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['69','70'])).

thf('72',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['59','71'])).

thf('73',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ X10 )
      | ( v1_xboole_0 @ X11 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X12 @ X11 )
      | ( ( k1_domain_1 @ X10 @ X11 @ X9 @ X12 )
        = ( k4_tarski @ X9 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_domain_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ X0 )
        = ( k4_tarski @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ X1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 )
      | ( ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ X1 @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ X0 )
        = ( k4_tarski @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) )
      = ( k4_tarski @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','75'])).

thf('77',plain,
    ( ( ( k1_domain_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) )
      = ( k4_tarski @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ( ( k4_tarski @ sk_B @ sk_C_1 )
      = ( k4_tarski @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['44','77'])).

thf('79',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k4_tarski @ sk_B @ sk_C_1 )
      = ( k4_tarski @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf(t33_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( k4_tarski @ A @ B )
        = ( k4_tarski @ C @ D ) )
     => ( ( A = C )
        & ( B = D ) ) ) )).

thf('80',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X21 = X20 )
      | ( ( k4_tarski @ X19 @ X21 )
       != ( k4_tarski @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('81',plain,(
    ! [X19: $i,X21: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X19 @ X21 ) )
      = X21 ) ),
    inference(inj_rec,[status(thm)],['80'])).

thf('82',plain,
    ( ( ( '#_fresh_sk2' @ ( k4_tarski @ sk_B @ sk_C_1 ) )
      = ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['79','81'])).

thf('83',plain,(
    ! [X19: $i,X21: $i] :
      ( ( '#_fresh_sk2' @ ( k4_tarski @ X19 @ X21 ) )
      = X21 ) ),
    inference(inj_rec,[status(thm)],['80'])).

thf('84',plain,
    ( ( sk_C_1
      = ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k4_tarski @ sk_B @ sk_C_1 )
      = ( k4_tarski @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('86',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19 = X18 )
      | ( ( k4_tarski @ X19 @ X21 )
       != ( k4_tarski @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t33_zfmisc_1])).

thf('87',plain,(
    ! [X19: $i,X21: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X19 @ X21 ) )
      = X19 ) ),
    inference(inj_rec,[status(thm)],['86'])).

thf('88',plain,
    ( ( ( '#_fresh_sk1' @ ( k4_tarski @ sk_B @ sk_C_1 ) )
      = ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['85','87'])).

thf('89',plain,(
    ! [X19: $i,X21: $i] :
      ( ( '#_fresh_sk1' @ ( k4_tarski @ X19 @ X21 ) )
      = X19 ) ),
    inference(inj_rec,[status(thm)],['86'])).

thf('90',plain,
    ( ( sk_B
      = ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_B @ sk_C_1 ) @ ( k8_filter_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','34'])).

thf('92',plain,
    ( ( k8_filter_1 @ sk_A )
    = ( a_1_0_filter_1 @ sk_A ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('93',plain,(
    ! [X6: $i,X8: $i] :
      ( ~ ( r2_hidden @ X8 @ ( a_1_0_filter_1 @ X6 ) )
      | ( r3_lattices @ X6 @ ( sk_C @ X6 @ X8 ) @ ( sk_D @ X6 @ X8 ) )
      | ~ ( l3_lattices @ X6 )
      | ~ ( v10_lattices @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_1_0_filter_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v10_lattices @ sk_A )
      | ~ ( l3_lattices @ sk_A )
      | ( r3_lattices @ sk_A @ ( sk_C @ sk_A @ X0 ) @ ( sk_D @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v10_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r3_lattices @ sk_A @ ( sk_C @ sk_A @ X0 ) @ ( sk_D @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r3_lattices @ sk_A @ ( sk_C @ sk_A @ X0 ) @ ( sk_D @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k8_filter_1 @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ ( sk_C @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['91','99'])).

thf('101',plain,
    ( ( r3_lattices @ sk_A @ sk_B @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['90','100'])).

thf('102',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ sk_B @ ( sk_D @ sk_A @ ( k4_tarski @ sk_B @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( r3_lattices @ sk_A @ sk_B @ sk_C_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['84','102'])).

thf('104',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r3_lattices @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ~ ( r3_lattices @ sk_A @ sk_B @ sk_C_1 )
   <= ~ ( r3_lattices @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('106',plain,(
    ~ ( r3_lattices @ sk_A @ sk_B @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['10','31'])).

thf('107',plain,(
    ~ ( r3_lattices @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['105','106'])).

thf('108',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['104','107'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('109',plain,(
    ! [X4: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 )
      | ( v2_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('110',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    ~ ( l1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ~ ( l2_lattices @ sk_A ) ),
    inference('sup-',[status(thm)],['0','112'])).

thf('114',plain,(
    l3_lattices @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l3_lattices,axiom,(
    ! [A: $i] :
      ( ( l3_lattices @ A )
     => ( ( l1_lattices @ A )
        & ( l2_lattices @ A ) ) ) )).

thf('115',plain,(
    ! [X3: $i] :
      ( ( l2_lattices @ X3 )
      | ~ ( l3_lattices @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_l3_lattices])).

thf('116',plain,(
    l2_lattices @ sk_A ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    $false ),
    inference(demod,[status(thm)],['113','116'])).


%------------------------------------------------------------------------------
