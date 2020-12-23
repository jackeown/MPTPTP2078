%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FBprWKkWLu

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:58 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 777 expanded)
%              Number of leaves         :   31 ( 227 expanded)
%              Depth                    :   33
%              Number of atoms          : 1584 (13961 expanded)
%              Number of equality atoms :   41 ( 170 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t52_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_orders_2 @ A @ B @ C )
              <=> ( r2_hidden @ B @ ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_orders_2 @ A @ B @ C )
                <=> ( r2_hidden @ B @ ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ X18 )
      | ( ( k6_domain_1 @ X18 @ X19 )
        = ( k1_tarski @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ X10 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(fraenkel_a_2_1_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v3_orders_2 @ B )
        & ( v4_orders_2 @ B )
        & ( v5_orders_2 @ B )
        & ( l1_orders_2 @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
     => ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) )
      <=> ? [D: $i] :
            ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
               => ( ( r2_hidden @ E @ C )
                 => ( r2_orders_2 @ B @ D @ E ) ) )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i,X16: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( r2_hidden @ X16 @ ( a_2_1_orders_2 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X13 ) )
      | ( X16 != X17 )
      | ( r2_hidden @ ( sk_E @ X17 @ X14 @ X13 ) @ X14 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('11',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ( r2_hidden @ ( sk_E @ X17 @ X14 @ X13 ) @ X14 )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X13 ) )
      | ( r2_hidden @ X17 @ ( a_2_1_orders_2 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v2_struct_0 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k1_tarski @ sk_C ) @ sk_A ) @ ( k1_tarski @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k1_tarski @ sk_C ) @ sk_A ) @ ( k1_tarski @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','17'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('19',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('21',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['18','23'])).

thf('25',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('26',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d13_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k2_orders_2 @ A @ B )
            = ( a_2_1_orders_2 @ A @ B ) ) ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k2_orders_2 @ X9 @ X8 )
        = ( a_2_1_orders_2 @ X9 @ X8 ) )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( v5_orders_2 @ X9 )
      | ~ ( v4_orders_2 @ X9 )
      | ~ ( v3_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['25','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['38'])).

thf('40',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['38'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('43',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,
    ( ( ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['42','44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('47',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( X16
        = ( sk_D_1 @ X14 @ X13 @ X16 ) )
      | ~ ( r2_hidden @ X16 @ ( a_2_1_orders_2 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( X0
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( X0
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','49','50','51','52'])).

thf('54',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['45','53'])).

thf('55',plain,
    ( ( ( sk_B
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('60',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','60'])).

thf('62',plain,
    ( ( ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['42','44'])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('64',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ( r2_orders_2 @ X13 @ ( sk_D_1 @ X14 @ X13 @ X16 ) @ X15 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( a_2_1_orders_2 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_C ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_C ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ X0 )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['62','70'])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C ) )
        | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['61','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['57','77'])).

thf('79',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['38'])).

thf('81',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('82',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('83',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('85',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['83','86'])).

thf('88',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['41','89'])).

thf('91',plain,
    ( ~ ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['40','90'])).

thf('92',plain,
    ( ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['24','91'])).

thf('93',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
      = sk_C ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
      = sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('97',plain,(
    ! [X13: $i,X14: $i,X16: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( r2_hidden @ X16 @ ( a_2_1_orders_2 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X13 ) )
      | ( X16 != X17 )
      | ~ ( r2_orders_2 @ X13 @ X17 @ ( sk_E @ X17 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('98',plain,(
    ! [X13: $i,X14: $i,X17: $i] :
      ( ~ ( r2_orders_2 @ X13 @ X17 @ ( sk_E @ X17 @ X14 @ X13 ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X13 ) )
      | ( r2_hidden @ X17 @ ( a_2_1_orders_2 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( v2_struct_0 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_E @ X0 @ ( k1_tarski @ sk_C ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['96','98'])).

thf('100',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_E @ X0 @ ( k1_tarski @ sk_C ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['99','100','101','102','103'])).

thf('105',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','104'])).

thf('106',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['43'])).

thf('107',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['43'])).

thf('108',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['41','89','107'])).

thf('109',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['106','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['105','109','110'])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['112','113'])).

thf('115',plain,
    ( ~ ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['40','90'])).

thf('116',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('118',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['84','85'])).

thf('120',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    $false ),
    inference(demod,[status(thm)],['0','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FBprWKkWLu
% 0.15/0.35  % Computer   : n003.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:12:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.36  % Running in FO mode
% 0.58/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.79  % Solved by: fo/fo7.sh
% 0.58/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.79  % done 540 iterations in 0.324s
% 0.58/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.79  % SZS output start Refutation
% 0.58/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.79  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.58/0.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.79  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.58/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.79  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.58/0.79  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.79  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.79  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.58/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.79  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.79  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.58/0.79  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.58/0.79  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.58/0.79  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.58/0.79  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.58/0.79  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 0.58/0.79  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.58/0.79  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.58/0.79  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.58/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.79  thf(t52_orders_2, conjecture,
% 0.58/0.79    (![A:$i]:
% 0.58/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.58/0.79         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.58/0.79       ( ![B:$i]:
% 0.58/0.79         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.79           ( ![C:$i]:
% 0.58/0.79             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.79               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.58/0.79                 ( r2_hidden @
% 0.58/0.79                   B @ 
% 0.58/0.79                   ( k2_orders_2 @
% 0.58/0.79                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.58/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.79    (~( ![A:$i]:
% 0.58/0.79        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.58/0.79            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.58/0.79          ( ![B:$i]:
% 0.58/0.79            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.79              ( ![C:$i]:
% 0.58/0.79                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.58/0.79                  ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.58/0.79                    ( r2_hidden @
% 0.58/0.79                      B @ 
% 0.58/0.79                      ( k2_orders_2 @
% 0.58/0.79                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.58/0.79    inference('cnf.neg', [status(esa)], [t52_orders_2])).
% 0.58/0.79  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('2', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(redefinition_k6_domain_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.58/0.79       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.58/0.79  thf('3', plain,
% 0.58/0.79      (![X18 : $i, X19 : $i]:
% 0.58/0.79         ((v1_xboole_0 @ X18)
% 0.58/0.79          | ~ (m1_subset_1 @ X19 @ X18)
% 0.58/0.79          | ((k6_domain_1 @ X18 @ X19) = (k1_tarski @ X19)))),
% 0.58/0.79      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.58/0.79  thf('4', plain,
% 0.58/0.79      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.58/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.79  thf('5', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(dt_k6_domain_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.58/0.79       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.58/0.79  thf('6', plain,
% 0.58/0.79      (![X10 : $i, X11 : $i]:
% 0.58/0.79         ((v1_xboole_0 @ X10)
% 0.58/0.79          | ~ (m1_subset_1 @ X11 @ X10)
% 0.58/0.79          | (m1_subset_1 @ (k6_domain_1 @ X10 @ X11) @ (k1_zfmisc_1 @ X10)))),
% 0.58/0.79      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.58/0.79  thf('7', plain,
% 0.58/0.79      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.58/0.79         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.79  thf('8', plain,
% 0.58/0.79      (((m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.58/0.79         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['4', '7'])).
% 0.58/0.79  thf('9', plain,
% 0.58/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.58/0.79           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.58/0.79      inference('simplify', [status(thm)], ['8'])).
% 0.58/0.79  thf(fraenkel_a_2_1_orders_2, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.58/0.79         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.58/0.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.58/0.79       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 0.58/0.79         ( ?[D:$i]:
% 0.58/0.79           ( ( ![E:$i]:
% 0.58/0.79               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.58/0.79                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 0.58/0.79             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.58/0.79  thf('10', plain,
% 0.58/0.79      (![X13 : $i, X14 : $i, X16 : $i, X17 : $i]:
% 0.58/0.79         (~ (l1_orders_2 @ X13)
% 0.58/0.79          | ~ (v5_orders_2 @ X13)
% 0.58/0.79          | ~ (v4_orders_2 @ X13)
% 0.58/0.79          | ~ (v3_orders_2 @ X13)
% 0.58/0.79          | (v2_struct_0 @ X13)
% 0.58/0.79          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.58/0.79          | (r2_hidden @ X16 @ (a_2_1_orders_2 @ X13 @ X14))
% 0.58/0.79          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X13))
% 0.58/0.79          | ((X16) != (X17))
% 0.58/0.79          | (r2_hidden @ (sk_E @ X17 @ X14 @ X13) @ X14))),
% 0.58/0.79      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.58/0.79  thf('11', plain,
% 0.58/0.79      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.58/0.79         ((r2_hidden @ (sk_E @ X17 @ X14 @ X13) @ X14)
% 0.58/0.79          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X13))
% 0.58/0.79          | (r2_hidden @ X17 @ (a_2_1_orders_2 @ X13 @ X14))
% 0.58/0.79          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.58/0.79          | (v2_struct_0 @ X13)
% 0.58/0.79          | ~ (v3_orders_2 @ X13)
% 0.58/0.79          | ~ (v4_orders_2 @ X13)
% 0.58/0.79          | ~ (v5_orders_2 @ X13)
% 0.58/0.79          | ~ (l1_orders_2 @ X13))),
% 0.58/0.79      inference('simplify', [status(thm)], ['10'])).
% 0.58/0.79  thf('12', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79          | ~ (l1_orders_2 @ sk_A)
% 0.58/0.79          | ~ (v5_orders_2 @ sk_A)
% 0.58/0.79          | ~ (v4_orders_2 @ sk_A)
% 0.58/0.79          | ~ (v3_orders_2 @ sk_A)
% 0.58/0.79          | (v2_struct_0 @ sk_A)
% 0.58/0.79          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.58/0.79          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79          | (r2_hidden @ (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A) @ 
% 0.58/0.79             (k1_tarski @ sk_C)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['9', '11'])).
% 0.58/0.79  thf('13', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('14', plain, ((v5_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('15', plain, ((v4_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('16', plain, ((v3_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('17', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79          | (v2_struct_0 @ sk_A)
% 0.58/0.79          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.58/0.79          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79          | (r2_hidden @ (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A) @ 
% 0.58/0.79             (k1_tarski @ sk_C)))),
% 0.58/0.79      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.58/0.79  thf('18', plain,
% 0.58/0.79      (((r2_hidden @ (sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) @ 
% 0.58/0.79         (k1_tarski @ sk_C))
% 0.58/0.79        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.58/0.79        | (v2_struct_0 @ sk_A)
% 0.58/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['1', '17'])).
% 0.58/0.79  thf(t69_enumset1, axiom,
% 0.58/0.79    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.58/0.79  thf('19', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.58/0.79      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.79  thf(d2_tarski, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i]:
% 0.58/0.79     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.58/0.79       ( ![D:$i]:
% 0.58/0.79         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.58/0.79  thf('20', plain,
% 0.58/0.79      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X4 @ X2)
% 0.58/0.79          | ((X4) = (X3))
% 0.58/0.79          | ((X4) = (X0))
% 0.58/0.79          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.58/0.79      inference('cnf', [status(esa)], [d2_tarski])).
% 0.58/0.79  thf('21', plain,
% 0.58/0.79      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.58/0.79         (((X4) = (X0))
% 0.58/0.79          | ((X4) = (X3))
% 0.58/0.79          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.58/0.79      inference('simplify', [status(thm)], ['20'])).
% 0.58/0.79  thf('22', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['19', '21'])).
% 0.58/0.79  thf('23', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.58/0.79      inference('simplify', [status(thm)], ['22'])).
% 0.58/0.79  thf('24', plain,
% 0.58/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79        | (v2_struct_0 @ sk_A)
% 0.58/0.79        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.58/0.79        | ((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['18', '23'])).
% 0.58/0.79  thf('25', plain,
% 0.58/0.79      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.58/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['2', '3'])).
% 0.58/0.79  thf('26', plain,
% 0.58/0.79      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.58/0.79         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.58/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.79  thf(d13_orders_2, axiom,
% 0.58/0.79    (![A:$i]:
% 0.58/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.58/0.79         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.58/0.79       ( ![B:$i]:
% 0.58/0.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.58/0.79           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 0.58/0.79  thf('27', plain,
% 0.58/0.79      (![X8 : $i, X9 : $i]:
% 0.58/0.79         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.58/0.79          | ((k2_orders_2 @ X9 @ X8) = (a_2_1_orders_2 @ X9 @ X8))
% 0.58/0.79          | ~ (l1_orders_2 @ X9)
% 0.58/0.79          | ~ (v5_orders_2 @ X9)
% 0.58/0.79          | ~ (v4_orders_2 @ X9)
% 0.58/0.79          | ~ (v3_orders_2 @ X9)
% 0.58/0.79          | (v2_struct_0 @ X9))),
% 0.58/0.79      inference('cnf', [status(esa)], [d13_orders_2])).
% 0.58/0.79  thf('28', plain,
% 0.58/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79        | (v2_struct_0 @ sk_A)
% 0.58/0.79        | ~ (v3_orders_2 @ sk_A)
% 0.58/0.79        | ~ (v4_orders_2 @ sk_A)
% 0.58/0.79        | ~ (v5_orders_2 @ sk_A)
% 0.58/0.79        | ~ (l1_orders_2 @ sk_A)
% 0.58/0.79        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.58/0.79            = (a_2_1_orders_2 @ sk_A @ 
% 0.58/0.79               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.58/0.79      inference('sup-', [status(thm)], ['26', '27'])).
% 0.58/0.79  thf('29', plain, ((v3_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('30', plain, ((v4_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('31', plain, ((v5_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('32', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('33', plain,
% 0.58/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79        | (v2_struct_0 @ sk_A)
% 0.58/0.79        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.58/0.79            = (a_2_1_orders_2 @ sk_A @ 
% 0.58/0.79               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.58/0.79      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 0.58/0.79  thf('34', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('35', plain,
% 0.58/0.79      ((((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.58/0.79          = (a_2_1_orders_2 @ sk_A @ 
% 0.58/0.79             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.58/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.79      inference('clc', [status(thm)], ['33', '34'])).
% 0.58/0.79  thf('36', plain,
% 0.58/0.79      ((((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.58/0.79          = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.58/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['25', '35'])).
% 0.58/0.79  thf('37', plain,
% 0.58/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.58/0.79            = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C))))),
% 0.58/0.79      inference('simplify', [status(thm)], ['36'])).
% 0.58/0.79  thf('38', plain,
% 0.58/0.79      ((~ (r2_hidden @ sk_B @ 
% 0.58/0.79           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.58/0.79        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('39', plain,
% 0.58/0.79      ((~ (r2_hidden @ sk_B @ 
% 0.58/0.79           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.58/0.79         <= (~
% 0.58/0.79             ((r2_hidden @ sk_B @ 
% 0.58/0.79               (k2_orders_2 @ sk_A @ 
% 0.58/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.58/0.79      inference('split', [status(esa)], ['38'])).
% 0.58/0.79  thf('40', plain,
% 0.58/0.79      (((~ (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.58/0.79         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.58/0.79         <= (~
% 0.58/0.79             ((r2_hidden @ sk_B @ 
% 0.58/0.79               (k2_orders_2 @ sk_A @ 
% 0.58/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.58/0.79      inference('sup-', [status(thm)], ['37', '39'])).
% 0.58/0.79  thf('41', plain,
% 0.58/0.79      (~
% 0.58/0.79       ((r2_hidden @ sk_B @ 
% 0.58/0.79         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) | 
% 0.58/0.79       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.58/0.79      inference('split', [status(esa)], ['38'])).
% 0.58/0.79  thf('42', plain,
% 0.58/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.58/0.79            = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C))))),
% 0.58/0.79      inference('simplify', [status(thm)], ['36'])).
% 0.58/0.79  thf('43', plain,
% 0.58/0.79      (((r2_hidden @ sk_B @ 
% 0.58/0.79         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.58/0.79        | (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('44', plain,
% 0.58/0.79      (((r2_hidden @ sk_B @ 
% 0.58/0.79         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.58/0.79         <= (((r2_hidden @ sk_B @ 
% 0.58/0.79               (k2_orders_2 @ sk_A @ 
% 0.58/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.58/0.79      inference('split', [status(esa)], ['43'])).
% 0.58/0.79  thf('45', plain,
% 0.58/0.79      ((((r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.58/0.79         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.58/0.79         <= (((r2_hidden @ sk_B @ 
% 0.58/0.79               (k2_orders_2 @ sk_A @ 
% 0.58/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.58/0.79      inference('sup+', [status(thm)], ['42', '44'])).
% 0.58/0.79  thf('46', plain,
% 0.58/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.58/0.79           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.58/0.79      inference('simplify', [status(thm)], ['8'])).
% 0.58/0.79  thf('47', plain,
% 0.58/0.79      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.58/0.79         (~ (l1_orders_2 @ X13)
% 0.58/0.79          | ~ (v5_orders_2 @ X13)
% 0.58/0.79          | ~ (v4_orders_2 @ X13)
% 0.58/0.79          | ~ (v3_orders_2 @ X13)
% 0.58/0.79          | (v2_struct_0 @ X13)
% 0.58/0.79          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.58/0.79          | ((X16) = (sk_D_1 @ X14 @ X13 @ X16))
% 0.58/0.79          | ~ (r2_hidden @ X16 @ (a_2_1_orders_2 @ X13 @ X14)))),
% 0.58/0.79      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.58/0.79  thf('48', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.58/0.79          | ((X0) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0))
% 0.58/0.79          | (v2_struct_0 @ sk_A)
% 0.58/0.79          | ~ (v3_orders_2 @ sk_A)
% 0.58/0.79          | ~ (v4_orders_2 @ sk_A)
% 0.58/0.79          | ~ (v5_orders_2 @ sk_A)
% 0.58/0.79          | ~ (l1_orders_2 @ sk_A))),
% 0.58/0.79      inference('sup-', [status(thm)], ['46', '47'])).
% 0.58/0.79  thf('49', plain, ((v3_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('50', plain, ((v4_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('51', plain, ((v5_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('52', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('53', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.58/0.79          | ((X0) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0))
% 0.58/0.79          | (v2_struct_0 @ sk_A))),
% 0.58/0.79      inference('demod', [status(thm)], ['48', '49', '50', '51', '52'])).
% 0.58/0.79  thf('54', plain,
% 0.58/0.79      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79         | (v2_struct_0 @ sk_A)
% 0.58/0.79         | ((sk_B) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B))
% 0.58/0.79         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.58/0.79         <= (((r2_hidden @ sk_B @ 
% 0.58/0.79               (k2_orders_2 @ sk_A @ 
% 0.58/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.58/0.79      inference('sup-', [status(thm)], ['45', '53'])).
% 0.58/0.79  thf('55', plain,
% 0.58/0.79      (((((sk_B) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B))
% 0.58/0.79         | (v2_struct_0 @ sk_A)
% 0.58/0.79         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.58/0.79         <= (((r2_hidden @ sk_B @ 
% 0.58/0.79               (k2_orders_2 @ sk_A @ 
% 0.58/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.58/0.79      inference('simplify', [status(thm)], ['54'])).
% 0.58/0.79  thf('56', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('57', plain,
% 0.58/0.79      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79         | ((sk_B) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B))))
% 0.58/0.79         <= (((r2_hidden @ sk_B @ 
% 0.58/0.79               (k2_orders_2 @ sk_A @ 
% 0.58/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.58/0.79      inference('clc', [status(thm)], ['55', '56'])).
% 0.58/0.79  thf('58', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.58/0.79      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.79  thf('59', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.58/0.79         (((X1) != (X0))
% 0.58/0.79          | (r2_hidden @ X1 @ X2)
% 0.58/0.79          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.58/0.79      inference('cnf', [status(esa)], [d2_tarski])).
% 0.58/0.79  thf('60', plain,
% 0.58/0.79      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.58/0.79      inference('simplify', [status(thm)], ['59'])).
% 0.58/0.79  thf('61', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.58/0.79      inference('sup+', [status(thm)], ['58', '60'])).
% 0.58/0.79  thf('62', plain,
% 0.58/0.79      ((((r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.58/0.79         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.58/0.79         <= (((r2_hidden @ sk_B @ 
% 0.58/0.79               (k2_orders_2 @ sk_A @ 
% 0.58/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.58/0.79      inference('sup+', [status(thm)], ['42', '44'])).
% 0.58/0.79  thf('63', plain,
% 0.58/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.58/0.79           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.58/0.79      inference('simplify', [status(thm)], ['8'])).
% 0.58/0.79  thf('64', plain,
% 0.58/0.79      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.58/0.79         (~ (l1_orders_2 @ X13)
% 0.58/0.79          | ~ (v5_orders_2 @ X13)
% 0.58/0.79          | ~ (v4_orders_2 @ X13)
% 0.58/0.79          | ~ (v3_orders_2 @ X13)
% 0.58/0.79          | (v2_struct_0 @ X13)
% 0.58/0.79          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.58/0.79          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 0.58/0.79          | (r2_orders_2 @ X13 @ (sk_D_1 @ X14 @ X13 @ X16) @ X15)
% 0.58/0.79          | ~ (r2_hidden @ X15 @ X14)
% 0.58/0.79          | ~ (r2_hidden @ X16 @ (a_2_1_orders_2 @ X13 @ X14)))),
% 0.58/0.79      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.58/0.79  thf('65', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.58/0.79          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_C))
% 0.58/0.79          | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0) @ 
% 0.58/0.79             X1)
% 0.58/0.79          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.58/0.79          | (v2_struct_0 @ sk_A)
% 0.58/0.79          | ~ (v3_orders_2 @ sk_A)
% 0.58/0.79          | ~ (v4_orders_2 @ sk_A)
% 0.58/0.79          | ~ (v5_orders_2 @ sk_A)
% 0.58/0.79          | ~ (l1_orders_2 @ sk_A))),
% 0.58/0.79      inference('sup-', [status(thm)], ['63', '64'])).
% 0.58/0.79  thf('66', plain, ((v3_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('67', plain, ((v4_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('68', plain, ((v5_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('69', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('70', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.58/0.79          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_C))
% 0.58/0.79          | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0) @ 
% 0.58/0.79             X1)
% 0.58/0.79          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.58/0.79          | (v2_struct_0 @ sk_A))),
% 0.58/0.79      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 0.58/0.79  thf('71', plain,
% 0.58/0.79      ((![X0 : $i]:
% 0.58/0.79          ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79           | (v2_struct_0 @ sk_A)
% 0.58/0.79           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79           | (r2_orders_2 @ sk_A @ 
% 0.58/0.79              (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ X0)
% 0.58/0.79           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_C))
% 0.58/0.79           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.58/0.79         <= (((r2_hidden @ sk_B @ 
% 0.58/0.79               (k2_orders_2 @ sk_A @ 
% 0.58/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.58/0.79      inference('sup-', [status(thm)], ['62', '70'])).
% 0.58/0.79  thf('72', plain,
% 0.58/0.79      ((![X0 : $i]:
% 0.58/0.79          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_C))
% 0.58/0.79           | (r2_orders_2 @ sk_A @ 
% 0.58/0.79              (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ X0)
% 0.58/0.79           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79           | (v2_struct_0 @ sk_A)
% 0.58/0.79           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.58/0.79         <= (((r2_hidden @ sk_B @ 
% 0.58/0.79               (k2_orders_2 @ sk_A @ 
% 0.58/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.58/0.79      inference('simplify', [status(thm)], ['71'])).
% 0.58/0.79  thf('73', plain,
% 0.58/0.79      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79         | (v2_struct_0 @ sk_A)
% 0.58/0.79         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.58/0.79         | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ 
% 0.58/0.79            sk_C)))
% 0.58/0.79         <= (((r2_hidden @ sk_B @ 
% 0.58/0.79               (k2_orders_2 @ sk_A @ 
% 0.58/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.58/0.79      inference('sup-', [status(thm)], ['61', '72'])).
% 0.58/0.79  thf('74', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('75', plain,
% 0.58/0.79      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79         | (v2_struct_0 @ sk_A)
% 0.58/0.79         | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ 
% 0.58/0.79            sk_C)))
% 0.58/0.79         <= (((r2_hidden @ sk_B @ 
% 0.58/0.79               (k2_orders_2 @ sk_A @ 
% 0.58/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.58/0.79      inference('demod', [status(thm)], ['73', '74'])).
% 0.58/0.79  thf('76', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('77', plain,
% 0.58/0.79      ((((r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ 
% 0.58/0.79          sk_C)
% 0.58/0.79         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.58/0.79         <= (((r2_hidden @ sk_B @ 
% 0.58/0.79               (k2_orders_2 @ sk_A @ 
% 0.58/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.58/0.79      inference('clc', [status(thm)], ['75', '76'])).
% 0.58/0.79  thf('78', plain,
% 0.58/0.79      ((((r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.58/0.79         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.58/0.79         <= (((r2_hidden @ sk_B @ 
% 0.58/0.79               (k2_orders_2 @ sk_A @ 
% 0.58/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.58/0.79      inference('sup+', [status(thm)], ['57', '77'])).
% 0.58/0.79  thf('79', plain,
% 0.58/0.79      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79         | (r2_orders_2 @ sk_A @ sk_B @ sk_C)))
% 0.58/0.79         <= (((r2_hidden @ sk_B @ 
% 0.58/0.79               (k2_orders_2 @ sk_A @ 
% 0.58/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.58/0.79      inference('simplify', [status(thm)], ['78'])).
% 0.58/0.79  thf('80', plain,
% 0.58/0.79      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.58/0.79         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.58/0.79      inference('split', [status(esa)], ['38'])).
% 0.58/0.79  thf('81', plain,
% 0.58/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.58/0.79         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.58/0.79             ((r2_hidden @ sk_B @ 
% 0.58/0.79               (k2_orders_2 @ sk_A @ 
% 0.58/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.58/0.79      inference('sup-', [status(thm)], ['79', '80'])).
% 0.58/0.79  thf(fc2_struct_0, axiom,
% 0.58/0.79    (![A:$i]:
% 0.58/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.58/0.79       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.58/0.79  thf('82', plain,
% 0.58/0.79      (![X7 : $i]:
% 0.58/0.79         (~ (v1_xboole_0 @ (u1_struct_0 @ X7))
% 0.58/0.79          | ~ (l1_struct_0 @ X7)
% 0.58/0.79          | (v2_struct_0 @ X7))),
% 0.58/0.79      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.58/0.79  thf('83', plain,
% 0.58/0.79      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.58/0.79         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.58/0.79             ((r2_hidden @ sk_B @ 
% 0.58/0.79               (k2_orders_2 @ sk_A @ 
% 0.58/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.58/0.79      inference('sup-', [status(thm)], ['81', '82'])).
% 0.58/0.79  thf('84', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf(dt_l1_orders_2, axiom,
% 0.58/0.79    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.58/0.79  thf('85', plain,
% 0.58/0.79      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_orders_2 @ X12))),
% 0.58/0.79      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.58/0.79  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 0.58/0.79      inference('sup-', [status(thm)], ['84', '85'])).
% 0.58/0.79  thf('87', plain,
% 0.58/0.79      (((v2_struct_0 @ sk_A))
% 0.58/0.79         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.58/0.79             ((r2_hidden @ sk_B @ 
% 0.58/0.79               (k2_orders_2 @ sk_A @ 
% 0.58/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.58/0.79      inference('demod', [status(thm)], ['83', '86'])).
% 0.58/0.79  thf('88', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('89', plain,
% 0.58/0.79      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.58/0.79       ~
% 0.58/0.79       ((r2_hidden @ sk_B @ 
% 0.58/0.79         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.58/0.79      inference('sup-', [status(thm)], ['87', '88'])).
% 0.58/0.79  thf('90', plain,
% 0.58/0.79      (~
% 0.58/0.79       ((r2_hidden @ sk_B @ 
% 0.58/0.79         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.58/0.79      inference('sat_resolution*', [status(thm)], ['41', '89'])).
% 0.58/0.79  thf('91', plain,
% 0.58/0.79      ((~ (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.58/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.79      inference('simpl_trail', [status(thm)], ['40', '90'])).
% 0.58/0.79  thf('92', plain,
% 0.58/0.79      ((((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C))
% 0.58/0.79        | (v2_struct_0 @ sk_A)
% 0.58/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['24', '91'])).
% 0.58/0.79  thf('93', plain,
% 0.58/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79        | (v2_struct_0 @ sk_A)
% 0.58/0.79        | ((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C)))),
% 0.58/0.79      inference('simplify', [status(thm)], ['92'])).
% 0.58/0.79  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('95', plain,
% 0.58/0.79      ((((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C))
% 0.58/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.79      inference('clc', [status(thm)], ['93', '94'])).
% 0.58/0.79  thf('96', plain,
% 0.58/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.58/0.79           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.58/0.79      inference('simplify', [status(thm)], ['8'])).
% 0.58/0.79  thf('97', plain,
% 0.58/0.79      (![X13 : $i, X14 : $i, X16 : $i, X17 : $i]:
% 0.58/0.79         (~ (l1_orders_2 @ X13)
% 0.58/0.79          | ~ (v5_orders_2 @ X13)
% 0.58/0.79          | ~ (v4_orders_2 @ X13)
% 0.58/0.79          | ~ (v3_orders_2 @ X13)
% 0.58/0.79          | (v2_struct_0 @ X13)
% 0.58/0.79          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.58/0.79          | (r2_hidden @ X16 @ (a_2_1_orders_2 @ X13 @ X14))
% 0.58/0.79          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X13))
% 0.58/0.79          | ((X16) != (X17))
% 0.58/0.79          | ~ (r2_orders_2 @ X13 @ X17 @ (sk_E @ X17 @ X14 @ X13)))),
% 0.58/0.79      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.58/0.79  thf('98', plain,
% 0.58/0.79      (![X13 : $i, X14 : $i, X17 : $i]:
% 0.58/0.79         (~ (r2_orders_2 @ X13 @ X17 @ (sk_E @ X17 @ X14 @ X13))
% 0.58/0.79          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X13))
% 0.58/0.79          | (r2_hidden @ X17 @ (a_2_1_orders_2 @ X13 @ X14))
% 0.58/0.79          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.58/0.79          | (v2_struct_0 @ X13)
% 0.58/0.79          | ~ (v3_orders_2 @ X13)
% 0.58/0.79          | ~ (v4_orders_2 @ X13)
% 0.58/0.79          | ~ (v5_orders_2 @ X13)
% 0.58/0.79          | ~ (l1_orders_2 @ X13))),
% 0.58/0.79      inference('simplify', [status(thm)], ['97'])).
% 0.58/0.79  thf('99', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79          | ~ (l1_orders_2 @ sk_A)
% 0.58/0.79          | ~ (v5_orders_2 @ sk_A)
% 0.58/0.79          | ~ (v4_orders_2 @ sk_A)
% 0.58/0.79          | ~ (v3_orders_2 @ sk_A)
% 0.58/0.79          | (v2_struct_0 @ sk_A)
% 0.58/0.79          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.58/0.79          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79          | ~ (r2_orders_2 @ sk_A @ X0 @ 
% 0.58/0.79               (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['96', '98'])).
% 0.58/0.79  thf('100', plain, ((l1_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('101', plain, ((v5_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('102', plain, ((v4_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('103', plain, ((v3_orders_2 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('104', plain,
% 0.58/0.79      (![X0 : $i]:
% 0.58/0.79         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79          | (v2_struct_0 @ sk_A)
% 0.58/0.79          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.58/0.79          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79          | ~ (r2_orders_2 @ sk_A @ X0 @ 
% 0.58/0.79               (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A)))),
% 0.58/0.79      inference('demod', [status(thm)], ['99', '100', '101', '102', '103'])).
% 0.58/0.79  thf('105', plain,
% 0.58/0.79      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.58/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.58/0.79        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.58/0.79        | (v2_struct_0 @ sk_A)
% 0.58/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['95', '104'])).
% 0.58/0.79  thf('106', plain,
% 0.58/0.79      (((r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.58/0.79         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.58/0.79      inference('split', [status(esa)], ['43'])).
% 0.58/0.79  thf('107', plain,
% 0.58/0.79      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.58/0.79       ((r2_hidden @ sk_B @ 
% 0.58/0.79         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.58/0.79      inference('split', [status(esa)], ['43'])).
% 0.58/0.79  thf('108', plain, (((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.58/0.79      inference('sat_resolution*', [status(thm)], ['41', '89', '107'])).
% 0.58/0.79  thf('109', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C)),
% 0.58/0.79      inference('simpl_trail', [status(thm)], ['106', '108'])).
% 0.58/0.79  thf('110', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('111', plain,
% 0.58/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.58/0.79        | (v2_struct_0 @ sk_A)
% 0.58/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.79      inference('demod', [status(thm)], ['105', '109', '110'])).
% 0.58/0.79  thf('112', plain,
% 0.58/0.79      (((v2_struct_0 @ sk_A)
% 0.58/0.79        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.58/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.79      inference('simplify', [status(thm)], ['111'])).
% 0.58/0.79  thf('113', plain, (~ (v2_struct_0 @ sk_A)),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('114', plain,
% 0.58/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.58/0.79        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C))))),
% 0.58/0.79      inference('clc', [status(thm)], ['112', '113'])).
% 0.58/0.79  thf('115', plain,
% 0.58/0.79      ((~ (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.58/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.58/0.79      inference('simpl_trail', [status(thm)], ['40', '90'])).
% 0.58/0.79  thf('116', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.58/0.79      inference('clc', [status(thm)], ['114', '115'])).
% 0.58/0.79  thf('117', plain,
% 0.58/0.79      (![X7 : $i]:
% 0.58/0.79         (~ (v1_xboole_0 @ (u1_struct_0 @ X7))
% 0.58/0.79          | ~ (l1_struct_0 @ X7)
% 0.58/0.79          | (v2_struct_0 @ X7))),
% 0.58/0.79      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.58/0.79  thf('118', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.58/0.79      inference('sup-', [status(thm)], ['116', '117'])).
% 0.58/0.79  thf('119', plain, ((l1_struct_0 @ sk_A)),
% 0.58/0.79      inference('sup-', [status(thm)], ['84', '85'])).
% 0.58/0.79  thf('120', plain, ((v2_struct_0 @ sk_A)),
% 0.58/0.79      inference('demod', [status(thm)], ['118', '119'])).
% 0.58/0.79  thf('121', plain, ($false), inference('demod', [status(thm)], ['0', '120'])).
% 0.58/0.79  
% 0.58/0.79  % SZS output end Refutation
% 0.58/0.79  
% 0.58/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
