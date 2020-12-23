%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6VxasbvBji

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:58 EST 2020

% Result     : Theorem 0.77s
% Output     : Refutation 0.77s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 393 expanded)
%              Number of leaves         :   32 ( 125 expanded)
%              Depth                    :   25
%              Number of atoms          : 1857 (6768 expanded)
%              Number of equality atoms :   45 (  72 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

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

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X7 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

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

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_orders_2 @ X16 @ X15 )
        = ( a_2_1_orders_2 @ X16 @ X15 ) )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['8','9','10','11','12'])).

thf('14',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['16'])).

thf('18',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

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

thf('21',plain,(
    ! [X18: $i,X19: $i,X21: $i,X22: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r2_hidden @ X21 @ ( a_2_1_orders_2 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X18 ) )
      | ( X21 != X22 )
      | ( r2_hidden @ ( sk_E @ X22 @ X19 @ X18 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('22',plain,(
    ! [X18: $i,X19: $i,X22: $i] :
      ( ( r2_hidden @ ( sk_E @ X22 @ X19 @ X18 ) @ X19 )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ X22 @ ( a_2_1_orders_2 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v2_struct_0 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
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
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k1_tarski @ sk_C ) @ sk_A ) @ ( k1_tarski @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('30',plain,(
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

thf('31',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('32',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['18','35'])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
      = sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('39',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ X23 )
      | ( ( k6_domain_1 @ X23 @ X24 )
        = ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('40',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
        = sk_C )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['37','42'])).

thf('44',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
        = sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
        = sk_C ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('48',plain,(
    ! [X18: $i,X19: $i,X21: $i,X22: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( r2_hidden @ X21 @ ( a_2_1_orders_2 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X18 ) )
      | ( X21 != X22 )
      | ~ ( r2_orders_2 @ X18 @ X22 @ ( sk_E @ X22 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('49',plain,(
    ! [X18: $i,X19: $i,X22: $i] :
      ( ~ ( r2_orders_2 @ X18 @ X22 @ ( sk_E @ X22 @ X19 @ X18 ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X18 ) )
      | ( r2_hidden @ X22 @ ( a_2_1_orders_2 @ X18 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( v2_struct_0 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( l1_orders_2 @ X18 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
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
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_E @ X0 @ ( k1_tarski @ sk_C ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['50','51','52','53','54'])).

thf('56',plain,
    ( ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['46','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v2_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['17','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup+',[status(thm)],['15','62'])).

thf('64',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) ) )
   <= ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('66',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('67',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('68',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('70',plain,(
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('71',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      & ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['16'])).

thf('76',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('77',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['16'])).

thf('78',plain,
    ( ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('80',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('81',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( X21
        = ( sk_D_1 @ X19 @ X18 @ X21 ) )
      | ~ ( r2_hidden @ X21 @ ( a_2_1_orders_2 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('82',plain,(
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
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( X0
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['82','83','84','85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( X0
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['78','89'])).

thf('91',plain,
    ( ( ( sk_B
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('95',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('96',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['94','96'])).

thf('98',plain,
    ( ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['76','77'])).

thf('99',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('101',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ( r2_orders_2 @ X18 @ ( sk_D_1 @ X19 @ X18 @ X21 ) @ X20 )
      | ~ ( r2_hidden @ X20 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( a_2_1_orders_2 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('102',plain,(
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
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_C ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103','104','105','106'])).

thf('108',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_C ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['99','107'])).

thf('109',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_C ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) ) ) ),
    inference(simplify,[status(thm)],['108'])).

thf('110',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ X0 )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['98','109'])).

thf('111',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C ) )
        | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['97','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k1_tarski @ sk_C ) @ sk_A @ sk_B ) @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup+',[status(thm)],['93','116'])).

thf('118',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('120',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X14: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_struct_0 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('122',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['69','70'])).

thf('124',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['122','123'])).

thf('125',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','74','75','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6VxasbvBji
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:39:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.77/0.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.77/0.95  % Solved by: fo/fo7.sh
% 0.77/0.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.77/0.95  % done 783 iterations in 0.496s
% 0.77/0.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.77/0.95  % SZS output start Refutation
% 0.77/0.95  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.77/0.95  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.77/0.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.77/0.95  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.77/0.95  thf(sk_A_type, type, sk_A: $i).
% 0.77/0.95  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.77/0.95  thf(sk_C_type, type, sk_C: $i).
% 0.77/0.95  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.77/0.95  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.77/0.95  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.77/0.95  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.77/0.95  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.77/0.95  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.77/0.95  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.77/0.95  thf(sk_B_type, type, sk_B: $i).
% 0.77/0.95  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.77/0.95  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.77/0.95  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.77/0.95  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 0.77/0.95  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.77/0.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.77/0.95  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.77/0.95  thf(t52_orders_2, conjecture,
% 0.77/0.95    (![A:$i]:
% 0.77/0.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.77/0.95         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.77/0.95       ( ![B:$i]:
% 0.77/0.95         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.77/0.95           ( ![C:$i]:
% 0.77/0.95             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.77/0.95               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.77/0.95                 ( r2_hidden @
% 0.77/0.95                   B @ 
% 0.77/0.95                   ( k2_orders_2 @
% 0.77/0.95                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.77/0.95  thf(zf_stmt_0, negated_conjecture,
% 0.77/0.95    (~( ![A:$i]:
% 0.77/0.95        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.77/0.95            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.77/0.95          ( ![B:$i]:
% 0.77/0.95            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.77/0.95              ( ![C:$i]:
% 0.77/0.95                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.77/0.95                  ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.77/0.95                    ( r2_hidden @
% 0.77/0.95                      B @ 
% 0.77/0.95                      ( k2_orders_2 @
% 0.77/0.95                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.77/0.95    inference('cnf.neg', [status(esa)], [t52_orders_2])).
% 0.77/0.95  thf('0', plain,
% 0.77/0.95      ((~ (r2_hidden @ sk_B @ 
% 0.77/0.95           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.77/0.95        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('1', plain,
% 0.77/0.95      (~
% 0.77/0.95       ((r2_hidden @ sk_B @ 
% 0.77/0.95         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) | 
% 0.77/0.95       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.77/0.95      inference('split', [status(esa)], ['0'])).
% 0.77/0.95  thf('2', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf(t2_subset, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( m1_subset_1 @ A @ B ) =>
% 0.77/0.95       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.77/0.95  thf('3', plain,
% 0.77/0.95      (![X9 : $i, X10 : $i]:
% 0.77/0.95         ((r2_hidden @ X9 @ X10)
% 0.77/0.95          | (v1_xboole_0 @ X10)
% 0.77/0.95          | ~ (m1_subset_1 @ X9 @ X10))),
% 0.77/0.95      inference('cnf', [status(esa)], [t2_subset])).
% 0.77/0.95  thf('4', plain,
% 0.77/0.95      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95        | (r2_hidden @ sk_C @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['2', '3'])).
% 0.77/0.95  thf(t63_subset_1, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( r2_hidden @ A @ B ) =>
% 0.77/0.95       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.77/0.95  thf('5', plain,
% 0.77/0.95      (![X7 : $i, X8 : $i]:
% 0.77/0.95         ((m1_subset_1 @ (k1_tarski @ X7) @ (k1_zfmisc_1 @ X8))
% 0.77/0.95          | ~ (r2_hidden @ X7 @ X8))),
% 0.77/0.95      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.77/0.95  thf('6', plain,
% 0.77/0.95      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.77/0.95           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['4', '5'])).
% 0.77/0.95  thf(d13_orders_2, axiom,
% 0.77/0.95    (![A:$i]:
% 0.77/0.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.77/0.95         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.77/0.95       ( ![B:$i]:
% 0.77/0.95         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.77/0.95           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 0.77/0.95  thf('7', plain,
% 0.77/0.95      (![X15 : $i, X16 : $i]:
% 0.77/0.95         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.77/0.95          | ((k2_orders_2 @ X16 @ X15) = (a_2_1_orders_2 @ X16 @ X15))
% 0.77/0.95          | ~ (l1_orders_2 @ X16)
% 0.77/0.95          | ~ (v5_orders_2 @ X16)
% 0.77/0.95          | ~ (v4_orders_2 @ X16)
% 0.77/0.95          | ~ (v3_orders_2 @ X16)
% 0.77/0.95          | (v2_struct_0 @ X16))),
% 0.77/0.95      inference('cnf', [status(esa)], [d13_orders_2])).
% 0.77/0.95  thf('8', plain,
% 0.77/0.95      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95        | (v2_struct_0 @ sk_A)
% 0.77/0.95        | ~ (v3_orders_2 @ sk_A)
% 0.77/0.95        | ~ (v4_orders_2 @ sk_A)
% 0.77/0.95        | ~ (v5_orders_2 @ sk_A)
% 0.77/0.95        | ~ (l1_orders_2 @ sk_A)
% 0.77/0.95        | ((k2_orders_2 @ sk_A @ (k1_tarski @ sk_C))
% 0.77/0.95            = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['6', '7'])).
% 0.77/0.95  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('10', plain, ((v4_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('11', plain, ((v5_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('12', plain, ((l1_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('13', plain,
% 0.77/0.95      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95        | (v2_struct_0 @ sk_A)
% 0.77/0.95        | ((k2_orders_2 @ sk_A @ (k1_tarski @ sk_C))
% 0.77/0.95            = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C))))),
% 0.77/0.95      inference('demod', [status(thm)], ['8', '9', '10', '11', '12'])).
% 0.77/0.95  thf('14', plain, (~ (v2_struct_0 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('15', plain,
% 0.77/0.95      ((((k2_orders_2 @ sk_A @ (k1_tarski @ sk_C))
% 0.77/0.95          = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('clc', [status(thm)], ['13', '14'])).
% 0.77/0.95  thf('16', plain,
% 0.77/0.95      (((r2_hidden @ sk_B @ 
% 0.77/0.95         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.77/0.95        | (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('17', plain,
% 0.77/0.95      (((r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.77/0.95         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.77/0.95      inference('split', [status(esa)], ['16'])).
% 0.77/0.95  thf('18', plain,
% 0.77/0.95      ((((k2_orders_2 @ sk_A @ (k1_tarski @ sk_C))
% 0.77/0.95          = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('clc', [status(thm)], ['13', '14'])).
% 0.77/0.95  thf('19', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('20', plain,
% 0.77/0.95      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.77/0.95           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['4', '5'])).
% 0.77/0.95  thf(fraenkel_a_2_1_orders_2, axiom,
% 0.77/0.95    (![A:$i,B:$i,C:$i]:
% 0.77/0.95     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.77/0.95         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.77/0.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.77/0.95       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 0.77/0.95         ( ?[D:$i]:
% 0.77/0.95           ( ( ![E:$i]:
% 0.77/0.95               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.77/0.95                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 0.77/0.95             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.77/0.95  thf('21', plain,
% 0.77/0.95      (![X18 : $i, X19 : $i, X21 : $i, X22 : $i]:
% 0.77/0.95         (~ (l1_orders_2 @ X18)
% 0.77/0.95          | ~ (v5_orders_2 @ X18)
% 0.77/0.95          | ~ (v4_orders_2 @ X18)
% 0.77/0.95          | ~ (v3_orders_2 @ X18)
% 0.77/0.95          | (v2_struct_0 @ X18)
% 0.77/0.95          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.77/0.95          | (r2_hidden @ X21 @ (a_2_1_orders_2 @ X18 @ X19))
% 0.77/0.95          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X18))
% 0.77/0.95          | ((X21) != (X22))
% 0.77/0.95          | (r2_hidden @ (sk_E @ X22 @ X19 @ X18) @ X19))),
% 0.77/0.95      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.77/0.95  thf('22', plain,
% 0.77/0.95      (![X18 : $i, X19 : $i, X22 : $i]:
% 0.77/0.95         ((r2_hidden @ (sk_E @ X22 @ X19 @ X18) @ X19)
% 0.77/0.95          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X18))
% 0.77/0.95          | (r2_hidden @ X22 @ (a_2_1_orders_2 @ X18 @ X19))
% 0.77/0.95          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.77/0.95          | (v2_struct_0 @ X18)
% 0.77/0.95          | ~ (v3_orders_2 @ X18)
% 0.77/0.95          | ~ (v4_orders_2 @ X18)
% 0.77/0.95          | ~ (v5_orders_2 @ X18)
% 0.77/0.95          | ~ (l1_orders_2 @ X18))),
% 0.77/0.95      inference('simplify', [status(thm)], ['21'])).
% 0.77/0.95  thf('23', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | ~ (l1_orders_2 @ sk_A)
% 0.77/0.95          | ~ (v5_orders_2 @ sk_A)
% 0.77/0.95          | ~ (v4_orders_2 @ sk_A)
% 0.77/0.95          | ~ (v3_orders_2 @ sk_A)
% 0.77/0.95          | (v2_struct_0 @ sk_A)
% 0.77/0.95          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | (r2_hidden @ (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A) @ 
% 0.77/0.95             (k1_tarski @ sk_C)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['20', '22'])).
% 0.77/0.95  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('25', plain, ((v5_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('26', plain, ((v4_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('27', plain, ((v3_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('28', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | (v2_struct_0 @ sk_A)
% 0.77/0.95          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | (r2_hidden @ (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A) @ 
% 0.77/0.95             (k1_tarski @ sk_C)))),
% 0.77/0.95      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.77/0.95  thf('29', plain,
% 0.77/0.95      (((r2_hidden @ (sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) @ 
% 0.77/0.95         (k1_tarski @ sk_C))
% 0.77/0.95        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95        | (v2_struct_0 @ sk_A)
% 0.77/0.95        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['19', '28'])).
% 0.77/0.95  thf(t69_enumset1, axiom,
% 0.77/0.95    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.77/0.95  thf('30', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.77/0.95      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.77/0.95  thf(d2_tarski, axiom,
% 0.77/0.95    (![A:$i,B:$i,C:$i]:
% 0.77/0.95     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.77/0.95       ( ![D:$i]:
% 0.77/0.95         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.77/0.95  thf('31', plain,
% 0.77/0.95      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.77/0.95         (~ (r2_hidden @ X4 @ X2)
% 0.77/0.95          | ((X4) = (X3))
% 0.77/0.95          | ((X4) = (X0))
% 0.77/0.95          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.77/0.95      inference('cnf', [status(esa)], [d2_tarski])).
% 0.77/0.95  thf('32', plain,
% 0.77/0.95      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.77/0.95         (((X4) = (X0))
% 0.77/0.95          | ((X4) = (X3))
% 0.77/0.95          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.77/0.95      inference('simplify', [status(thm)], ['31'])).
% 0.77/0.95  thf('33', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['30', '32'])).
% 0.77/0.95  thf('34', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.77/0.95      inference('simplify', [status(thm)], ['33'])).
% 0.77/0.95  thf('35', plain,
% 0.77/0.95      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95        | (v2_struct_0 @ sk_A)
% 0.77/0.95        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95        | ((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['29', '34'])).
% 0.77/0.95  thf('36', plain,
% 0.77/0.95      (((r2_hidden @ sk_B @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95        | ((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C))
% 0.77/0.95        | (v2_struct_0 @ sk_A)
% 0.77/0.95        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('sup+', [status(thm)], ['18', '35'])).
% 0.77/0.95  thf('37', plain,
% 0.77/0.95      (((v2_struct_0 @ sk_A)
% 0.77/0.95        | ((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C))
% 0.77/0.95        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95        | (r2_hidden @ sk_B @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C))))),
% 0.77/0.95      inference('simplify', [status(thm)], ['36'])).
% 0.77/0.95  thf('38', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf(redefinition_k6_domain_1, axiom,
% 0.77/0.95    (![A:$i,B:$i]:
% 0.77/0.95     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.77/0.95       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.77/0.95  thf('39', plain,
% 0.77/0.95      (![X23 : $i, X24 : $i]:
% 0.77/0.95         ((v1_xboole_0 @ X23)
% 0.77/0.95          | ~ (m1_subset_1 @ X24 @ X23)
% 0.77/0.95          | ((k6_domain_1 @ X23 @ X24) = (k1_tarski @ X24)))),
% 0.77/0.95      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.77/0.95  thf('40', plain,
% 0.77/0.95      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.77/0.95        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['38', '39'])).
% 0.77/0.95  thf('41', plain,
% 0.77/0.95      ((~ (r2_hidden @ sk_B @ 
% 0.77/0.95           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.77/0.95         <= (~
% 0.77/0.95             ((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('split', [status(esa)], ['0'])).
% 0.77/0.95  thf('42', plain,
% 0.77/0.95      (((~ (r2_hidden @ sk_B @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.77/0.95         <= (~
% 0.77/0.95             ((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['40', '41'])).
% 0.77/0.95  thf('43', plain,
% 0.77/0.95      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95         | ((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C))
% 0.77/0.95         | (v2_struct_0 @ sk_A)
% 0.77/0.95         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.77/0.95         <= (~
% 0.77/0.95             ((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['37', '42'])).
% 0.77/0.95  thf('44', plain,
% 0.77/0.95      ((((v2_struct_0 @ sk_A)
% 0.77/0.95         | ((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C))
% 0.77/0.95         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.77/0.95         <= (~
% 0.77/0.95             ((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('simplify', [status(thm)], ['43'])).
% 0.77/0.95  thf('45', plain, (~ (v2_struct_0 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('46', plain,
% 0.77/0.95      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95         | ((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C))))
% 0.77/0.95         <= (~
% 0.77/0.95             ((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('clc', [status(thm)], ['44', '45'])).
% 0.77/0.95  thf('47', plain,
% 0.77/0.95      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.77/0.95           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['4', '5'])).
% 0.77/0.95  thf('48', plain,
% 0.77/0.95      (![X18 : $i, X19 : $i, X21 : $i, X22 : $i]:
% 0.77/0.95         (~ (l1_orders_2 @ X18)
% 0.77/0.95          | ~ (v5_orders_2 @ X18)
% 0.77/0.95          | ~ (v4_orders_2 @ X18)
% 0.77/0.95          | ~ (v3_orders_2 @ X18)
% 0.77/0.95          | (v2_struct_0 @ X18)
% 0.77/0.95          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.77/0.95          | (r2_hidden @ X21 @ (a_2_1_orders_2 @ X18 @ X19))
% 0.77/0.95          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X18))
% 0.77/0.95          | ((X21) != (X22))
% 0.77/0.95          | ~ (r2_orders_2 @ X18 @ X22 @ (sk_E @ X22 @ X19 @ X18)))),
% 0.77/0.95      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.77/0.95  thf('49', plain,
% 0.77/0.95      (![X18 : $i, X19 : $i, X22 : $i]:
% 0.77/0.95         (~ (r2_orders_2 @ X18 @ X22 @ (sk_E @ X22 @ X19 @ X18))
% 0.77/0.95          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X18))
% 0.77/0.95          | (r2_hidden @ X22 @ (a_2_1_orders_2 @ X18 @ X19))
% 0.77/0.95          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.77/0.95          | (v2_struct_0 @ X18)
% 0.77/0.95          | ~ (v3_orders_2 @ X18)
% 0.77/0.95          | ~ (v4_orders_2 @ X18)
% 0.77/0.95          | ~ (v5_orders_2 @ X18)
% 0.77/0.95          | ~ (l1_orders_2 @ X18))),
% 0.77/0.95      inference('simplify', [status(thm)], ['48'])).
% 0.77/0.95  thf('50', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | ~ (l1_orders_2 @ sk_A)
% 0.77/0.95          | ~ (v5_orders_2 @ sk_A)
% 0.77/0.95          | ~ (v4_orders_2 @ sk_A)
% 0.77/0.95          | ~ (v3_orders_2 @ sk_A)
% 0.77/0.95          | (v2_struct_0 @ sk_A)
% 0.77/0.95          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | ~ (r2_orders_2 @ sk_A @ X0 @ 
% 0.77/0.95               (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['47', '49'])).
% 0.77/0.95  thf('51', plain, ((l1_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('52', plain, ((v5_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('53', plain, ((v4_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('54', plain, ((v3_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('55', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | (v2_struct_0 @ sk_A)
% 0.77/0.95          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | ~ (r2_orders_2 @ sk_A @ X0 @ 
% 0.77/0.95               (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A)))),
% 0.77/0.95      inference('demod', [status(thm)], ['50', '51', '52', '53', '54'])).
% 0.77/0.95  thf('56', plain,
% 0.77/0.95      (((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.77/0.95         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.77/0.95         | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95         | (v2_struct_0 @ sk_A)
% 0.77/0.95         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.77/0.95         <= (~
% 0.77/0.95             ((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['46', '55'])).
% 0.77/0.95  thf('57', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('58', plain,
% 0.77/0.95      (((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.77/0.95         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95         | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95         | (v2_struct_0 @ sk_A)
% 0.77/0.95         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.77/0.95         <= (~
% 0.77/0.95             ((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('demod', [status(thm)], ['56', '57'])).
% 0.77/0.95  thf('59', plain,
% 0.77/0.95      ((((v2_struct_0 @ sk_A)
% 0.77/0.95         | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95         | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)))
% 0.77/0.95         <= (~
% 0.77/0.95             ((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('simplify', [status(thm)], ['58'])).
% 0.77/0.95  thf('60', plain,
% 0.77/0.95      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95         | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95         | (v2_struct_0 @ sk_A)))
% 0.77/0.95         <= (~
% 0.77/0.95             ((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) & 
% 0.77/0.95             ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['17', '59'])).
% 0.77/0.95  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('62', plain,
% 0.77/0.95      ((((r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.77/0.95         <= (~
% 0.77/0.95             ((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) & 
% 0.77/0.95             ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.77/0.95      inference('clc', [status(thm)], ['60', '61'])).
% 0.77/0.95  thf('63', plain,
% 0.77/0.95      ((((r2_hidden @ sk_B @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.77/0.95         <= (~
% 0.77/0.95             ((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) & 
% 0.77/0.95             ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.77/0.95      inference('sup+', [status(thm)], ['15', '62'])).
% 0.77/0.95  thf('64', plain,
% 0.77/0.95      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95         | (r2_hidden @ sk_B @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C)))))
% 0.77/0.95         <= (~
% 0.77/0.95             ((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) & 
% 0.77/0.95             ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.77/0.95      inference('simplify', [status(thm)], ['63'])).
% 0.77/0.95  thf('65', plain,
% 0.77/0.95      (((~ (r2_hidden @ sk_B @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.77/0.95         <= (~
% 0.77/0.95             ((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['40', '41'])).
% 0.77/0.95  thf('66', plain,
% 0.77/0.95      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.77/0.95         <= (~
% 0.77/0.95             ((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) & 
% 0.77/0.95             ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.77/0.95      inference('clc', [status(thm)], ['64', '65'])).
% 0.77/0.95  thf(fc2_struct_0, axiom,
% 0.77/0.95    (![A:$i]:
% 0.77/0.95     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.77/0.95       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.77/0.95  thf('67', plain,
% 0.77/0.95      (![X14 : $i]:
% 0.77/0.95         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 0.77/0.95          | ~ (l1_struct_0 @ X14)
% 0.77/0.95          | (v2_struct_0 @ X14))),
% 0.77/0.95      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.77/0.95  thf('68', plain,
% 0.77/0.95      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.77/0.95         <= (~
% 0.77/0.95             ((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) & 
% 0.77/0.95             ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['66', '67'])).
% 0.77/0.95  thf('69', plain, ((l1_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf(dt_l1_orders_2, axiom,
% 0.77/0.95    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.77/0.95  thf('70', plain,
% 0.77/0.95      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_orders_2 @ X17))),
% 0.77/0.95      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.77/0.95  thf('71', plain, ((l1_struct_0 @ sk_A)),
% 0.77/0.95      inference('sup-', [status(thm)], ['69', '70'])).
% 0.77/0.95  thf('72', plain,
% 0.77/0.95      (((v2_struct_0 @ sk_A))
% 0.77/0.95         <= (~
% 0.77/0.95             ((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) & 
% 0.77/0.95             ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.77/0.95      inference('demod', [status(thm)], ['68', '71'])).
% 0.77/0.95  thf('73', plain, (~ (v2_struct_0 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('74', plain,
% 0.77/0.95      (((r2_hidden @ sk_B @ 
% 0.77/0.95         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) | 
% 0.77/0.95       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.77/0.95      inference('sup-', [status(thm)], ['72', '73'])).
% 0.77/0.95  thf('75', plain,
% 0.77/0.95      (((r2_hidden @ sk_B @ 
% 0.77/0.95         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) | 
% 0.77/0.95       ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.77/0.95      inference('split', [status(esa)], ['16'])).
% 0.77/0.95  thf('76', plain,
% 0.77/0.95      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.77/0.95        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['38', '39'])).
% 0.77/0.95  thf('77', plain,
% 0.77/0.95      (((r2_hidden @ sk_B @ 
% 0.77/0.95         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.77/0.95         <= (((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('split', [status(esa)], ['16'])).
% 0.77/0.95  thf('78', plain,
% 0.77/0.95      ((((r2_hidden @ sk_B @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.77/0.95         <= (((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('sup+', [status(thm)], ['76', '77'])).
% 0.77/0.95  thf('79', plain,
% 0.77/0.95      ((((k2_orders_2 @ sk_A @ (k1_tarski @ sk_C))
% 0.77/0.95          = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('clc', [status(thm)], ['13', '14'])).
% 0.77/0.95  thf('80', plain,
% 0.77/0.95      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.77/0.95           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['4', '5'])).
% 0.77/0.95  thf('81', plain,
% 0.77/0.95      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.77/0.95         (~ (l1_orders_2 @ X18)
% 0.77/0.95          | ~ (v5_orders_2 @ X18)
% 0.77/0.95          | ~ (v4_orders_2 @ X18)
% 0.77/0.95          | ~ (v3_orders_2 @ X18)
% 0.77/0.95          | (v2_struct_0 @ X18)
% 0.77/0.95          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.77/0.95          | ((X21) = (sk_D_1 @ X19 @ X18 @ X21))
% 0.77/0.95          | ~ (r2_hidden @ X21 @ (a_2_1_orders_2 @ X18 @ X19)))),
% 0.77/0.95      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.77/0.95  thf('82', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95          | ((X0) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0))
% 0.77/0.95          | (v2_struct_0 @ sk_A)
% 0.77/0.95          | ~ (v3_orders_2 @ sk_A)
% 0.77/0.95          | ~ (v4_orders_2 @ sk_A)
% 0.77/0.95          | ~ (v5_orders_2 @ sk_A)
% 0.77/0.95          | ~ (l1_orders_2 @ sk_A))),
% 0.77/0.95      inference('sup-', [status(thm)], ['80', '81'])).
% 0.77/0.95  thf('83', plain, ((v3_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('84', plain, ((v4_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('85', plain, ((v5_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('86', plain, ((l1_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('87', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95          | ((X0) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0))
% 0.77/0.95          | (v2_struct_0 @ sk_A))),
% 0.77/0.95      inference('demod', [status(thm)], ['82', '83', '84', '85', '86'])).
% 0.77/0.95  thf('88', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         (~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | (v2_struct_0 @ sk_A)
% 0.77/0.95          | ((X0) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0))
% 0.77/0.95          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['79', '87'])).
% 0.77/0.95  thf('89', plain,
% 0.77/0.95      (![X0 : $i]:
% 0.77/0.95         (((X0) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0))
% 0.77/0.95          | (v2_struct_0 @ sk_A)
% 0.77/0.95          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | ~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C))))),
% 0.77/0.95      inference('simplify', [status(thm)], ['88'])).
% 0.77/0.95  thf('90', plain,
% 0.77/0.95      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95         | (v2_struct_0 @ sk_A)
% 0.77/0.95         | ((sk_B) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B))))
% 0.77/0.95         <= (((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['78', '89'])).
% 0.77/0.95  thf('91', plain,
% 0.77/0.95      (((((sk_B) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B))
% 0.77/0.95         | (v2_struct_0 @ sk_A)
% 0.77/0.95         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.77/0.95         <= (((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('simplify', [status(thm)], ['90'])).
% 0.77/0.95  thf('92', plain, (~ (v2_struct_0 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('93', plain,
% 0.77/0.95      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95         | ((sk_B) = (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B))))
% 0.77/0.95         <= (((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('clc', [status(thm)], ['91', '92'])).
% 0.77/0.95  thf('94', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.77/0.95      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.77/0.95  thf('95', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.77/0.95         (((X1) != (X0))
% 0.77/0.95          | (r2_hidden @ X1 @ X2)
% 0.77/0.95          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.77/0.95      inference('cnf', [status(esa)], [d2_tarski])).
% 0.77/0.95  thf('96', plain,
% 0.77/0.95      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.77/0.95      inference('simplify', [status(thm)], ['95'])).
% 0.77/0.95  thf('97', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.77/0.95      inference('sup+', [status(thm)], ['94', '96'])).
% 0.77/0.95  thf('98', plain,
% 0.77/0.95      ((((r2_hidden @ sk_B @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.77/0.95         <= (((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('sup+', [status(thm)], ['76', '77'])).
% 0.77/0.95  thf('99', plain,
% 0.77/0.95      ((((k2_orders_2 @ sk_A @ (k1_tarski @ sk_C))
% 0.77/0.95          = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('clc', [status(thm)], ['13', '14'])).
% 0.77/0.95  thf('100', plain,
% 0.77/0.95      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95        | (m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.77/0.95           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['4', '5'])).
% 0.77/0.95  thf('101', plain,
% 0.77/0.95      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.77/0.95         (~ (l1_orders_2 @ X18)
% 0.77/0.95          | ~ (v5_orders_2 @ X18)
% 0.77/0.95          | ~ (v4_orders_2 @ X18)
% 0.77/0.95          | ~ (v3_orders_2 @ X18)
% 0.77/0.95          | (v2_struct_0 @ X18)
% 0.77/0.95          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.77/0.95          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.77/0.95          | (r2_orders_2 @ X18 @ (sk_D_1 @ X19 @ X18 @ X21) @ X20)
% 0.77/0.95          | ~ (r2_hidden @ X20 @ X19)
% 0.77/0.95          | ~ (r2_hidden @ X21 @ (a_2_1_orders_2 @ X18 @ X19)))),
% 0.77/0.95      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.77/0.95  thf('102', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_C))
% 0.77/0.95          | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0) @ 
% 0.77/0.95             X1)
% 0.77/0.95          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | (v2_struct_0 @ sk_A)
% 0.77/0.95          | ~ (v3_orders_2 @ sk_A)
% 0.77/0.95          | ~ (v4_orders_2 @ sk_A)
% 0.77/0.95          | ~ (v5_orders_2 @ sk_A)
% 0.77/0.95          | ~ (l1_orders_2 @ sk_A))),
% 0.77/0.95      inference('sup-', [status(thm)], ['100', '101'])).
% 0.77/0.95  thf('103', plain, ((v3_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('104', plain, ((v4_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('105', plain, ((v5_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('106', plain, ((l1_orders_2 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('107', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_C))
% 0.77/0.95          | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0) @ 
% 0.77/0.95             X1)
% 0.77/0.95          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | (v2_struct_0 @ sk_A))),
% 0.77/0.95      inference('demod', [status(thm)], ['102', '103', '104', '105', '106'])).
% 0.77/0.95  thf('108', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         (~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.77/0.95          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | (v2_struct_0 @ sk_A)
% 0.77/0.95          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0) @ 
% 0.77/0.95             X1)
% 0.77/0.95          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_C))
% 0.77/0.95          | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.77/0.95      inference('sup-', [status(thm)], ['99', '107'])).
% 0.77/0.95  thf('109', plain,
% 0.77/0.95      (![X0 : $i, X1 : $i]:
% 0.77/0.95         (~ (r2_hidden @ X1 @ (k1_tarski @ sk_C))
% 0.77/0.95          | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ X0) @ 
% 0.77/0.95             X1)
% 0.77/0.95          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | (v2_struct_0 @ sk_A)
% 0.77/0.95          | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95          | ~ (r2_hidden @ X0 @ (k2_orders_2 @ sk_A @ (k1_tarski @ sk_C))))),
% 0.77/0.95      inference('simplify', [status(thm)], ['108'])).
% 0.77/0.95  thf('110', plain,
% 0.77/0.95      ((![X0 : $i]:
% 0.77/0.95          ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95           | (v2_struct_0 @ sk_A)
% 0.77/0.95           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95           | (r2_orders_2 @ sk_A @ 
% 0.77/0.95              (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ X0)
% 0.77/0.95           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_C))))
% 0.77/0.95         <= (((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['98', '109'])).
% 0.77/0.95  thf('111', plain,
% 0.77/0.95      ((![X0 : $i]:
% 0.77/0.95          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_C))
% 0.77/0.95           | (r2_orders_2 @ sk_A @ 
% 0.77/0.95              (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ X0)
% 0.77/0.95           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95           | (v2_struct_0 @ sk_A)
% 0.77/0.95           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.77/0.95         <= (((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('simplify', [status(thm)], ['110'])).
% 0.77/0.95  thf('112', plain,
% 0.77/0.95      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95         | (v2_struct_0 @ sk_A)
% 0.77/0.95         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.77/0.95         | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ 
% 0.77/0.95            sk_C)))
% 0.77/0.95         <= (((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['97', '111'])).
% 0.77/0.95  thf('113', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('114', plain,
% 0.77/0.95      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95         | (v2_struct_0 @ sk_A)
% 0.77/0.95         | (r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ 
% 0.77/0.95            sk_C)))
% 0.77/0.95         <= (((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('demod', [status(thm)], ['112', '113'])).
% 0.77/0.95  thf('115', plain, (~ (v2_struct_0 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('116', plain,
% 0.77/0.95      ((((r2_orders_2 @ sk_A @ (sk_D_1 @ (k1_tarski @ sk_C) @ sk_A @ sk_B) @ 
% 0.77/0.95          sk_C)
% 0.77/0.95         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.77/0.95         <= (((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('clc', [status(thm)], ['114', '115'])).
% 0.77/0.95  thf('117', plain,
% 0.77/0.95      ((((r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.77/0.95         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.77/0.95         <= (((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('sup+', [status(thm)], ['93', '116'])).
% 0.77/0.95  thf('118', plain,
% 0.77/0.95      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.77/0.95         | (r2_orders_2 @ sk_A @ sk_B @ sk_C)))
% 0.77/0.95         <= (((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('simplify', [status(thm)], ['117'])).
% 0.77/0.95  thf('119', plain,
% 0.77/0.95      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.77/0.95         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.77/0.95      inference('split', [status(esa)], ['0'])).
% 0.77/0.95  thf('120', plain,
% 0.77/0.95      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.77/0.95         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.77/0.95             ((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['118', '119'])).
% 0.77/0.95  thf('121', plain,
% 0.77/0.95      (![X14 : $i]:
% 0.77/0.95         (~ (v1_xboole_0 @ (u1_struct_0 @ X14))
% 0.77/0.95          | ~ (l1_struct_0 @ X14)
% 0.77/0.95          | (v2_struct_0 @ X14))),
% 0.77/0.95      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.77/0.95  thf('122', plain,
% 0.77/0.95      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.77/0.95         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.77/0.95             ((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('sup-', [status(thm)], ['120', '121'])).
% 0.77/0.95  thf('123', plain, ((l1_struct_0 @ sk_A)),
% 0.77/0.95      inference('sup-', [status(thm)], ['69', '70'])).
% 0.77/0.95  thf('124', plain,
% 0.77/0.95      (((v2_struct_0 @ sk_A))
% 0.77/0.95         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.77/0.95             ((r2_hidden @ sk_B @ 
% 0.77/0.95               (k2_orders_2 @ sk_A @ 
% 0.77/0.95                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.77/0.95      inference('demod', [status(thm)], ['122', '123'])).
% 0.77/0.95  thf('125', plain, (~ (v2_struct_0 @ sk_A)),
% 0.77/0.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.77/0.95  thf('126', plain,
% 0.77/0.95      (~
% 0.77/0.95       ((r2_hidden @ sk_B @ 
% 0.77/0.95         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) | 
% 0.77/0.95       ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.77/0.95      inference('sup-', [status(thm)], ['124', '125'])).
% 0.77/0.95  thf('127', plain, ($false),
% 0.77/0.95      inference('sat_resolution*', [status(thm)], ['1', '74', '75', '126'])).
% 0.77/0.95  
% 0.77/0.95  % SZS output end Refutation
% 0.77/0.95  
% 0.77/0.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
