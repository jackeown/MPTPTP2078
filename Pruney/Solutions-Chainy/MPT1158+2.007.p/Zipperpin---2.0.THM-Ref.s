%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3tRsL90V4h

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:58 EST 2020

% Result     : Theorem 0.65s
% Output     : Refutation 0.65s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 860 expanded)
%              Number of leaves         :   32 ( 258 expanded)
%              Depth                    :   33
%              Number of atoms          : 1546 (16047 expanded)
%              Number of equality atoms :   41 ( 126 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v6_orders_2_type,type,(
    v6_orders_2: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( ( k6_domain_1 @ X16 @ X17 )
        = ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A )
            & ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X19 ) @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t35_orders_2])).

thf('7',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','12'])).

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

thf('14',plain,(
    ! [X11: $i,X12: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r2_hidden @ X14 @ ( a_2_1_orders_2 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X11 ) )
      | ( X14 != X15 )
      | ( r2_hidden @ ( sk_E @ X15 @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('15',plain,(
    ! [X11: $i,X12: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_E @ X15 @ X12 @ X11 ) @ X12 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X11 ) )
      | ( r2_hidden @ X15 @ ( a_2_1_orders_2 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v2_struct_0 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
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
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k1_tarski @ sk_C ) @ sk_A ) @ ( k1_tarski @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20'])).

thf('22',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A ) @ ( k1_tarski @ sk_C ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','21'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('23',plain,(
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

thf('24',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('25',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('30',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

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

thf('31',plain,(
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

thf('32',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['32','33','34','35','36'])).

thf('38',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['29','39'])).

thf('41',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['41'])).

thf('45',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('47',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['45','47'])).

thf('49',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('50',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['50'])).

thf('52',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('53',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( r2_orders_2 @ X11 @ ( sk_D_1 @ X12 @ X11 @ X14 ) @ X13 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( a_2_1_orders_2 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      | ~ ( r2_hidden @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('56',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      | ~ ( r2_hidden @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55','56','57','58','59'])).

thf('61',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A @ sk_B ) @ X0 )
        | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['51','60'])).

thf('62',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['50'])).

thf('63',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('64',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( X14
        = ( sk_D_1 @ X12 @ X11 @ X14 ) )
      | ~ ( r2_hidden @ X14 @ ( a_2_1_orders_2 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      | ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) )
    = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('67',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
      | ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69','70'])).

thf('72',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference(clc,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_B
      = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['62','73'])).

thf('75',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
        | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['61','74'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ sk_B @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['49','75'])).

thf('77',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['48','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['79','80'])).

thf('82',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['41'])).

thf('83',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('84',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('85',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('87',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('88',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ) ),
    inference(demod,[status(thm)],['85','88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference('sat_resolution*',[status(thm)],['44','91'])).

thf('93',plain,
    ( ~ ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['43','92'])).

thf('94',plain,
    ( ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
      = sk_C )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['28','93'])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
      = sk_C ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C ) @ sk_A )
      = sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','12'])).

thf('99',plain,(
    ! [X11: $i,X12: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r2_hidden @ X14 @ ( a_2_1_orders_2 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X11 ) )
      | ( X14 != X15 )
      | ~ ( r2_orders_2 @ X11 @ X15 @ ( sk_E @ X15 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('100',plain,(
    ! [X11: $i,X12: $i,X15: $i] :
      ( ~ ( r2_orders_2 @ X11 @ X15 @ ( sk_E @ X15 @ X12 @ X11 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X11 ) )
      | ( r2_hidden @ X15 @ ( a_2_1_orders_2 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v2_struct_0 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
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
    inference('sup-',[status(thm)],['98','100'])).

thf('102',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_E @ X0 @ ( k1_tarski @ sk_C ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['101','102','103','104','105'])).

thf('107',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['97','106'])).

thf('108',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['50'])).

thf('109',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C ) ) ) ),
    inference(split,[status(esa)],['50'])).

thf('110',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['44','91','109'])).

thf('111',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['108','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['107','111','112'])).

thf('114',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,
    ( ~ ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['43','92'])).

thf('118',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('120',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['86','87'])).

thf('122',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['120','121'])).

thf('123',plain,(
    $false ),
    inference(demod,[status(thm)],['0','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3tRsL90V4h
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:33:53 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.65/0.86  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.65/0.86  % Solved by: fo/fo7.sh
% 0.65/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.65/0.86  % done 572 iterations in 0.392s
% 0.65/0.86  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.65/0.86  % SZS output start Refutation
% 0.65/0.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.65/0.86  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.65/0.86  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.65/0.86  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.65/0.86  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.65/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.65/0.86  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.65/0.86  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.65/0.86  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.65/0.86  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.65/0.86  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.65/0.86  thf(sk_C_type, type, sk_C: $i).
% 0.65/0.86  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.65/0.86  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.65/0.86  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.65/0.86  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.65/0.86  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 0.65/0.86  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.65/0.86  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.65/0.86  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.65/0.86  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.65/0.86  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.65/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.65/0.86  thf(t52_orders_2, conjecture,
% 0.65/0.86    (![A:$i]:
% 0.65/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.65/0.86         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.65/0.86       ( ![B:$i]:
% 0.65/0.86         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.65/0.86           ( ![C:$i]:
% 0.65/0.86             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.65/0.86               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.65/0.86                 ( r2_hidden @
% 0.65/0.86                   B @ 
% 0.65/0.86                   ( k2_orders_2 @
% 0.65/0.86                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.65/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.65/0.86    (~( ![A:$i]:
% 0.65/0.86        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.65/0.86            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.65/0.86          ( ![B:$i]:
% 0.65/0.86            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.65/0.86              ( ![C:$i]:
% 0.65/0.86                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.65/0.86                  ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.65/0.86                    ( r2_hidden @
% 0.65/0.86                      B @ 
% 0.65/0.86                      ( k2_orders_2 @
% 0.65/0.86                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.65/0.86    inference('cnf.neg', [status(esa)], [t52_orders_2])).
% 0.65/0.86  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('2', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf(redefinition_k6_domain_1, axiom,
% 0.65/0.86    (![A:$i,B:$i]:
% 0.65/0.86     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.65/0.86       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.65/0.86  thf('3', plain,
% 0.65/0.86      (![X16 : $i, X17 : $i]:
% 0.65/0.86         ((v1_xboole_0 @ X16)
% 0.65/0.86          | ~ (m1_subset_1 @ X17 @ X16)
% 0.65/0.86          | ((k6_domain_1 @ X16 @ X17) = (k1_tarski @ X17)))),
% 0.65/0.86      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.65/0.86  thf('4', plain,
% 0.65/0.86      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['2', '3'])).
% 0.65/0.86  thf('5', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf(t35_orders_2, axiom,
% 0.65/0.86    (![A:$i]:
% 0.65/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.65/0.86       ( ![B:$i]:
% 0.65/0.86         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.65/0.86           ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 0.65/0.86             ( m1_subset_1 @
% 0.65/0.86               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.65/0.86               ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.65/0.86  thf('6', plain,
% 0.65/0.86      (![X18 : $i, X19 : $i]:
% 0.65/0.86         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.65/0.86          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X19) @ X18) @ 
% 0.65/0.86             (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.65/0.86          | ~ (l1_orders_2 @ X19)
% 0.65/0.86          | ~ (v3_orders_2 @ X19)
% 0.65/0.86          | (v2_struct_0 @ X19))),
% 0.65/0.86      inference('cnf', [status(esa)], [t35_orders_2])).
% 0.65/0.86  thf('7', plain,
% 0.65/0.86      (((v2_struct_0 @ sk_A)
% 0.65/0.86        | ~ (v3_orders_2 @ sk_A)
% 0.65/0.86        | ~ (l1_orders_2 @ sk_A)
% 0.65/0.86        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.65/0.86           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['5', '6'])).
% 0.65/0.86  thf('8', plain, ((v3_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('9', plain, ((l1_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('10', plain,
% 0.65/0.86      (((v2_struct_0 @ sk_A)
% 0.65/0.86        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.65/0.86           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.65/0.86      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.65/0.86  thf('11', plain, (~ (v2_struct_0 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('12', plain,
% 0.65/0.86      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.65/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('clc', [status(thm)], ['10', '11'])).
% 0.65/0.86  thf('13', plain,
% 0.65/0.86      (((m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.65/0.86         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['4', '12'])).
% 0.65/0.86  thf(fraenkel_a_2_1_orders_2, axiom,
% 0.65/0.86    (![A:$i,B:$i,C:$i]:
% 0.65/0.86     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.65/0.86         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.65/0.86         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.65/0.86       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 0.65/0.86         ( ?[D:$i]:
% 0.65/0.86           ( ( ![E:$i]:
% 0.65/0.86               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.65/0.86                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 0.65/0.86             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.65/0.86  thf('14', plain,
% 0.65/0.86      (![X11 : $i, X12 : $i, X14 : $i, X15 : $i]:
% 0.65/0.86         (~ (l1_orders_2 @ X11)
% 0.65/0.86          | ~ (v5_orders_2 @ X11)
% 0.65/0.86          | ~ (v4_orders_2 @ X11)
% 0.65/0.86          | ~ (v3_orders_2 @ X11)
% 0.65/0.86          | (v2_struct_0 @ X11)
% 0.65/0.86          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.65/0.86          | (r2_hidden @ X14 @ (a_2_1_orders_2 @ X11 @ X12))
% 0.65/0.86          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X11))
% 0.65/0.86          | ((X14) != (X15))
% 0.65/0.86          | (r2_hidden @ (sk_E @ X15 @ X12 @ X11) @ X12))),
% 0.65/0.86      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.65/0.86  thf('15', plain,
% 0.65/0.86      (![X11 : $i, X12 : $i, X15 : $i]:
% 0.65/0.86         ((r2_hidden @ (sk_E @ X15 @ X12 @ X11) @ X12)
% 0.65/0.86          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X11))
% 0.65/0.86          | (r2_hidden @ X15 @ (a_2_1_orders_2 @ X11 @ X12))
% 0.65/0.86          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.65/0.86          | (v2_struct_0 @ X11)
% 0.65/0.86          | ~ (v3_orders_2 @ X11)
% 0.65/0.86          | ~ (v4_orders_2 @ X11)
% 0.65/0.86          | ~ (v5_orders_2 @ X11)
% 0.65/0.86          | ~ (l1_orders_2 @ X11))),
% 0.65/0.86      inference('simplify', [status(thm)], ['14'])).
% 0.65/0.86  thf('16', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | ~ (l1_orders_2 @ sk_A)
% 0.65/0.86          | ~ (v5_orders_2 @ sk_A)
% 0.65/0.86          | ~ (v4_orders_2 @ sk_A)
% 0.65/0.86          | ~ (v3_orders_2 @ sk_A)
% 0.65/0.86          | (v2_struct_0 @ sk_A)
% 0.65/0.86          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.65/0.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | (r2_hidden @ (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A) @ 
% 0.65/0.86             (k1_tarski @ sk_C)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['13', '15'])).
% 0.65/0.86  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('18', plain, ((v5_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('19', plain, ((v4_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('20', plain, ((v3_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('21', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | (v2_struct_0 @ sk_A)
% 0.65/0.86          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.65/0.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | (r2_hidden @ (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A) @ 
% 0.65/0.86             (k1_tarski @ sk_C)))),
% 0.65/0.86      inference('demod', [status(thm)], ['16', '17', '18', '19', '20'])).
% 0.65/0.86  thf('22', plain,
% 0.65/0.86      (((r2_hidden @ (sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) @ 
% 0.65/0.86         (k1_tarski @ sk_C))
% 0.65/0.86        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.65/0.86        | (v2_struct_0 @ sk_A)
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['1', '21'])).
% 0.65/0.86  thf(t69_enumset1, axiom,
% 0.65/0.86    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.65/0.86  thf('23', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.65/0.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.65/0.86  thf(d2_tarski, axiom,
% 0.65/0.86    (![A:$i,B:$i,C:$i]:
% 0.65/0.86     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.65/0.86       ( ![D:$i]:
% 0.65/0.86         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.65/0.86  thf('24', plain,
% 0.65/0.86      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.65/0.86         (~ (r2_hidden @ X4 @ X2)
% 0.65/0.86          | ((X4) = (X3))
% 0.65/0.86          | ((X4) = (X0))
% 0.65/0.86          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.65/0.86      inference('cnf', [status(esa)], [d2_tarski])).
% 0.65/0.86  thf('25', plain,
% 0.65/0.86      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.65/0.86         (((X4) = (X0))
% 0.65/0.86          | ((X4) = (X3))
% 0.65/0.86          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.65/0.86      inference('simplify', [status(thm)], ['24'])).
% 0.65/0.86  thf('26', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['23', '25'])).
% 0.65/0.86  thf('27', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.65/0.86      inference('simplify', [status(thm)], ['26'])).
% 0.65/0.86  thf('28', plain,
% 0.65/0.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86        | (v2_struct_0 @ sk_A)
% 0.65/0.86        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.65/0.86        | ((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['22', '27'])).
% 0.65/0.86  thf('29', plain,
% 0.65/0.86      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['2', '3'])).
% 0.65/0.86  thf('30', plain,
% 0.65/0.86      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.65/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('clc', [status(thm)], ['10', '11'])).
% 0.65/0.86  thf(d13_orders_2, axiom,
% 0.65/0.86    (![A:$i]:
% 0.65/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.65/0.86         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.65/0.86       ( ![B:$i]:
% 0.65/0.86         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.65/0.86           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 0.65/0.86  thf('31', plain,
% 0.65/0.86      (![X8 : $i, X9 : $i]:
% 0.65/0.86         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.65/0.86          | ((k2_orders_2 @ X9 @ X8) = (a_2_1_orders_2 @ X9 @ X8))
% 0.65/0.86          | ~ (l1_orders_2 @ X9)
% 0.65/0.86          | ~ (v5_orders_2 @ X9)
% 0.65/0.86          | ~ (v4_orders_2 @ X9)
% 0.65/0.86          | ~ (v3_orders_2 @ X9)
% 0.65/0.86          | (v2_struct_0 @ X9))),
% 0.65/0.86      inference('cnf', [status(esa)], [d13_orders_2])).
% 0.65/0.86  thf('32', plain,
% 0.65/0.86      (((v2_struct_0 @ sk_A)
% 0.65/0.86        | ~ (v3_orders_2 @ sk_A)
% 0.65/0.86        | ~ (v4_orders_2 @ sk_A)
% 0.65/0.86        | ~ (v5_orders_2 @ sk_A)
% 0.65/0.86        | ~ (l1_orders_2 @ sk_A)
% 0.65/0.86        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.65/0.86            = (a_2_1_orders_2 @ sk_A @ 
% 0.65/0.86               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['30', '31'])).
% 0.65/0.86  thf('33', plain, ((v3_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('34', plain, ((v4_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('35', plain, ((v5_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('36', plain, ((l1_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('37', plain,
% 0.65/0.86      (((v2_struct_0 @ sk_A)
% 0.65/0.86        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.65/0.86            = (a_2_1_orders_2 @ sk_A @ 
% 0.65/0.86               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.65/0.86      inference('demod', [status(thm)], ['32', '33', '34', '35', '36'])).
% 0.65/0.86  thf('38', plain, (~ (v2_struct_0 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('39', plain,
% 0.65/0.86      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.65/0.86         = (a_2_1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.65/0.86      inference('clc', [status(thm)], ['37', '38'])).
% 0.65/0.86  thf('40', plain,
% 0.65/0.86      ((((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.65/0.86          = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['29', '39'])).
% 0.65/0.86  thf('41', plain,
% 0.65/0.86      ((~ (r2_hidden @ sk_B @ 
% 0.65/0.86           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.65/0.86        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('42', plain,
% 0.65/0.86      ((~ (r2_hidden @ sk_B @ 
% 0.65/0.86           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.65/0.86         <= (~
% 0.65/0.86             ((r2_hidden @ sk_B @ 
% 0.65/0.86               (k2_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.65/0.86      inference('split', [status(esa)], ['41'])).
% 0.65/0.86  thf('43', plain,
% 0.65/0.86      (((~ (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.65/0.86         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.65/0.86         <= (~
% 0.65/0.86             ((r2_hidden @ sk_B @ 
% 0.65/0.86               (k2_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['40', '42'])).
% 0.65/0.86  thf('44', plain,
% 0.65/0.86      (~
% 0.65/0.86       ((r2_hidden @ sk_B @ 
% 0.65/0.86         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))) | 
% 0.65/0.86       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.65/0.86      inference('split', [status(esa)], ['41'])).
% 0.65/0.86  thf('45', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.65/0.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.65/0.86  thf('46', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.65/0.86         (((X1) != (X0))
% 0.65/0.86          | (r2_hidden @ X1 @ X2)
% 0.65/0.86          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.65/0.86      inference('cnf', [status(esa)], [d2_tarski])).
% 0.65/0.86  thf('47', plain,
% 0.65/0.86      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.65/0.86      inference('simplify', [status(thm)], ['46'])).
% 0.65/0.86  thf('48', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.65/0.86      inference('sup+', [status(thm)], ['45', '47'])).
% 0.65/0.86  thf('49', plain,
% 0.65/0.86      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) = (k1_tarski @ sk_C))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['2', '3'])).
% 0.65/0.86  thf('50', plain,
% 0.65/0.86      (((r2_hidden @ sk_B @ 
% 0.65/0.86         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.65/0.86        | (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('51', plain,
% 0.65/0.86      (((r2_hidden @ sk_B @ 
% 0.65/0.86         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.65/0.86         <= (((r2_hidden @ sk_B @ 
% 0.65/0.86               (k2_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.65/0.86      inference('split', [status(esa)], ['50'])).
% 0.65/0.86  thf('52', plain,
% 0.65/0.86      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.65/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('clc', [status(thm)], ['10', '11'])).
% 0.65/0.86  thf('53', plain,
% 0.65/0.86      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.65/0.86         (~ (l1_orders_2 @ X11)
% 0.65/0.86          | ~ (v5_orders_2 @ X11)
% 0.65/0.86          | ~ (v4_orders_2 @ X11)
% 0.65/0.86          | ~ (v3_orders_2 @ X11)
% 0.65/0.86          | (v2_struct_0 @ X11)
% 0.65/0.86          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.65/0.86          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.65/0.86          | (r2_orders_2 @ X11 @ (sk_D_1 @ X12 @ X11 @ X14) @ X13)
% 0.65/0.86          | ~ (r2_hidden @ X13 @ X12)
% 0.65/0.86          | ~ (r2_hidden @ X14 @ (a_2_1_orders_2 @ X11 @ X12)))),
% 0.65/0.86      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.65/0.86  thf('54', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         (~ (r2_hidden @ X0 @ 
% 0.65/0.86             (a_2_1_orders_2 @ sk_A @ 
% 0.65/0.86              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.65/0.86          | ~ (r2_hidden @ X1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.65/0.86          | (r2_orders_2 @ sk_A @ 
% 0.65/0.86             (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A @ X0) @ 
% 0.65/0.86             X1)
% 0.65/0.86          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | (v2_struct_0 @ sk_A)
% 0.65/0.86          | ~ (v3_orders_2 @ sk_A)
% 0.65/0.86          | ~ (v4_orders_2 @ sk_A)
% 0.65/0.86          | ~ (v5_orders_2 @ sk_A)
% 0.65/0.86          | ~ (l1_orders_2 @ sk_A))),
% 0.65/0.86      inference('sup-', [status(thm)], ['52', '53'])).
% 0.65/0.86  thf('55', plain,
% 0.65/0.86      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.65/0.86         = (a_2_1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.65/0.86      inference('clc', [status(thm)], ['37', '38'])).
% 0.65/0.86  thf('56', plain, ((v3_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('57', plain, ((v4_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('58', plain, ((v5_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('59', plain, ((l1_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('60', plain,
% 0.65/0.86      (![X0 : $i, X1 : $i]:
% 0.65/0.86         (~ (r2_hidden @ X0 @ 
% 0.65/0.86             (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.65/0.86          | ~ (r2_hidden @ X1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.65/0.86          | (r2_orders_2 @ sk_A @ 
% 0.65/0.86             (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A @ X0) @ 
% 0.65/0.86             X1)
% 0.65/0.86          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | (v2_struct_0 @ sk_A))),
% 0.65/0.86      inference('demod', [status(thm)], ['54', '55', '56', '57', '58', '59'])).
% 0.65/0.86  thf('61', plain,
% 0.65/0.86      ((![X0 : $i]:
% 0.65/0.86          ((v2_struct_0 @ sk_A)
% 0.65/0.86           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86           | (r2_orders_2 @ sk_A @ 
% 0.65/0.86              (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A @ 
% 0.65/0.86               sk_B) @ 
% 0.65/0.86              X0)
% 0.65/0.86           | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.65/0.86         <= (((r2_hidden @ sk_B @ 
% 0.65/0.86               (k2_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['51', '60'])).
% 0.65/0.86  thf('62', plain,
% 0.65/0.86      (((r2_hidden @ sk_B @ 
% 0.65/0.86         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.65/0.86         <= (((r2_hidden @ sk_B @ 
% 0.65/0.86               (k2_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.65/0.86      inference('split', [status(esa)], ['50'])).
% 0.65/0.86  thf('63', plain,
% 0.65/0.86      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ 
% 0.65/0.86        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('clc', [status(thm)], ['10', '11'])).
% 0.65/0.86  thf('64', plain,
% 0.65/0.86      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.65/0.86         (~ (l1_orders_2 @ X11)
% 0.65/0.86          | ~ (v5_orders_2 @ X11)
% 0.65/0.86          | ~ (v4_orders_2 @ X11)
% 0.65/0.86          | ~ (v3_orders_2 @ X11)
% 0.65/0.86          | (v2_struct_0 @ X11)
% 0.65/0.86          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.65/0.86          | ((X14) = (sk_D_1 @ X12 @ X11 @ X14))
% 0.65/0.86          | ~ (r2_hidden @ X14 @ (a_2_1_orders_2 @ X11 @ X12)))),
% 0.65/0.86      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.65/0.86  thf('65', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         (~ (r2_hidden @ X0 @ 
% 0.65/0.86             (a_2_1_orders_2 @ sk_A @ 
% 0.65/0.86              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.65/0.86          | ((X0)
% 0.65/0.86              = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A @ 
% 0.65/0.86                 X0))
% 0.65/0.86          | (v2_struct_0 @ sk_A)
% 0.65/0.86          | ~ (v3_orders_2 @ sk_A)
% 0.65/0.86          | ~ (v4_orders_2 @ sk_A)
% 0.65/0.86          | ~ (v5_orders_2 @ sk_A)
% 0.65/0.86          | ~ (l1_orders_2 @ sk_A))),
% 0.65/0.86      inference('sup-', [status(thm)], ['63', '64'])).
% 0.65/0.86  thf('66', plain,
% 0.65/0.86      (((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))
% 0.65/0.86         = (a_2_1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))),
% 0.65/0.86      inference('clc', [status(thm)], ['37', '38'])).
% 0.65/0.86  thf('67', plain, ((v3_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('68', plain, ((v4_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('69', plain, ((v5_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('70', plain, ((l1_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('71', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         (~ (r2_hidden @ X0 @ 
% 0.65/0.86             (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))
% 0.65/0.86          | ((X0)
% 0.65/0.86              = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A @ 
% 0.65/0.86                 X0))
% 0.65/0.86          | (v2_struct_0 @ sk_A))),
% 0.65/0.86      inference('demod', [status(thm)], ['65', '66', '67', '68', '69', '70'])).
% 0.65/0.86  thf('72', plain, (~ (v2_struct_0 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('73', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         (((X0)
% 0.65/0.86            = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A @ X0))
% 0.65/0.86          | ~ (r2_hidden @ X0 @ 
% 0.65/0.86               (k2_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.65/0.86      inference('clc', [status(thm)], ['71', '72'])).
% 0.65/0.86  thf('74', plain,
% 0.65/0.86      ((((sk_B)
% 0.65/0.86          = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C) @ sk_A @ sk_B)))
% 0.65/0.86         <= (((r2_hidden @ sk_B @ 
% 0.65/0.86               (k2_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['62', '73'])).
% 0.65/0.86  thf('75', plain,
% 0.65/0.86      ((![X0 : $i]:
% 0.65/0.86          ((v2_struct_0 @ sk_A)
% 0.65/0.86           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86           | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.65/0.86           | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))
% 0.65/0.86         <= (((r2_hidden @ sk_B @ 
% 0.65/0.86               (k2_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.65/0.86      inference('demod', [status(thm)], ['61', '74'])).
% 0.65/0.86  thf('76', plain,
% 0.65/0.86      ((![X0 : $i]:
% 0.65/0.86          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_C))
% 0.65/0.86           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86           | (r2_orders_2 @ sk_A @ sk_B @ X0)
% 0.65/0.86           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86           | (v2_struct_0 @ sk_A)))
% 0.65/0.86         <= (((r2_hidden @ sk_B @ 
% 0.65/0.86               (k2_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['49', '75'])).
% 0.65/0.86  thf('77', plain,
% 0.65/0.86      ((((v2_struct_0 @ sk_A)
% 0.65/0.86         | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.65/0.86         | (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.65/0.86         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.65/0.86         <= (((r2_hidden @ sk_B @ 
% 0.65/0.86               (k2_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['48', '76'])).
% 0.65/0.86  thf('78', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('79', plain,
% 0.65/0.86      ((((v2_struct_0 @ sk_A)
% 0.65/0.86         | (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.65/0.86         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.65/0.86         <= (((r2_hidden @ sk_B @ 
% 0.65/0.86               (k2_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.65/0.86      inference('demod', [status(thm)], ['77', '78'])).
% 0.65/0.86  thf('80', plain, (~ (v2_struct_0 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('81', plain,
% 0.65/0.86      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86         | (r2_orders_2 @ sk_A @ sk_B @ sk_C)))
% 0.65/0.86         <= (((r2_hidden @ sk_B @ 
% 0.65/0.86               (k2_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.65/0.86      inference('clc', [status(thm)], ['79', '80'])).
% 0.65/0.86  thf('82', plain,
% 0.65/0.86      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.65/0.86         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.65/0.86      inference('split', [status(esa)], ['41'])).
% 0.65/0.86  thf('83', plain,
% 0.65/0.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.65/0.86         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.65/0.86             ((r2_hidden @ sk_B @ 
% 0.65/0.86               (k2_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['81', '82'])).
% 0.65/0.86  thf(fc2_struct_0, axiom,
% 0.65/0.86    (![A:$i]:
% 0.65/0.86     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.65/0.86       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.65/0.86  thf('84', plain,
% 0.65/0.86      (![X7 : $i]:
% 0.65/0.86         (~ (v1_xboole_0 @ (u1_struct_0 @ X7))
% 0.65/0.86          | ~ (l1_struct_0 @ X7)
% 0.65/0.86          | (v2_struct_0 @ X7))),
% 0.65/0.86      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.65/0.86  thf('85', plain,
% 0.65/0.86      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.65/0.86         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.65/0.86             ((r2_hidden @ sk_B @ 
% 0.65/0.86               (k2_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['83', '84'])).
% 0.65/0.86  thf('86', plain, ((l1_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf(dt_l1_orders_2, axiom,
% 0.65/0.86    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.65/0.86  thf('87', plain,
% 0.65/0.86      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_orders_2 @ X10))),
% 0.65/0.86      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.65/0.86  thf('88', plain, ((l1_struct_0 @ sk_A)),
% 0.65/0.86      inference('sup-', [status(thm)], ['86', '87'])).
% 0.65/0.86  thf('89', plain,
% 0.65/0.86      (((v2_struct_0 @ sk_A))
% 0.65/0.86         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.65/0.86             ((r2_hidden @ sk_B @ 
% 0.65/0.86               (k2_orders_2 @ sk_A @ 
% 0.65/0.86                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C)))))),
% 0.65/0.86      inference('demod', [status(thm)], ['85', '88'])).
% 0.65/0.86  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('91', plain,
% 0.65/0.86      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.65/0.86       ~
% 0.65/0.86       ((r2_hidden @ sk_B @ 
% 0.65/0.86         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.65/0.86      inference('sup-', [status(thm)], ['89', '90'])).
% 0.65/0.86  thf('92', plain,
% 0.65/0.86      (~
% 0.65/0.86       ((r2_hidden @ sk_B @ 
% 0.65/0.86         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.65/0.86      inference('sat_resolution*', [status(thm)], ['44', '91'])).
% 0.65/0.86  thf('93', plain,
% 0.65/0.86      ((~ (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('simpl_trail', [status(thm)], ['43', '92'])).
% 0.65/0.86  thf('94', plain,
% 0.65/0.86      ((((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C))
% 0.65/0.86        | (v2_struct_0 @ sk_A)
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['28', '93'])).
% 0.65/0.86  thf('95', plain,
% 0.65/0.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86        | (v2_struct_0 @ sk_A)
% 0.65/0.86        | ((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C)))),
% 0.65/0.86      inference('simplify', [status(thm)], ['94'])).
% 0.65/0.86  thf('96', plain, (~ (v2_struct_0 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('97', plain,
% 0.65/0.86      ((((sk_E @ sk_B @ (k1_tarski @ sk_C) @ sk_A) = (sk_C))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('clc', [status(thm)], ['95', '96'])).
% 0.65/0.86  thf('98', plain,
% 0.65/0.86      (((m1_subset_1 @ (k1_tarski @ sk_C) @ 
% 0.65/0.86         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup+', [status(thm)], ['4', '12'])).
% 0.65/0.86  thf('99', plain,
% 0.65/0.86      (![X11 : $i, X12 : $i, X14 : $i, X15 : $i]:
% 0.65/0.86         (~ (l1_orders_2 @ X11)
% 0.65/0.86          | ~ (v5_orders_2 @ X11)
% 0.65/0.86          | ~ (v4_orders_2 @ X11)
% 0.65/0.86          | ~ (v3_orders_2 @ X11)
% 0.65/0.86          | (v2_struct_0 @ X11)
% 0.65/0.86          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.65/0.86          | (r2_hidden @ X14 @ (a_2_1_orders_2 @ X11 @ X12))
% 0.65/0.86          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X11))
% 0.65/0.86          | ((X14) != (X15))
% 0.65/0.86          | ~ (r2_orders_2 @ X11 @ X15 @ (sk_E @ X15 @ X12 @ X11)))),
% 0.65/0.86      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.65/0.86  thf('100', plain,
% 0.65/0.86      (![X11 : $i, X12 : $i, X15 : $i]:
% 0.65/0.86         (~ (r2_orders_2 @ X11 @ X15 @ (sk_E @ X15 @ X12 @ X11))
% 0.65/0.86          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X11))
% 0.65/0.86          | (r2_hidden @ X15 @ (a_2_1_orders_2 @ X11 @ X12))
% 0.65/0.86          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.65/0.86          | (v2_struct_0 @ X11)
% 0.65/0.86          | ~ (v3_orders_2 @ X11)
% 0.65/0.86          | ~ (v4_orders_2 @ X11)
% 0.65/0.86          | ~ (v5_orders_2 @ X11)
% 0.65/0.86          | ~ (l1_orders_2 @ X11))),
% 0.65/0.86      inference('simplify', [status(thm)], ['99'])).
% 0.65/0.86  thf('101', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | ~ (l1_orders_2 @ sk_A)
% 0.65/0.86          | ~ (v5_orders_2 @ sk_A)
% 0.65/0.86          | ~ (v4_orders_2 @ sk_A)
% 0.65/0.86          | ~ (v3_orders_2 @ sk_A)
% 0.65/0.86          | (v2_struct_0 @ sk_A)
% 0.65/0.86          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.65/0.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | ~ (r2_orders_2 @ sk_A @ X0 @ 
% 0.65/0.86               (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['98', '100'])).
% 0.65/0.86  thf('102', plain, ((l1_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('103', plain, ((v5_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('104', plain, ((v4_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('105', plain, ((v3_orders_2 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('106', plain,
% 0.65/0.86      (![X0 : $i]:
% 0.65/0.86         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | (v2_struct_0 @ sk_A)
% 0.65/0.86          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.65/0.86          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86          | ~ (r2_orders_2 @ sk_A @ X0 @ 
% 0.65/0.86               (sk_E @ X0 @ (k1_tarski @ sk_C) @ sk_A)))),
% 0.65/0.86      inference('demod', [status(thm)], ['101', '102', '103', '104', '105'])).
% 0.65/0.86  thf('107', plain,
% 0.65/0.86      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.65/0.86        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.65/0.86        | (v2_struct_0 @ sk_A)
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('sup-', [status(thm)], ['97', '106'])).
% 0.65/0.86  thf('108', plain,
% 0.65/0.86      (((r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.65/0.86         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.65/0.86      inference('split', [status(esa)], ['50'])).
% 0.65/0.86  thf('109', plain,
% 0.65/0.86      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.65/0.86       ((r2_hidden @ sk_B @ 
% 0.65/0.86         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C))))),
% 0.65/0.86      inference('split', [status(esa)], ['50'])).
% 0.65/0.86  thf('110', plain, (((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.65/0.86      inference('sat_resolution*', [status(thm)], ['44', '91', '109'])).
% 0.65/0.86  thf('111', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C)),
% 0.65/0.86      inference('simpl_trail', [status(thm)], ['108', '110'])).
% 0.65/0.86  thf('112', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('113', plain,
% 0.65/0.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.65/0.86        | (v2_struct_0 @ sk_A)
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('demod', [status(thm)], ['107', '111', '112'])).
% 0.65/0.86  thf('114', plain,
% 0.65/0.86      (((v2_struct_0 @ sk_A)
% 0.65/0.86        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('simplify', [status(thm)], ['113'])).
% 0.65/0.86  thf('115', plain, (~ (v2_struct_0 @ sk_A)),
% 0.65/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.65/0.86  thf('116', plain,
% 0.65/0.86      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.65/0.86        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C))))),
% 0.65/0.86      inference('clc', [status(thm)], ['114', '115'])).
% 0.65/0.86  thf('117', plain,
% 0.65/0.86      ((~ (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C)))
% 0.65/0.86        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.65/0.86      inference('simpl_trail', [status(thm)], ['43', '92'])).
% 0.65/0.86  thf('118', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.65/0.86      inference('clc', [status(thm)], ['116', '117'])).
% 0.65/0.86  thf('119', plain,
% 0.65/0.86      (![X7 : $i]:
% 0.65/0.86         (~ (v1_xboole_0 @ (u1_struct_0 @ X7))
% 0.65/0.86          | ~ (l1_struct_0 @ X7)
% 0.65/0.86          | (v2_struct_0 @ X7))),
% 0.65/0.86      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.65/0.86  thf('120', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.65/0.86      inference('sup-', [status(thm)], ['118', '119'])).
% 0.65/0.86  thf('121', plain, ((l1_struct_0 @ sk_A)),
% 0.65/0.86      inference('sup-', [status(thm)], ['86', '87'])).
% 0.65/0.86  thf('122', plain, ((v2_struct_0 @ sk_A)),
% 0.65/0.86      inference('demod', [status(thm)], ['120', '121'])).
% 0.65/0.86  thf('123', plain, ($false), inference('demod', [status(thm)], ['0', '122'])).
% 0.65/0.86  
% 0.65/0.86  % SZS output end Refutation
% 0.65/0.86  
% 0.65/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
