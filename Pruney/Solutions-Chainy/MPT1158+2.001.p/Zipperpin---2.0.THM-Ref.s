%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xYBrlduTpy

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:57 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 763 expanded)
%              Number of leaves         :   29 ( 222 expanded)
%              Depth                    :   33
%              Number of atoms          : 1531 (13854 expanded)
%              Number of equality atoms :   32 ( 153 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

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
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( ( k6_domain_1 @ X17 @ X18 )
        = ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ X9 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
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
    ! [X12: $i,X13: $i,X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r2_hidden @ X15 @ ( a_2_1_orders_2 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X12 ) )
      | ( X15 != X16 )
      | ( r2_hidden @ ( sk_E @ X16 @ X13 @ X12 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('11',plain,(
    ! [X12: $i,X13: $i,X16: $i] :
      ( ( r2_hidden @ ( sk_E @ X16 @ X13 @ X12 ) @ X13 )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X12 ) )
      | ( r2_hidden @ X16 @ ( a_2_1_orders_2 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v2_struct_0 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k1_tarski @ sk_C_1 ) @ sk_A ) @ ( k1_tarski @ sk_C_1 ) ) ) ),
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
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k1_tarski @ sk_C_1 ) @ sk_A ) @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_E @ sk_B @ ( k1_tarski @ sk_C_1 ) @ sk_A ) @ ( k1_tarski @ sk_C_1 ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','17'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('19',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('20',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C_1 ) @ sk_A )
      = sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 )
      = ( k1_tarski @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('23',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
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

thf('24',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X8 ) ) )
      | ( ( k2_orders_2 @ X8 @ X7 )
        = ( a_2_1_orders_2 @ X8 @ X7 ) )
      | ~ ( l1_orders_2 @ X8 )
      | ~ ( v5_orders_2 @ X8 )
      | ~ ( v4_orders_2 @ X8 )
      | ~ ( v3_orders_2 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( ~ ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['35'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) )
      = ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('40',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ( ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['39','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('44',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( X15
        = ( sk_D @ X13 @ X12 @ X15 ) )
      | ~ ( r2_hidden @ X15 @ ( a_2_1_orders_2 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ( X0
        = ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ( X0
        = ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( sk_B
        = ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,
    ( ( ( sk_B
        = ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_B
        = ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('56',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['39','41'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('59',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ( r2_orders_2 @ X12 @ ( sk_D @ X13 @ X12 @ X15 ) @ X14 )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( a_2_1_orders_2 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_C_1 ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_A @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_C_1 ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_A @ X0 ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B ) @ X0 )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_1 ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['57','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_1 ) )
        | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B ) @ X0 )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['56','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B ) @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( r2_orders_2 @ sk_A @ ( sk_D @ ( k1_tarski @ sk_C_1 ) @ sk_A @ sk_B ) @ sk_C_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup+',[status(thm)],['54','72'])).

thf('74',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['35'])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('77',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('78',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('80',plain,(
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('81',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference('sat_resolution*',[status(thm)],['38','84'])).

thf('86',plain,
    ( ~ ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['37','85'])).

thf('87',plain,
    ( ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C_1 ) @ sk_A )
      = sk_C_1 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','86'])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C_1 ) @ sk_A )
      = sk_C_1 ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( sk_E @ sk_B @ ( k1_tarski @ sk_C_1 ) @ sk_A )
      = sk_C_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_C_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('92',plain,(
    ! [X12: $i,X13: $i,X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( r2_hidden @ X15 @ ( a_2_1_orders_2 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X12 ) )
      | ( X15 != X16 )
      | ~ ( r2_orders_2 @ X12 @ X16 @ ( sk_E @ X16 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('93',plain,(
    ! [X12: $i,X13: $i,X16: $i] :
      ( ~ ( r2_orders_2 @ X12 @ X16 @ ( sk_E @ X16 @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X12 ) )
      | ( r2_hidden @ X16 @ ( a_2_1_orders_2 @ X12 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( v2_struct_0 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_E @ X0 @ ( k1_tarski @ sk_C_1 ) @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ X0 @ ( sk_E @ X0 @ ( k1_tarski @ sk_C_1 ) @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','99'])).

thf('101',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['40'])).

thf('102',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_B @ ( k2_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_C_1 ) ) ) ),
    inference(split,[status(esa)],['40'])).

thf('103',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['38','84','102'])).

thf('104',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['101','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','104','105'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( r2_hidden @ sk_B @ ( a_2_1_orders_2 @ sk_A @ ( k1_tarski @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['37','85'])).

thf('111',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('113',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['79','80'])).

thf('115',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['113','114'])).

thf('116',plain,(
    $false ),
    inference(demod,[status(thm)],['0','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xYBrlduTpy
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.69/0.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.90  % Solved by: fo/fo7.sh
% 0.69/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.90  % done 598 iterations in 0.448s
% 0.69/0.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.90  % SZS output start Refutation
% 0.69/0.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.69/0.90  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 0.69/0.90  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.69/0.90  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.69/0.90  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.69/0.90  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.69/0.90  thf(sk_B_type, type, sk_B: $i).
% 0.69/0.90  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.69/0.90  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.69/0.90  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.69/0.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.90  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.69/0.90  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.69/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.69/0.90  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.69/0.90  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.69/0.90  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.69/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.90  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.90  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.69/0.90  thf(t52_orders_2, conjecture,
% 0.69/0.90    (![A:$i]:
% 0.69/0.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.69/0.90         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.69/0.90       ( ![B:$i]:
% 0.69/0.90         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.69/0.90           ( ![C:$i]:
% 0.69/0.90             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.69/0.90               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.69/0.90                 ( r2_hidden @
% 0.69/0.90                   B @ 
% 0.69/0.90                   ( k2_orders_2 @
% 0.69/0.90                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ))).
% 0.69/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.90    (~( ![A:$i]:
% 0.69/0.90        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.69/0.90            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.69/0.90          ( ![B:$i]:
% 0.69/0.90            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.69/0.90              ( ![C:$i]:
% 0.69/0.90                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.69/0.90                  ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.69/0.90                    ( r2_hidden @
% 0.69/0.90                      B @ 
% 0.69/0.90                      ( k2_orders_2 @
% 0.69/0.90                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) ) ) ) ) ) ) ) )),
% 0.69/0.90    inference('cnf.neg', [status(esa)], [t52_orders_2])).
% 0.69/0.90  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('2', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(redefinition_k6_domain_1, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.69/0.90       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.69/0.90  thf('3', plain,
% 0.69/0.90      (![X17 : $i, X18 : $i]:
% 0.69/0.90         ((v1_xboole_0 @ X17)
% 0.69/0.90          | ~ (m1_subset_1 @ X18 @ X17)
% 0.69/0.90          | ((k6_domain_1 @ X17 @ X18) = (k1_tarski @ X18)))),
% 0.69/0.90      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.69/0.90  thf('4', plain,
% 0.69/0.90      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.69/0.90        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['2', '3'])).
% 0.69/0.90  thf('5', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(dt_k6_domain_1, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.69/0.90       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.69/0.90  thf('6', plain,
% 0.69/0.90      (![X9 : $i, X10 : $i]:
% 0.69/0.90         ((v1_xboole_0 @ X9)
% 0.69/0.90          | ~ (m1_subset_1 @ X10 @ X9)
% 0.69/0.90          | (m1_subset_1 @ (k6_domain_1 @ X9 @ X10) @ (k1_zfmisc_1 @ X9)))),
% 0.69/0.90      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.69/0.90  thf('7', plain,
% 0.69/0.90      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.69/0.90         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.90        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['5', '6'])).
% 0.69/0.90  thf('8', plain,
% 0.69/0.90      (((m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.69/0.90         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.90        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('sup+', [status(thm)], ['4', '7'])).
% 0.69/0.90  thf('9', plain,
% 0.69/0.90      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90        | (m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.69/0.90           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.90      inference('simplify', [status(thm)], ['8'])).
% 0.69/0.90  thf(fraenkel_a_2_1_orders_2, axiom,
% 0.69/0.90    (![A:$i,B:$i,C:$i]:
% 0.69/0.90     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.69/0.90         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.69/0.90         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.69/0.90       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 0.69/0.90         ( ?[D:$i]:
% 0.69/0.90           ( ( ![E:$i]:
% 0.69/0.90               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.69/0.90                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 0.69/0.90             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.69/0.90  thf('10', plain,
% 0.69/0.90      (![X12 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.69/0.90         (~ (l1_orders_2 @ X12)
% 0.69/0.90          | ~ (v5_orders_2 @ X12)
% 0.69/0.90          | ~ (v4_orders_2 @ X12)
% 0.69/0.90          | ~ (v3_orders_2 @ X12)
% 0.69/0.90          | (v2_struct_0 @ X12)
% 0.69/0.90          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.69/0.90          | (r2_hidden @ X15 @ (a_2_1_orders_2 @ X12 @ X13))
% 0.69/0.90          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.69/0.90          | ((X15) != (X16))
% 0.69/0.90          | (r2_hidden @ (sk_E @ X16 @ X13 @ X12) @ X13))),
% 0.69/0.90      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.69/0.90  thf('11', plain,
% 0.69/0.90      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.69/0.90         ((r2_hidden @ (sk_E @ X16 @ X13 @ X12) @ X13)
% 0.69/0.90          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.69/0.90          | (r2_hidden @ X16 @ (a_2_1_orders_2 @ X12 @ X13))
% 0.69/0.90          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.69/0.90          | (v2_struct_0 @ X12)
% 0.69/0.90          | ~ (v3_orders_2 @ X12)
% 0.69/0.90          | ~ (v4_orders_2 @ X12)
% 0.69/0.90          | ~ (v5_orders_2 @ X12)
% 0.69/0.90          | ~ (l1_orders_2 @ X12))),
% 0.69/0.90      inference('simplify', [status(thm)], ['10'])).
% 0.69/0.90  thf('12', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90          | ~ (l1_orders_2 @ sk_A)
% 0.69/0.90          | ~ (v5_orders_2 @ sk_A)
% 0.69/0.90          | ~ (v4_orders_2 @ sk_A)
% 0.69/0.90          | ~ (v3_orders_2 @ sk_A)
% 0.69/0.90          | (v2_struct_0 @ sk_A)
% 0.69/0.90          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90          | (r2_hidden @ (sk_E @ X0 @ (k1_tarski @ sk_C_1) @ sk_A) @ 
% 0.69/0.90             (k1_tarski @ sk_C_1)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['9', '11'])).
% 0.69/0.90  thf('13', plain, ((l1_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('14', plain, ((v5_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('15', plain, ((v4_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('16', plain, ((v3_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('17', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90          | (v2_struct_0 @ sk_A)
% 0.69/0.90          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90          | (r2_hidden @ (sk_E @ X0 @ (k1_tarski @ sk_C_1) @ sk_A) @ 
% 0.69/0.90             (k1_tarski @ sk_C_1)))),
% 0.69/0.90      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.69/0.90  thf('18', plain,
% 0.69/0.90      (((r2_hidden @ (sk_E @ sk_B @ (k1_tarski @ sk_C_1) @ sk_A) @ 
% 0.69/0.90         (k1_tarski @ sk_C_1))
% 0.69/0.90        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.69/0.90        | (v2_struct_0 @ sk_A)
% 0.69/0.90        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['1', '17'])).
% 0.69/0.90  thf(d1_tarski, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.69/0.90       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.69/0.90  thf('19', plain,
% 0.69/0.90      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.69/0.90         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.69/0.90      inference('cnf', [status(esa)], [d1_tarski])).
% 0.69/0.90  thf('20', plain,
% 0.69/0.90      (![X0 : $i, X3 : $i]:
% 0.69/0.90         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.69/0.90      inference('simplify', [status(thm)], ['19'])).
% 0.69/0.90  thf('21', plain,
% 0.69/0.90      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90        | (v2_struct_0 @ sk_A)
% 0.69/0.90        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.69/0.90        | ((sk_E @ sk_B @ (k1_tarski @ sk_C_1) @ sk_A) = (sk_C_1)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['18', '20'])).
% 0.69/0.90  thf('22', plain,
% 0.69/0.90      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) = (k1_tarski @ sk_C_1))
% 0.69/0.90        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['2', '3'])).
% 0.69/0.90  thf('23', plain,
% 0.69/0.90      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1) @ 
% 0.69/0.90         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.69/0.90        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['5', '6'])).
% 0.69/0.90  thf(d13_orders_2, axiom,
% 0.69/0.90    (![A:$i]:
% 0.69/0.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.69/0.90         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.69/0.90       ( ![B:$i]:
% 0.69/0.90         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.69/0.90           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 0.69/0.90  thf('24', plain,
% 0.69/0.90      (![X7 : $i, X8 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (u1_struct_0 @ X8)))
% 0.69/0.90          | ((k2_orders_2 @ X8 @ X7) = (a_2_1_orders_2 @ X8 @ X7))
% 0.69/0.90          | ~ (l1_orders_2 @ X8)
% 0.69/0.90          | ~ (v5_orders_2 @ X8)
% 0.69/0.90          | ~ (v4_orders_2 @ X8)
% 0.69/0.90          | ~ (v3_orders_2 @ X8)
% 0.69/0.90          | (v2_struct_0 @ X8))),
% 0.69/0.90      inference('cnf', [status(esa)], [d13_orders_2])).
% 0.69/0.90  thf('25', plain,
% 0.69/0.90      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90        | (v2_struct_0 @ sk_A)
% 0.69/0.90        | ~ (v3_orders_2 @ sk_A)
% 0.69/0.90        | ~ (v4_orders_2 @ sk_A)
% 0.69/0.90        | ~ (v5_orders_2 @ sk_A)
% 0.69/0.90        | ~ (l1_orders_2 @ sk_A)
% 0.69/0.90        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.69/0.90            = (a_2_1_orders_2 @ sk_A @ 
% 0.69/0.90               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 0.69/0.90      inference('sup-', [status(thm)], ['23', '24'])).
% 0.69/0.90  thf('26', plain, ((v3_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('27', plain, ((v4_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('28', plain, ((v5_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('29', plain, ((l1_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('30', plain,
% 0.69/0.90      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90        | (v2_struct_0 @ sk_A)
% 0.69/0.90        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.69/0.90            = (a_2_1_orders_2 @ sk_A @ 
% 0.69/0.90               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 0.69/0.90      inference('demod', [status(thm)], ['25', '26', '27', '28', '29'])).
% 0.69/0.90  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('32', plain,
% 0.69/0.90      ((((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.69/0.90          = (a_2_1_orders_2 @ sk_A @ 
% 0.69/0.90             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.69/0.90        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('clc', [status(thm)], ['30', '31'])).
% 0.69/0.90  thf('33', plain,
% 0.69/0.90      ((((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.69/0.90          = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.69/0.90        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('sup+', [status(thm)], ['22', '32'])).
% 0.69/0.90  thf('34', plain,
% 0.69/0.90      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.69/0.90            = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1))))),
% 0.69/0.90      inference('simplify', [status(thm)], ['33'])).
% 0.69/0.90  thf('35', plain,
% 0.69/0.90      ((~ (r2_hidden @ sk_B @ 
% 0.69/0.90           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.69/0.90        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('36', plain,
% 0.69/0.90      ((~ (r2_hidden @ sk_B @ 
% 0.69/0.90           (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))
% 0.69/0.90         <= (~
% 0.69/0.90             ((r2_hidden @ sk_B @ 
% 0.69/0.90               (k2_orders_2 @ sk_A @ 
% 0.69/0.90                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.69/0.90      inference('split', [status(esa)], ['35'])).
% 0.69/0.90  thf('37', plain,
% 0.69/0.90      (((~ (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.69/0.90         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.69/0.90         <= (~
% 0.69/0.90             ((r2_hidden @ sk_B @ 
% 0.69/0.90               (k2_orders_2 @ sk_A @ 
% 0.69/0.90                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.69/0.90      inference('sup-', [status(thm)], ['34', '36'])).
% 0.69/0.90  thf('38', plain,
% 0.69/0.90      (~
% 0.69/0.90       ((r2_hidden @ sk_B @ 
% 0.69/0.90         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))) | 
% 0.69/0.90       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 0.69/0.90      inference('split', [status(esa)], ['35'])).
% 0.69/0.90  thf('39', plain,
% 0.69/0.90      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90        | ((k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))
% 0.69/0.90            = (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1))))),
% 0.69/0.90      inference('simplify', [status(thm)], ['33'])).
% 0.69/0.90  thf('40', plain,
% 0.69/0.90      (((r2_hidden @ sk_B @ 
% 0.69/0.90         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))
% 0.69/0.90        | (r2_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('41', plain,
% 0.69/0.90      (((r2_hidden @ sk_B @ 
% 0.69/0.90         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))
% 0.69/0.90         <= (((r2_hidden @ sk_B @ 
% 0.69/0.90               (k2_orders_2 @ sk_A @ 
% 0.69/0.90                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.69/0.90      inference('split', [status(esa)], ['40'])).
% 0.69/0.90  thf('42', plain,
% 0.69/0.90      ((((r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.69/0.90         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.69/0.90         <= (((r2_hidden @ sk_B @ 
% 0.69/0.90               (k2_orders_2 @ sk_A @ 
% 0.69/0.90                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['39', '41'])).
% 0.69/0.90  thf('43', plain,
% 0.69/0.90      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90        | (m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.69/0.90           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.90      inference('simplify', [status(thm)], ['8'])).
% 0.69/0.90  thf('44', plain,
% 0.69/0.90      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.69/0.90         (~ (l1_orders_2 @ X12)
% 0.69/0.90          | ~ (v5_orders_2 @ X12)
% 0.69/0.90          | ~ (v4_orders_2 @ X12)
% 0.69/0.90          | ~ (v3_orders_2 @ X12)
% 0.69/0.90          | (v2_struct_0 @ X12)
% 0.69/0.90          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.69/0.90          | ((X15) = (sk_D @ X13 @ X12 @ X15))
% 0.69/0.90          | ~ (r2_hidden @ X15 @ (a_2_1_orders_2 @ X12 @ X13)))),
% 0.69/0.90      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.69/0.90  thf('45', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.69/0.90          | ((X0) = (sk_D @ (k1_tarski @ sk_C_1) @ sk_A @ X0))
% 0.69/0.90          | (v2_struct_0 @ sk_A)
% 0.69/0.90          | ~ (v3_orders_2 @ sk_A)
% 0.69/0.90          | ~ (v4_orders_2 @ sk_A)
% 0.69/0.90          | ~ (v5_orders_2 @ sk_A)
% 0.69/0.90          | ~ (l1_orders_2 @ sk_A))),
% 0.69/0.90      inference('sup-', [status(thm)], ['43', '44'])).
% 0.69/0.90  thf('46', plain, ((v3_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('47', plain, ((v4_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('48', plain, ((v5_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('49', plain, ((l1_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('50', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.69/0.90          | ((X0) = (sk_D @ (k1_tarski @ sk_C_1) @ sk_A @ X0))
% 0.69/0.90          | (v2_struct_0 @ sk_A))),
% 0.69/0.90      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 0.69/0.90  thf('51', plain,
% 0.69/0.90      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90         | (v2_struct_0 @ sk_A)
% 0.69/0.90         | ((sk_B) = (sk_D @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B))
% 0.69/0.90         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.69/0.90         <= (((r2_hidden @ sk_B @ 
% 0.69/0.90               (k2_orders_2 @ sk_A @ 
% 0.69/0.90                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.69/0.90      inference('sup-', [status(thm)], ['42', '50'])).
% 0.69/0.90  thf('52', plain,
% 0.69/0.90      (((((sk_B) = (sk_D @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B))
% 0.69/0.90         | (v2_struct_0 @ sk_A)
% 0.69/0.90         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.69/0.90         <= (((r2_hidden @ sk_B @ 
% 0.69/0.90               (k2_orders_2 @ sk_A @ 
% 0.69/0.90                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.69/0.90      inference('simplify', [status(thm)], ['51'])).
% 0.69/0.90  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('54', plain,
% 0.69/0.90      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90         | ((sk_B) = (sk_D @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B))))
% 0.69/0.90         <= (((r2_hidden @ sk_B @ 
% 0.69/0.90               (k2_orders_2 @ sk_A @ 
% 0.69/0.90                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.69/0.90      inference('clc', [status(thm)], ['52', '53'])).
% 0.69/0.90  thf('55', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.90         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.69/0.90      inference('cnf', [status(esa)], [d1_tarski])).
% 0.69/0.90  thf('56', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.69/0.90      inference('simplify', [status(thm)], ['55'])).
% 0.69/0.90  thf('57', plain,
% 0.69/0.90      ((((r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.69/0.90         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.69/0.90         <= (((r2_hidden @ sk_B @ 
% 0.69/0.90               (k2_orders_2 @ sk_A @ 
% 0.69/0.90                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['39', '41'])).
% 0.69/0.90  thf('58', plain,
% 0.69/0.90      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90        | (m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.69/0.90           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.90      inference('simplify', [status(thm)], ['8'])).
% 0.69/0.90  thf('59', plain,
% 0.69/0.90      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.69/0.90         (~ (l1_orders_2 @ X12)
% 0.69/0.90          | ~ (v5_orders_2 @ X12)
% 0.69/0.90          | ~ (v4_orders_2 @ X12)
% 0.69/0.90          | ~ (v3_orders_2 @ X12)
% 0.69/0.90          | (v2_struct_0 @ X12)
% 0.69/0.90          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.69/0.90          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.69/0.90          | (r2_orders_2 @ X12 @ (sk_D @ X13 @ X12 @ X15) @ X14)
% 0.69/0.90          | ~ (r2_hidden @ X14 @ X13)
% 0.69/0.90          | ~ (r2_hidden @ X15 @ (a_2_1_orders_2 @ X12 @ X13)))),
% 0.69/0.90      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.69/0.90  thf('60', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.69/0.90          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_C_1))
% 0.69/0.90          | (r2_orders_2 @ sk_A @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_A @ X0) @ 
% 0.69/0.90             X1)
% 0.69/0.90          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.69/0.90          | (v2_struct_0 @ sk_A)
% 0.69/0.90          | ~ (v3_orders_2 @ sk_A)
% 0.69/0.90          | ~ (v4_orders_2 @ sk_A)
% 0.69/0.90          | ~ (v5_orders_2 @ sk_A)
% 0.69/0.90          | ~ (l1_orders_2 @ sk_A))),
% 0.69/0.90      inference('sup-', [status(thm)], ['58', '59'])).
% 0.69/0.90  thf('61', plain, ((v3_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('62', plain, ((v4_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('63', plain, ((v5_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('64', plain, ((l1_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('65', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90          | ~ (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.69/0.90          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_C_1))
% 0.69/0.90          | (r2_orders_2 @ sk_A @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_A @ X0) @ 
% 0.69/0.90             X1)
% 0.69/0.90          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.69/0.90          | (v2_struct_0 @ sk_A))),
% 0.69/0.90      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 0.69/0.90  thf('66', plain,
% 0.69/0.90      ((![X0 : $i]:
% 0.69/0.90          ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90           | (v2_struct_0 @ sk_A)
% 0.69/0.90           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90           | (r2_orders_2 @ sk_A @ 
% 0.69/0.90              (sk_D @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B) @ X0)
% 0.69/0.90           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_C_1))
% 0.69/0.90           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.69/0.90         <= (((r2_hidden @ sk_B @ 
% 0.69/0.90               (k2_orders_2 @ sk_A @ 
% 0.69/0.90                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.69/0.90      inference('sup-', [status(thm)], ['57', '65'])).
% 0.69/0.90  thf('67', plain,
% 0.69/0.90      ((![X0 : $i]:
% 0.69/0.90          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_C_1))
% 0.69/0.90           | (r2_orders_2 @ sk_A @ 
% 0.69/0.90              (sk_D @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B) @ X0)
% 0.69/0.90           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90           | (v2_struct_0 @ sk_A)
% 0.69/0.90           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.69/0.90         <= (((r2_hidden @ sk_B @ 
% 0.69/0.90               (k2_orders_2 @ sk_A @ 
% 0.69/0.90                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.69/0.90      inference('simplify', [status(thm)], ['66'])).
% 0.69/0.90  thf('68', plain,
% 0.69/0.90      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90         | (v2_struct_0 @ sk_A)
% 0.69/0.90         | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.69/0.90         | (r2_orders_2 @ sk_A @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B) @ 
% 0.69/0.90            sk_C_1)))
% 0.69/0.90         <= (((r2_hidden @ sk_B @ 
% 0.69/0.90               (k2_orders_2 @ sk_A @ 
% 0.69/0.90                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.69/0.90      inference('sup-', [status(thm)], ['56', '67'])).
% 0.69/0.90  thf('69', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('70', plain,
% 0.69/0.90      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90         | (v2_struct_0 @ sk_A)
% 0.69/0.90         | (r2_orders_2 @ sk_A @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B) @ 
% 0.69/0.90            sk_C_1)))
% 0.69/0.90         <= (((r2_hidden @ sk_B @ 
% 0.69/0.90               (k2_orders_2 @ sk_A @ 
% 0.69/0.90                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.69/0.90      inference('demod', [status(thm)], ['68', '69'])).
% 0.69/0.90  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('72', plain,
% 0.69/0.90      ((((r2_orders_2 @ sk_A @ (sk_D @ (k1_tarski @ sk_C_1) @ sk_A @ sk_B) @ 
% 0.69/0.90          sk_C_1)
% 0.69/0.90         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.69/0.90         <= (((r2_hidden @ sk_B @ 
% 0.69/0.90               (k2_orders_2 @ sk_A @ 
% 0.69/0.90                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.69/0.90      inference('clc', [status(thm)], ['70', '71'])).
% 0.69/0.90  thf('73', plain,
% 0.69/0.90      ((((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)
% 0.69/0.90         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.69/0.90         <= (((r2_hidden @ sk_B @ 
% 0.69/0.90               (k2_orders_2 @ sk_A @ 
% 0.69/0.90                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.69/0.90      inference('sup+', [status(thm)], ['54', '72'])).
% 0.69/0.90  thf('74', plain,
% 0.69/0.90      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90         | (r2_orders_2 @ sk_A @ sk_B @ sk_C_1)))
% 0.69/0.90         <= (((r2_hidden @ sk_B @ 
% 0.69/0.90               (k2_orders_2 @ sk_A @ 
% 0.69/0.90                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.69/0.90      inference('simplify', [status(thm)], ['73'])).
% 0.69/0.90  thf('75', plain,
% 0.69/0.90      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C_1))
% 0.69/0.90         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)))),
% 0.69/0.90      inference('split', [status(esa)], ['35'])).
% 0.69/0.90  thf('76', plain,
% 0.69/0.90      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.69/0.90         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.69/0.90             ((r2_hidden @ sk_B @ 
% 0.69/0.90               (k2_orders_2 @ sk_A @ 
% 0.69/0.90                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.69/0.90      inference('sup-', [status(thm)], ['74', '75'])).
% 0.69/0.90  thf(fc2_struct_0, axiom,
% 0.69/0.90    (![A:$i]:
% 0.69/0.90     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.69/0.90       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.69/0.90  thf('77', plain,
% 0.69/0.90      (![X6 : $i]:
% 0.69/0.90         (~ (v1_xboole_0 @ (u1_struct_0 @ X6))
% 0.69/0.90          | ~ (l1_struct_0 @ X6)
% 0.69/0.90          | (v2_struct_0 @ X6))),
% 0.69/0.90      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.69/0.90  thf('78', plain,
% 0.69/0.90      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.69/0.90         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.69/0.90             ((r2_hidden @ sk_B @ 
% 0.69/0.90               (k2_orders_2 @ sk_A @ 
% 0.69/0.90                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.69/0.90      inference('sup-', [status(thm)], ['76', '77'])).
% 0.69/0.90  thf('79', plain, ((l1_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(dt_l1_orders_2, axiom,
% 0.69/0.90    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.69/0.90  thf('80', plain,
% 0.69/0.90      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_orders_2 @ X11))),
% 0.69/0.90      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.69/0.90  thf('81', plain, ((l1_struct_0 @ sk_A)),
% 0.69/0.90      inference('sup-', [status(thm)], ['79', '80'])).
% 0.69/0.90  thf('82', plain,
% 0.69/0.90      (((v2_struct_0 @ sk_A))
% 0.69/0.90         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.69/0.90             ((r2_hidden @ sk_B @ 
% 0.69/0.90               (k2_orders_2 @ sk_A @ 
% 0.69/0.90                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1)))))),
% 0.69/0.90      inference('demod', [status(thm)], ['78', '81'])).
% 0.69/0.90  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('84', plain,
% 0.69/0.90      (((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.69/0.90       ~
% 0.69/0.90       ((r2_hidden @ sk_B @ 
% 0.69/0.90         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 0.69/0.90      inference('sup-', [status(thm)], ['82', '83'])).
% 0.69/0.90  thf('85', plain,
% 0.69/0.90      (~
% 0.69/0.90       ((r2_hidden @ sk_B @ 
% 0.69/0.90         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 0.69/0.90      inference('sat_resolution*', [status(thm)], ['38', '84'])).
% 0.69/0.90  thf('86', plain,
% 0.69/0.90      ((~ (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.69/0.90        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('simpl_trail', [status(thm)], ['37', '85'])).
% 0.69/0.90  thf('87', plain,
% 0.69/0.90      ((((sk_E @ sk_B @ (k1_tarski @ sk_C_1) @ sk_A) = (sk_C_1))
% 0.69/0.90        | (v2_struct_0 @ sk_A)
% 0.69/0.90        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['21', '86'])).
% 0.69/0.90  thf('88', plain,
% 0.69/0.90      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90        | (v2_struct_0 @ sk_A)
% 0.69/0.90        | ((sk_E @ sk_B @ (k1_tarski @ sk_C_1) @ sk_A) = (sk_C_1)))),
% 0.69/0.90      inference('simplify', [status(thm)], ['87'])).
% 0.69/0.90  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('90', plain,
% 0.69/0.90      ((((sk_E @ sk_B @ (k1_tarski @ sk_C_1) @ sk_A) = (sk_C_1))
% 0.69/0.90        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('clc', [status(thm)], ['88', '89'])).
% 0.69/0.90  thf('91', plain,
% 0.69/0.90      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90        | (m1_subset_1 @ (k1_tarski @ sk_C_1) @ 
% 0.69/0.90           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.69/0.90      inference('simplify', [status(thm)], ['8'])).
% 0.69/0.90  thf('92', plain,
% 0.69/0.90      (![X12 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.69/0.90         (~ (l1_orders_2 @ X12)
% 0.69/0.90          | ~ (v5_orders_2 @ X12)
% 0.69/0.90          | ~ (v4_orders_2 @ X12)
% 0.69/0.90          | ~ (v3_orders_2 @ X12)
% 0.69/0.90          | (v2_struct_0 @ X12)
% 0.69/0.90          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.69/0.90          | (r2_hidden @ X15 @ (a_2_1_orders_2 @ X12 @ X13))
% 0.69/0.90          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.69/0.90          | ((X15) != (X16))
% 0.69/0.90          | ~ (r2_orders_2 @ X12 @ X16 @ (sk_E @ X16 @ X13 @ X12)))),
% 0.69/0.90      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.69/0.90  thf('93', plain,
% 0.69/0.90      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.69/0.90         (~ (r2_orders_2 @ X12 @ X16 @ (sk_E @ X16 @ X13 @ X12))
% 0.69/0.90          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X12))
% 0.69/0.90          | (r2_hidden @ X16 @ (a_2_1_orders_2 @ X12 @ X13))
% 0.69/0.90          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.69/0.90          | (v2_struct_0 @ X12)
% 0.69/0.90          | ~ (v3_orders_2 @ X12)
% 0.69/0.90          | ~ (v4_orders_2 @ X12)
% 0.69/0.90          | ~ (v5_orders_2 @ X12)
% 0.69/0.90          | ~ (l1_orders_2 @ X12))),
% 0.69/0.90      inference('simplify', [status(thm)], ['92'])).
% 0.69/0.90  thf('94', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90          | ~ (l1_orders_2 @ sk_A)
% 0.69/0.90          | ~ (v5_orders_2 @ sk_A)
% 0.69/0.90          | ~ (v4_orders_2 @ sk_A)
% 0.69/0.90          | ~ (v3_orders_2 @ sk_A)
% 0.69/0.90          | (v2_struct_0 @ sk_A)
% 0.69/0.90          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90          | ~ (r2_orders_2 @ sk_A @ X0 @ 
% 0.69/0.90               (sk_E @ X0 @ (k1_tarski @ sk_C_1) @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['91', '93'])).
% 0.69/0.90  thf('95', plain, ((l1_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('96', plain, ((v5_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('97', plain, ((v4_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('98', plain, ((v3_orders_2 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('99', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90          | (v2_struct_0 @ sk_A)
% 0.69/0.90          | (r2_hidden @ X0 @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90          | ~ (r2_orders_2 @ sk_A @ X0 @ 
% 0.69/0.90               (sk_E @ X0 @ (k1_tarski @ sk_C_1) @ sk_A)))),
% 0.69/0.90      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 0.69/0.90  thf('100', plain,
% 0.69/0.90      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C_1)
% 0.69/0.90        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90        | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.69/0.90        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.69/0.90        | (v2_struct_0 @ sk_A)
% 0.69/0.90        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['90', '99'])).
% 0.69/0.90  thf('101', plain,
% 0.69/0.90      (((r2_orders_2 @ sk_A @ sk_B @ sk_C_1))
% 0.69/0.90         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)))),
% 0.69/0.90      inference('split', [status(esa)], ['40'])).
% 0.69/0.90  thf('102', plain,
% 0.69/0.90      (((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.69/0.90       ((r2_hidden @ sk_B @ 
% 0.69/0.90         (k2_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_C_1))))),
% 0.69/0.90      inference('split', [status(esa)], ['40'])).
% 0.69/0.90  thf('103', plain, (((r2_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 0.69/0.90      inference('sat_resolution*', [status(thm)], ['38', '84', '102'])).
% 0.69/0.90  thf('104', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)),
% 0.69/0.90      inference('simpl_trail', [status(thm)], ['101', '103'])).
% 0.69/0.90  thf('105', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('106', plain,
% 0.69/0.90      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.69/0.90        | (v2_struct_0 @ sk_A)
% 0.69/0.90        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('demod', [status(thm)], ['100', '104', '105'])).
% 0.69/0.90  thf('107', plain,
% 0.69/0.90      (((v2_struct_0 @ sk_A)
% 0.69/0.90        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.69/0.90        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('simplify', [status(thm)], ['106'])).
% 0.69/0.90  thf('108', plain, (~ (v2_struct_0 @ sk_A)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('109', plain,
% 0.69/0.90      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.69/0.90        | (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1))))),
% 0.69/0.90      inference('clc', [status(thm)], ['107', '108'])).
% 0.69/0.90  thf('110', plain,
% 0.69/0.90      ((~ (r2_hidden @ sk_B @ (a_2_1_orders_2 @ sk_A @ (k1_tarski @ sk_C_1)))
% 0.69/0.90        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.69/0.90      inference('simpl_trail', [status(thm)], ['37', '85'])).
% 0.69/0.90  thf('111', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.69/0.90      inference('clc', [status(thm)], ['109', '110'])).
% 0.69/0.90  thf('112', plain,
% 0.69/0.90      (![X6 : $i]:
% 0.69/0.90         (~ (v1_xboole_0 @ (u1_struct_0 @ X6))
% 0.69/0.90          | ~ (l1_struct_0 @ X6)
% 0.69/0.90          | (v2_struct_0 @ X6))),
% 0.69/0.90      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.69/0.90  thf('113', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.69/0.90      inference('sup-', [status(thm)], ['111', '112'])).
% 0.69/0.90  thf('114', plain, ((l1_struct_0 @ sk_A)),
% 0.69/0.90      inference('sup-', [status(thm)], ['79', '80'])).
% 0.69/0.90  thf('115', plain, ((v2_struct_0 @ sk_A)),
% 0.69/0.90      inference('demod', [status(thm)], ['113', '114'])).
% 0.69/0.90  thf('116', plain, ($false), inference('demod', [status(thm)], ['0', '115'])).
% 0.69/0.90  
% 0.69/0.90  % SZS output end Refutation
% 0.69/0.90  
% 0.69/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
