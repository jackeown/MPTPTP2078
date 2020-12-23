%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B73OC6pxdu

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:56 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 763 expanded)
%              Number of leaves         :   29 ( 222 expanded)
%              Depth                    :   33
%              Number of atoms          : 1531 (13854 expanded)
%              Number of equality atoms :   32 ( 153 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(a_2_0_orders_2_type,type,(
    a_2_0_orders_2: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(t51_orders_2,conjecture,(
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
              <=> ( r2_hidden @ C @ ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) )).

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
                <=> ( r2_hidden @ C @ ( k1_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t51_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ X20 )
      | ( ( k6_domain_1 @ X20 @ X21 )
        = ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('4',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ X12 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(fraenkel_a_2_0_orders_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( v3_orders_2 @ B )
        & ( v4_orders_2 @ B )
        & ( v5_orders_2 @ B )
        & ( l1_orders_2 @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
     => ( ( r2_hidden @ A @ ( a_2_0_orders_2 @ B @ C ) )
      <=> ? [D: $i] :
            ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) )
               => ( ( r2_hidden @ E @ C )
                 => ( r2_orders_2 @ B @ E @ D ) ) )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i,X18: $i,X19: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r2_hidden @ X18 @ ( a_2_0_orders_2 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X15 ) )
      | ( X18 != X19 )
      | ( r2_hidden @ ( sk_E @ X19 @ X16 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('11',plain,(
    ! [X15: $i,X16: $i,X19: $i] :
      ( ( r2_hidden @ ( sk_E @ X19 @ X16 @ X15 ) @ X16 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X15 ) )
      | ( r2_hidden @ X19 @ ( a_2_0_orders_2 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v2_struct_0 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
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
      | ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['12','13','14','15','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_E @ sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_C_1 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
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
    | ( r2_hidden @ sk_C_1 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( ( sk_E @ sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('23',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d12_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_orders_2 @ A @ B )
            = ( a_2_0_orders_2 @ A @ B ) ) ) ) )).

thf('24',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k1_orders_2 @ X11 @ X10 )
        = ( a_2_0_orders_2 @ X11 @ X10 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d12_orders_2])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
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
    | ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','29'])).

thf('31',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( ~ ( r2_hidden @ sk_C_1 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['35'])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('40',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ( ( r2_hidden @ sk_C_1 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['39','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('44',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( X18
        = ( sk_D @ X16 @ X15 @ X18 ) )
      | ~ ( r2_hidden @ X18 @ ( a_2_0_orders_2 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( X0
        = ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) )
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
      | ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( X0
        = ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49'])).

thf('51',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( sk_C_1
        = ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,
    ( ( ( sk_C_1
        = ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( sk_C_1
        = ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
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
    ( ( ( r2_hidden @ sk_C_1 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['39','41'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('59',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ( r2_orders_2 @ X15 @ X17 @ ( sk_D @ X16 @ X15 @ X18 ) )
      | ~ ( r2_hidden @ X17 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( a_2_0_orders_2 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_B ) )
      | ( r2_orders_2 @ sk_A @ X1 @ ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) )
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
      | ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_B ) )
      | ( r2_orders_2 @ sk_A @ X1 @ ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['57','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
        | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['56','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['54','72'])).

thf('74',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) )
   <= ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['35'])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('77',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('78',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('80',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('81',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
      & ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['78','81'])).

thf('83',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['38','84'])).

thf('86',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['37','85'])).

thf('87',plain,
    ( ( ( sk_E @ sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_B )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['21','86'])).

thf('88',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( sk_E @ sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_B ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( sk_E @ sk_C_1 @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('92',plain,(
    ! [X15: $i,X16: $i,X18: $i,X19: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r2_hidden @ X18 @ ( a_2_0_orders_2 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X15 ) )
      | ( X18 != X19 )
      | ~ ( r2_orders_2 @ X15 @ ( sk_E @ X19 @ X16 @ X15 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('93',plain,(
    ! [X15: $i,X16: $i,X19: $i] :
      ( ~ ( r2_orders_2 @ X15 @ ( sk_E @ X19 @ X16 @ X15 ) @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X15 ) )
      | ( r2_hidden @ X19 @ ( a_2_0_orders_2 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v2_struct_0 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_E @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
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
      | ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_E @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['90','99'])).

thf('101',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['40'])).

thf('102',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C_1 )
    | ( r2_hidden @ sk_C_1 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['40'])).

thf('103',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['38','84','102'])).

thf('104',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['101','103'])).

thf('105',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['100','104','105'])).

thf('107',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['106'])).

thf('108',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['37','85'])).

thf('111',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['109','110'])).

thf('112',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
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
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.B73OC6pxdu
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.59/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.79  % Solved by: fo/fo7.sh
% 0.59/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.79  % done 463 iterations in 0.351s
% 0.59/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.79  % SZS output start Refutation
% 0.59/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.79  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.59/0.79  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.79  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.59/0.79  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.79  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.59/0.79  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.59/0.79  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.59/0.79  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.59/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.79  thf(a_2_0_orders_2_type, type, a_2_0_orders_2: $i > $i > $i).
% 0.59/0.79  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.59/0.79  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.59/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.79  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.59/0.79  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.59/0.79  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.59/0.79  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.59/0.79  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.59/0.79  thf(t51_orders_2, conjecture,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.59/0.79         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.59/0.79       ( ![B:$i]:
% 0.59/0.79         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.79           ( ![C:$i]:
% 0.59/0.79             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.79               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.59/0.79                 ( r2_hidden @
% 0.59/0.79                   C @ 
% 0.59/0.79                   ( k1_orders_2 @
% 0.59/0.79                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ) ))).
% 0.59/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.79    (~( ![A:$i]:
% 0.59/0.79        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.59/0.79            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.59/0.79          ( ![B:$i]:
% 0.59/0.79            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.79              ( ![C:$i]:
% 0.59/0.79                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.59/0.79                  ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.59/0.79                    ( r2_hidden @
% 0.59/0.79                      C @ 
% 0.59/0.79                      ( k1_orders_2 @
% 0.59/0.79                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ) ) )),
% 0.59/0.79    inference('cnf.neg', [status(esa)], [t51_orders_2])).
% 0.59/0.79  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('2', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(redefinition_k6_domain_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.59/0.79       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.59/0.79  thf('3', plain,
% 0.59/0.79      (![X20 : $i, X21 : $i]:
% 0.59/0.79         ((v1_xboole_0 @ X20)
% 0.59/0.79          | ~ (m1_subset_1 @ X21 @ X20)
% 0.59/0.79          | ((k6_domain_1 @ X20 @ X21) = (k1_tarski @ X21)))),
% 0.59/0.79      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.59/0.79  thf('4', plain,
% 0.59/0.79      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.59/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.79  thf('5', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf(dt_k6_domain_1, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.59/0.79       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.59/0.79  thf('6', plain,
% 0.59/0.79      (![X12 : $i, X13 : $i]:
% 0.59/0.79         ((v1_xboole_0 @ X12)
% 0.59/0.79          | ~ (m1_subset_1 @ X13 @ X12)
% 0.59/0.79          | (m1_subset_1 @ (k6_domain_1 @ X12 @ X13) @ (k1_zfmisc_1 @ X12)))),
% 0.59/0.79      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.59/0.79  thf('7', plain,
% 0.59/0.79      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.59/0.79         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf('8', plain,
% 0.59/0.79      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.59/0.79         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['4', '7'])).
% 0.59/0.79  thf('9', plain,
% 0.59/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.59/0.79           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.79      inference('simplify', [status(thm)], ['8'])).
% 0.59/0.79  thf(fraenkel_a_2_0_orders_2, axiom,
% 0.59/0.79    (![A:$i,B:$i,C:$i]:
% 0.59/0.79     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.59/0.79         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.59/0.79         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.59/0.79       ( ( r2_hidden @ A @ ( a_2_0_orders_2 @ B @ C ) ) <=>
% 0.59/0.79         ( ?[D:$i]:
% 0.59/0.79           ( ( ![E:$i]:
% 0.59/0.79               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.59/0.79                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ E @ D ) ) ) ) & 
% 0.59/0.79             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.59/0.79  thf('10', plain,
% 0.59/0.79      (![X15 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 0.59/0.79         (~ (l1_orders_2 @ X15)
% 0.59/0.79          | ~ (v5_orders_2 @ X15)
% 0.59/0.79          | ~ (v4_orders_2 @ X15)
% 0.59/0.79          | ~ (v3_orders_2 @ X15)
% 0.59/0.79          | (v2_struct_0 @ X15)
% 0.59/0.79          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.59/0.79          | (r2_hidden @ X18 @ (a_2_0_orders_2 @ X15 @ X16))
% 0.59/0.79          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X15))
% 0.59/0.79          | ((X18) != (X19))
% 0.59/0.79          | (r2_hidden @ (sk_E @ X19 @ X16 @ X15) @ X16))),
% 0.59/0.79      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.59/0.79  thf('11', plain,
% 0.59/0.79      (![X15 : $i, X16 : $i, X19 : $i]:
% 0.59/0.79         ((r2_hidden @ (sk_E @ X19 @ X16 @ X15) @ X16)
% 0.59/0.79          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X15))
% 0.59/0.79          | (r2_hidden @ X19 @ (a_2_0_orders_2 @ X15 @ X16))
% 0.59/0.79          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.59/0.79          | (v2_struct_0 @ X15)
% 0.59/0.79          | ~ (v3_orders_2 @ X15)
% 0.59/0.79          | ~ (v4_orders_2 @ X15)
% 0.59/0.79          | ~ (v5_orders_2 @ X15)
% 0.59/0.79          | ~ (l1_orders_2 @ X15))),
% 0.59/0.79      inference('simplify', [status(thm)], ['10'])).
% 0.59/0.79  thf('12', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79          | ~ (l1_orders_2 @ sk_A)
% 0.59/0.79          | ~ (v5_orders_2 @ sk_A)
% 0.59/0.79          | ~ (v4_orders_2 @ sk_A)
% 0.59/0.79          | ~ (v3_orders_2 @ sk_A)
% 0.59/0.79          | (v2_struct_0 @ sk_A)
% 0.59/0.79          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.79          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79          | (r2_hidden @ (sk_E @ X0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.59/0.79             (k1_tarski @ sk_B)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['9', '11'])).
% 0.59/0.79  thf('13', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('14', plain, ((v5_orders_2 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('15', plain, ((v4_orders_2 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('16', plain, ((v3_orders_2 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('17', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79          | (v2_struct_0 @ sk_A)
% 0.59/0.79          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.79          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79          | (r2_hidden @ (sk_E @ X0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.59/0.79             (k1_tarski @ sk_B)))),
% 0.59/0.79      inference('demod', [status(thm)], ['12', '13', '14', '15', '16'])).
% 0.59/0.79  thf('18', plain,
% 0.59/0.79      (((r2_hidden @ (sk_E @ sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.59/0.79         (k1_tarski @ sk_B))
% 0.59/0.79        | (r2_hidden @ sk_C_1 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.79        | (v2_struct_0 @ sk_A)
% 0.59/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['1', '17'])).
% 0.59/0.79  thf(d1_tarski, axiom,
% 0.59/0.79    (![A:$i,B:$i]:
% 0.59/0.79     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.59/0.79       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.59/0.79  thf('19', plain,
% 0.59/0.79      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.59/0.79         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.59/0.79      inference('cnf', [status(esa)], [d1_tarski])).
% 0.59/0.79  thf('20', plain,
% 0.59/0.79      (![X0 : $i, X3 : $i]:
% 0.59/0.79         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.59/0.79      inference('simplify', [status(thm)], ['19'])).
% 0.59/0.79  thf('21', plain,
% 0.59/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79        | (v2_struct_0 @ sk_A)
% 0.59/0.79        | (r2_hidden @ sk_C_1 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.79        | ((sk_E @ sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) = (sk_B)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['18', '20'])).
% 0.59/0.79  thf('22', plain,
% 0.59/0.79      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.59/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.79  thf('23', plain,
% 0.59/0.79      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.59/0.79         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.59/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('sup-', [status(thm)], ['5', '6'])).
% 0.59/0.79  thf(d12_orders_2, axiom,
% 0.59/0.79    (![A:$i]:
% 0.59/0.79     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.59/0.79         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.59/0.79       ( ![B:$i]:
% 0.59/0.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.59/0.79           ( ( k1_orders_2 @ A @ B ) = ( a_2_0_orders_2 @ A @ B ) ) ) ) ))).
% 0.59/0.79  thf('24', plain,
% 0.59/0.79      (![X10 : $i, X11 : $i]:
% 0.59/0.79         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.59/0.79          | ((k1_orders_2 @ X11 @ X10) = (a_2_0_orders_2 @ X11 @ X10))
% 0.59/0.79          | ~ (l1_orders_2 @ X11)
% 0.59/0.79          | ~ (v5_orders_2 @ X11)
% 0.59/0.79          | ~ (v4_orders_2 @ X11)
% 0.59/0.79          | ~ (v3_orders_2 @ X11)
% 0.59/0.79          | (v2_struct_0 @ X11))),
% 0.59/0.79      inference('cnf', [status(esa)], [d12_orders_2])).
% 0.59/0.79  thf('25', plain,
% 0.59/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79        | (v2_struct_0 @ sk_A)
% 0.59/0.79        | ~ (v3_orders_2 @ sk_A)
% 0.59/0.79        | ~ (v4_orders_2 @ sk_A)
% 0.59/0.79        | ~ (v5_orders_2 @ sk_A)
% 0.59/0.79        | ~ (l1_orders_2 @ sk_A)
% 0.59/0.79        | ((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.59/0.79            = (a_2_0_orders_2 @ sk_A @ 
% 0.59/0.79               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['23', '24'])).
% 0.59/0.79  thf('26', plain, ((v3_orders_2 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('27', plain, ((v4_orders_2 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('28', plain, ((v5_orders_2 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('29', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('30', plain,
% 0.59/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79        | (v2_struct_0 @ sk_A)
% 0.59/0.79        | ((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.59/0.79            = (a_2_0_orders_2 @ sk_A @ 
% 0.59/0.79               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.59/0.79      inference('demod', [status(thm)], ['25', '26', '27', '28', '29'])).
% 0.59/0.79  thf('31', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('32', plain,
% 0.59/0.79      ((((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.59/0.79          = (a_2_0_orders_2 @ sk_A @ 
% 0.59/0.79             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.59/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('clc', [status(thm)], ['30', '31'])).
% 0.59/0.79  thf('33', plain,
% 0.59/0.79      ((((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.59/0.79          = (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.79      inference('sup+', [status(thm)], ['22', '32'])).
% 0.59/0.79  thf('34', plain,
% 0.59/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79        | ((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.59/0.79            = (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.59/0.79      inference('simplify', [status(thm)], ['33'])).
% 0.59/0.79  thf('35', plain,
% 0.59/0.79      ((~ (r2_hidden @ sk_C_1 @ 
% 0.59/0.79           (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.59/0.79        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('36', plain,
% 0.59/0.79      ((~ (r2_hidden @ sk_C_1 @ 
% 0.59/0.79           (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.59/0.79         <= (~
% 0.59/0.79             ((r2_hidden @ sk_C_1 @ 
% 0.59/0.79               (k1_orders_2 @ sk_A @ 
% 0.59/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.79      inference('split', [status(esa)], ['35'])).
% 0.59/0.79  thf('37', plain,
% 0.59/0.79      (((~ (r2_hidden @ sk_C_1 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.79         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.79         <= (~
% 0.59/0.79             ((r2_hidden @ sk_C_1 @ 
% 0.59/0.79               (k1_orders_2 @ sk_A @ 
% 0.59/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['34', '36'])).
% 0.59/0.79  thf('38', plain,
% 0.59/0.79      (~
% 0.59/0.79       ((r2_hidden @ sk_C_1 @ 
% 0.59/0.79         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))) | 
% 0.59/0.79       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 0.59/0.79      inference('split', [status(esa)], ['35'])).
% 0.59/0.79  thf('39', plain,
% 0.59/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79        | ((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.59/0.79            = (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.59/0.79      inference('simplify', [status(thm)], ['33'])).
% 0.59/0.79  thf('40', plain,
% 0.59/0.79      (((r2_hidden @ sk_C_1 @ 
% 0.59/0.79         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.59/0.79        | (r2_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('41', plain,
% 0.59/0.79      (((r2_hidden @ sk_C_1 @ 
% 0.59/0.79         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.59/0.79         <= (((r2_hidden @ sk_C_1 @ 
% 0.59/0.79               (k1_orders_2 @ sk_A @ 
% 0.59/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.79      inference('split', [status(esa)], ['40'])).
% 0.59/0.79  thf('42', plain,
% 0.59/0.79      ((((r2_hidden @ sk_C_1 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.79         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.79         <= (((r2_hidden @ sk_C_1 @ 
% 0.59/0.79               (k1_orders_2 @ sk_A @ 
% 0.59/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.79      inference('sup+', [status(thm)], ['39', '41'])).
% 0.59/0.79  thf('43', plain,
% 0.59/0.79      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.59/0.79           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.79      inference('simplify', [status(thm)], ['8'])).
% 0.59/0.79  thf('44', plain,
% 0.59/0.79      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.59/0.79         (~ (l1_orders_2 @ X15)
% 0.59/0.79          | ~ (v5_orders_2 @ X15)
% 0.59/0.79          | ~ (v4_orders_2 @ X15)
% 0.59/0.79          | ~ (v3_orders_2 @ X15)
% 0.59/0.79          | (v2_struct_0 @ X15)
% 0.59/0.79          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.59/0.79          | ((X18) = (sk_D @ X16 @ X15 @ X18))
% 0.59/0.79          | ~ (r2_hidden @ X18 @ (a_2_0_orders_2 @ X15 @ X16)))),
% 0.59/0.79      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.59/0.79  thf('45', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79          | ~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.79          | ((X0) = (sk_D @ (k1_tarski @ sk_B) @ sk_A @ X0))
% 0.59/0.79          | (v2_struct_0 @ sk_A)
% 0.59/0.79          | ~ (v3_orders_2 @ sk_A)
% 0.59/0.79          | ~ (v4_orders_2 @ sk_A)
% 0.59/0.79          | ~ (v5_orders_2 @ sk_A)
% 0.59/0.79          | ~ (l1_orders_2 @ sk_A))),
% 0.59/0.79      inference('sup-', [status(thm)], ['43', '44'])).
% 0.59/0.79  thf('46', plain, ((v3_orders_2 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('47', plain, ((v4_orders_2 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('48', plain, ((v5_orders_2 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('49', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('50', plain,
% 0.59/0.79      (![X0 : $i]:
% 0.59/0.79         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79          | ~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.79          | ((X0) = (sk_D @ (k1_tarski @ sk_B) @ sk_A @ X0))
% 0.59/0.79          | (v2_struct_0 @ sk_A))),
% 0.59/0.79      inference('demod', [status(thm)], ['45', '46', '47', '48', '49'])).
% 0.59/0.79  thf('51', plain,
% 0.59/0.79      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79         | (v2_struct_0 @ sk_A)
% 0.59/0.79         | ((sk_C_1) = (sk_D @ (k1_tarski @ sk_B) @ sk_A @ sk_C_1))
% 0.59/0.79         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.79         <= (((r2_hidden @ sk_C_1 @ 
% 0.59/0.79               (k1_orders_2 @ sk_A @ 
% 0.59/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.79      inference('sup-', [status(thm)], ['42', '50'])).
% 0.59/0.79  thf('52', plain,
% 0.59/0.79      (((((sk_C_1) = (sk_D @ (k1_tarski @ sk_B) @ sk_A @ sk_C_1))
% 0.59/0.79         | (v2_struct_0 @ sk_A)
% 0.59/0.79         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.79         <= (((r2_hidden @ sk_C_1 @ 
% 0.59/0.79               (k1_orders_2 @ sk_A @ 
% 0.59/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.79      inference('simplify', [status(thm)], ['51'])).
% 0.59/0.79  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.79  thf('54', plain,
% 0.59/0.79      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.79         | ((sk_C_1) = (sk_D @ (k1_tarski @ sk_B) @ sk_A @ sk_C_1))))
% 0.59/0.79         <= (((r2_hidden @ sk_C_1 @ 
% 0.59/0.79               (k1_orders_2 @ sk_A @ 
% 0.59/0.79                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.79      inference('clc', [status(thm)], ['52', '53'])).
% 0.59/0.79  thf('55', plain,
% 0.59/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.79         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.59/0.79      inference('cnf', [status(esa)], [d1_tarski])).
% 0.59/0.79  thf('56', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.59/0.79      inference('simplify', [status(thm)], ['55'])).
% 0.59/0.79  thf('57', plain,
% 0.59/0.79      ((((r2_hidden @ sk_C_1 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.80         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.80         <= (((r2_hidden @ sk_C_1 @ 
% 0.59/0.80               (k1_orders_2 @ sk_A @ 
% 0.59/0.80                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.80      inference('sup+', [status(thm)], ['39', '41'])).
% 0.59/0.80  thf('58', plain,
% 0.59/0.80      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.80        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.59/0.80           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.80      inference('simplify', [status(thm)], ['8'])).
% 0.59/0.80  thf('59', plain,
% 0.59/0.80      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.80         (~ (l1_orders_2 @ X15)
% 0.59/0.80          | ~ (v5_orders_2 @ X15)
% 0.59/0.80          | ~ (v4_orders_2 @ X15)
% 0.59/0.80          | ~ (v3_orders_2 @ X15)
% 0.59/0.80          | (v2_struct_0 @ X15)
% 0.59/0.80          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.59/0.80          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.59/0.80          | (r2_orders_2 @ X15 @ X17 @ (sk_D @ X16 @ X15 @ X18))
% 0.59/0.80          | ~ (r2_hidden @ X17 @ X16)
% 0.59/0.80          | ~ (r2_hidden @ X18 @ (a_2_0_orders_2 @ X15 @ X16)))),
% 0.59/0.80      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.59/0.80  thf('60', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.80          | ~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.80          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_B))
% 0.59/0.80          | (r2_orders_2 @ sk_A @ X1 @ (sk_D @ (k1_tarski @ sk_B) @ sk_A @ X0))
% 0.59/0.80          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.59/0.80          | (v2_struct_0 @ sk_A)
% 0.59/0.80          | ~ (v3_orders_2 @ sk_A)
% 0.59/0.80          | ~ (v4_orders_2 @ sk_A)
% 0.59/0.80          | ~ (v5_orders_2 @ sk_A)
% 0.59/0.80          | ~ (l1_orders_2 @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['58', '59'])).
% 0.59/0.80  thf('61', plain, ((v3_orders_2 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('62', plain, ((v4_orders_2 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('63', plain, ((v5_orders_2 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('64', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('65', plain,
% 0.59/0.80      (![X0 : $i, X1 : $i]:
% 0.59/0.80         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.80          | ~ (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.80          | ~ (r2_hidden @ X1 @ (k1_tarski @ sk_B))
% 0.59/0.80          | (r2_orders_2 @ sk_A @ X1 @ (sk_D @ (k1_tarski @ sk_B) @ sk_A @ X0))
% 0.59/0.80          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.59/0.80          | (v2_struct_0 @ sk_A))),
% 0.59/0.80      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 0.59/0.80  thf('66', plain,
% 0.59/0.80      ((![X0 : $i]:
% 0.59/0.80          ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.80           | (v2_struct_0 @ sk_A)
% 0.59/0.80           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.80           | (r2_orders_2 @ sk_A @ X0 @ 
% 0.59/0.80              (sk_D @ (k1_tarski @ sk_B) @ sk_A @ sk_C_1))
% 0.59/0.80           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.59/0.80           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.80         <= (((r2_hidden @ sk_C_1 @ 
% 0.59/0.80               (k1_orders_2 @ sk_A @ 
% 0.59/0.80                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.80      inference('sup-', [status(thm)], ['57', '65'])).
% 0.59/0.80  thf('67', plain,
% 0.59/0.80      ((![X0 : $i]:
% 0.59/0.80          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.59/0.80           | (r2_orders_2 @ sk_A @ X0 @ 
% 0.59/0.80              (sk_D @ (k1_tarski @ sk_B) @ sk_A @ sk_C_1))
% 0.59/0.80           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.80           | (v2_struct_0 @ sk_A)
% 0.59/0.80           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.80         <= (((r2_hidden @ sk_C_1 @ 
% 0.59/0.80               (k1_orders_2 @ sk_A @ 
% 0.59/0.80                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.80      inference('simplify', [status(thm)], ['66'])).
% 0.59/0.80  thf('68', plain,
% 0.59/0.80      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.80         | (v2_struct_0 @ sk_A)
% 0.59/0.80         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.59/0.80         | (r2_orders_2 @ sk_A @ sk_B @ 
% 0.59/0.80            (sk_D @ (k1_tarski @ sk_B) @ sk_A @ sk_C_1))))
% 0.59/0.80         <= (((r2_hidden @ sk_C_1 @ 
% 0.59/0.80               (k1_orders_2 @ sk_A @ 
% 0.59/0.80                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.80      inference('sup-', [status(thm)], ['56', '67'])).
% 0.59/0.80  thf('69', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('70', plain,
% 0.59/0.80      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.80         | (v2_struct_0 @ sk_A)
% 0.59/0.80         | (r2_orders_2 @ sk_A @ sk_B @ 
% 0.59/0.80            (sk_D @ (k1_tarski @ sk_B) @ sk_A @ sk_C_1))))
% 0.59/0.80         <= (((r2_hidden @ sk_C_1 @ 
% 0.59/0.80               (k1_orders_2 @ sk_A @ 
% 0.59/0.80                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.80      inference('demod', [status(thm)], ['68', '69'])).
% 0.59/0.80  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('72', plain,
% 0.59/0.80      ((((r2_orders_2 @ sk_A @ sk_B @ 
% 0.59/0.80          (sk_D @ (k1_tarski @ sk_B) @ sk_A @ sk_C_1))
% 0.59/0.80         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.80         <= (((r2_hidden @ sk_C_1 @ 
% 0.59/0.80               (k1_orders_2 @ sk_A @ 
% 0.59/0.80                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.80      inference('clc', [status(thm)], ['70', '71'])).
% 0.59/0.80  thf('73', plain,
% 0.59/0.80      ((((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)
% 0.59/0.80         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.80         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.59/0.80         <= (((r2_hidden @ sk_C_1 @ 
% 0.59/0.80               (k1_orders_2 @ sk_A @ 
% 0.59/0.80                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.80      inference('sup+', [status(thm)], ['54', '72'])).
% 0.59/0.80  thf('74', plain,
% 0.59/0.80      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.80         | (r2_orders_2 @ sk_A @ sk_B @ sk_C_1)))
% 0.59/0.80         <= (((r2_hidden @ sk_C_1 @ 
% 0.59/0.80               (k1_orders_2 @ sk_A @ 
% 0.59/0.80                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.80      inference('simplify', [status(thm)], ['73'])).
% 0.59/0.80  thf('75', plain,
% 0.59/0.80      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C_1))
% 0.59/0.80         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)))),
% 0.59/0.80      inference('split', [status(esa)], ['35'])).
% 0.59/0.80  thf('76', plain,
% 0.59/0.80      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.59/0.80         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.59/0.80             ((r2_hidden @ sk_C_1 @ 
% 0.59/0.80               (k1_orders_2 @ sk_A @ 
% 0.59/0.80                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.80      inference('sup-', [status(thm)], ['74', '75'])).
% 0.59/0.80  thf(fc2_struct_0, axiom,
% 0.59/0.80    (![A:$i]:
% 0.59/0.80     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.59/0.80       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.59/0.80  thf('77', plain,
% 0.59/0.80      (![X9 : $i]:
% 0.59/0.80         (~ (v1_xboole_0 @ (u1_struct_0 @ X9))
% 0.59/0.80          | ~ (l1_struct_0 @ X9)
% 0.59/0.80          | (v2_struct_0 @ X9))),
% 0.59/0.80      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.59/0.80  thf('78', plain,
% 0.59/0.80      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.59/0.80         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.59/0.80             ((r2_hidden @ sk_C_1 @ 
% 0.59/0.80               (k1_orders_2 @ sk_A @ 
% 0.59/0.80                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.80      inference('sup-', [status(thm)], ['76', '77'])).
% 0.59/0.80  thf('79', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf(dt_l1_orders_2, axiom,
% 0.59/0.80    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.59/0.80  thf('80', plain,
% 0.59/0.80      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_orders_2 @ X14))),
% 0.59/0.80      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.59/0.80  thf('81', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.80      inference('sup-', [status(thm)], ['79', '80'])).
% 0.59/0.80  thf('82', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_A))
% 0.59/0.80         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) & 
% 0.59/0.80             ((r2_hidden @ sk_C_1 @ 
% 0.59/0.80               (k1_orders_2 @ sk_A @ 
% 0.59/0.80                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.59/0.80      inference('demod', [status(thm)], ['78', '81'])).
% 0.59/0.80  thf('83', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('84', plain,
% 0.59/0.80      (((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.59/0.80       ~
% 0.59/0.80       ((r2_hidden @ sk_C_1 @ 
% 0.59/0.80         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.59/0.80      inference('sup-', [status(thm)], ['82', '83'])).
% 0.59/0.80  thf('85', plain,
% 0.59/0.80      (~
% 0.59/0.80       ((r2_hidden @ sk_C_1 @ 
% 0.59/0.80         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.59/0.80      inference('sat_resolution*', [status(thm)], ['38', '84'])).
% 0.59/0.80  thf('86', plain,
% 0.59/0.80      ((~ (r2_hidden @ sk_C_1 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.80        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.80      inference('simpl_trail', [status(thm)], ['37', '85'])).
% 0.59/0.80  thf('87', plain,
% 0.59/0.80      ((((sk_E @ sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) = (sk_B))
% 0.59/0.80        | (v2_struct_0 @ sk_A)
% 0.59/0.80        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.80        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['21', '86'])).
% 0.59/0.80  thf('88', plain,
% 0.59/0.80      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.80        | (v2_struct_0 @ sk_A)
% 0.59/0.80        | ((sk_E @ sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) = (sk_B)))),
% 0.59/0.80      inference('simplify', [status(thm)], ['87'])).
% 0.59/0.80  thf('89', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('90', plain,
% 0.59/0.80      ((((sk_E @ sk_C_1 @ (k1_tarski @ sk_B) @ sk_A) = (sk_B))
% 0.59/0.80        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.80      inference('clc', [status(thm)], ['88', '89'])).
% 0.59/0.80  thf('91', plain,
% 0.59/0.80      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.80        | (m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.59/0.80           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.59/0.80      inference('simplify', [status(thm)], ['8'])).
% 0.59/0.80  thf('92', plain,
% 0.59/0.80      (![X15 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 0.59/0.80         (~ (l1_orders_2 @ X15)
% 0.59/0.80          | ~ (v5_orders_2 @ X15)
% 0.59/0.80          | ~ (v4_orders_2 @ X15)
% 0.59/0.80          | ~ (v3_orders_2 @ X15)
% 0.59/0.80          | (v2_struct_0 @ X15)
% 0.59/0.80          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.59/0.80          | (r2_hidden @ X18 @ (a_2_0_orders_2 @ X15 @ X16))
% 0.59/0.80          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X15))
% 0.59/0.80          | ((X18) != (X19))
% 0.59/0.80          | ~ (r2_orders_2 @ X15 @ (sk_E @ X19 @ X16 @ X15) @ X19))),
% 0.59/0.80      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.59/0.80  thf('93', plain,
% 0.59/0.80      (![X15 : $i, X16 : $i, X19 : $i]:
% 0.59/0.80         (~ (r2_orders_2 @ X15 @ (sk_E @ X19 @ X16 @ X15) @ X19)
% 0.59/0.80          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X15))
% 0.59/0.80          | (r2_hidden @ X19 @ (a_2_0_orders_2 @ X15 @ X16))
% 0.59/0.80          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.59/0.80          | (v2_struct_0 @ X15)
% 0.59/0.80          | ~ (v3_orders_2 @ X15)
% 0.59/0.80          | ~ (v4_orders_2 @ X15)
% 0.59/0.80          | ~ (v5_orders_2 @ X15)
% 0.59/0.80          | ~ (l1_orders_2 @ X15))),
% 0.59/0.80      inference('simplify', [status(thm)], ['92'])).
% 0.59/0.80  thf('94', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.80          | ~ (l1_orders_2 @ sk_A)
% 0.59/0.80          | ~ (v5_orders_2 @ sk_A)
% 0.59/0.80          | ~ (v4_orders_2 @ sk_A)
% 0.59/0.80          | ~ (v3_orders_2 @ sk_A)
% 0.59/0.80          | (v2_struct_0 @ sk_A)
% 0.59/0.80          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.80          | ~ (r2_orders_2 @ sk_A @ (sk_E @ X0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.59/0.80               X0))),
% 0.59/0.80      inference('sup-', [status(thm)], ['91', '93'])).
% 0.59/0.80  thf('95', plain, ((l1_orders_2 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('96', plain, ((v5_orders_2 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('97', plain, ((v4_orders_2 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('98', plain, ((v3_orders_2 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('99', plain,
% 0.59/0.80      (![X0 : $i]:
% 0.59/0.80         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.80          | (v2_struct_0 @ sk_A)
% 0.59/0.80          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.80          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.59/0.80          | ~ (r2_orders_2 @ sk_A @ (sk_E @ X0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.59/0.80               X0))),
% 0.59/0.80      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 0.59/0.80  thf('100', plain,
% 0.59/0.80      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C_1)
% 0.59/0.80        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.80        | ~ (m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))
% 0.59/0.80        | (r2_hidden @ sk_C_1 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.80        | (v2_struct_0 @ sk_A)
% 0.59/0.80        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.80      inference('sup-', [status(thm)], ['90', '99'])).
% 0.59/0.80  thf('101', plain,
% 0.59/0.80      (((r2_orders_2 @ sk_A @ sk_B @ sk_C_1))
% 0.59/0.80         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)))),
% 0.59/0.80      inference('split', [status(esa)], ['40'])).
% 0.59/0.80  thf('102', plain,
% 0.59/0.80      (((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)) | 
% 0.59/0.80       ((r2_hidden @ sk_C_1 @ 
% 0.59/0.80         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.59/0.80      inference('split', [status(esa)], ['40'])).
% 0.59/0.80  thf('103', plain, (((r2_orders_2 @ sk_A @ sk_B @ sk_C_1))),
% 0.59/0.80      inference('sat_resolution*', [status(thm)], ['38', '84', '102'])).
% 0.59/0.80  thf('104', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C_1)),
% 0.59/0.80      inference('simpl_trail', [status(thm)], ['101', '103'])).
% 0.59/0.80  thf('105', plain, ((m1_subset_1 @ sk_C_1 @ (u1_struct_0 @ sk_A))),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('106', plain,
% 0.59/0.80      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.80        | (r2_hidden @ sk_C_1 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.80        | (v2_struct_0 @ sk_A)
% 0.59/0.80        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.80      inference('demod', [status(thm)], ['100', '104', '105'])).
% 0.59/0.80  thf('107', plain,
% 0.59/0.80      (((v2_struct_0 @ sk_A)
% 0.59/0.80        | (r2_hidden @ sk_C_1 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.80        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.80      inference('simplify', [status(thm)], ['106'])).
% 0.59/0.80  thf('108', plain, (~ (v2_struct_0 @ sk_A)),
% 0.59/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.80  thf('109', plain,
% 0.59/0.80      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.59/0.80        | (r2_hidden @ sk_C_1 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.59/0.80      inference('clc', [status(thm)], ['107', '108'])).
% 0.59/0.80  thf('110', plain,
% 0.59/0.80      ((~ (r2_hidden @ sk_C_1 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.59/0.80        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.59/0.80      inference('simpl_trail', [status(thm)], ['37', '85'])).
% 0.59/0.80  thf('111', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.59/0.80      inference('clc', [status(thm)], ['109', '110'])).
% 0.59/0.80  thf('112', plain,
% 0.59/0.80      (![X9 : $i]:
% 0.59/0.80         (~ (v1_xboole_0 @ (u1_struct_0 @ X9))
% 0.59/0.80          | ~ (l1_struct_0 @ X9)
% 0.59/0.80          | (v2_struct_0 @ X9))),
% 0.59/0.80      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.59/0.80  thf('113', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.59/0.80      inference('sup-', [status(thm)], ['111', '112'])).
% 0.59/0.80  thf('114', plain, ((l1_struct_0 @ sk_A)),
% 0.59/0.80      inference('sup-', [status(thm)], ['79', '80'])).
% 0.59/0.80  thf('115', plain, ((v2_struct_0 @ sk_A)),
% 0.59/0.80      inference('demod', [status(thm)], ['113', '114'])).
% 0.59/0.80  thf('116', plain, ($false), inference('demod', [status(thm)], ['0', '115'])).
% 0.59/0.80  
% 0.59/0.80  % SZS output end Refutation
% 0.59/0.80  
% 0.59/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
