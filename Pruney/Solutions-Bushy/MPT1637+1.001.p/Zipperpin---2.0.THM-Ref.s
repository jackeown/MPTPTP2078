%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1637+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.H2nWNJY7SP

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:53 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 707 expanded)
%              Number of leaves         :   28 ( 197 expanded)
%              Depth                    :   30
%              Number of atoms          : 1434 (9793 expanded)
%              Number of equality atoms :   38 ( 168 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_waybel_0_type,type,(
    k5_waybel_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(a_2_0_waybel_0_type,type,(
    a_2_0_waybel_0: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k3_waybel_0_type,type,(
    k3_waybel_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t17_waybel_0,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_hidden @ C @ ( k5_waybel_0 @ A @ B ) )
              <=> ( r1_orders_2 @ A @ C @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
               => ( ( r2_hidden @ C @ ( k5_waybel_0 @ A @ B ) )
                <=> ( r1_orders_2 @ A @ C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_waybel_0])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( ( k6_domain_1 @ X16 @ X17 )
        = ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('5',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ X7 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t14_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k3_waybel_0 @ A @ B )
            = ( a_2_0_waybel_0 @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( ( k3_waybel_0 @ X19 @ X18 )
        = ( a_2_0_waybel_0 @ X19 @ X18 ) )
      | ~ ( l1_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t14_waybel_0])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k3_waybel_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_waybel_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d17_waybel_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k5_waybel_0 @ A @ B )
            = ( k3_waybel_0 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ X1 ) )
      | ( ( k5_waybel_0 @ X1 @ X0 )
        = ( k3_waybel_0 @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) )
      | ~ ( l1_orders_2 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d17_waybel_0])).

thf('14',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k5_waybel_0 @ sk_A @ sk_B )
      = ( k3_waybel_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k5_waybel_0 @ sk_A @ sk_B )
      = ( k3_waybel_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k5_waybel_0 @ sk_A @ sk_B )
    = ( k3_waybel_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( ( k5_waybel_0 @ sk_A @ sk_B )
      = ( a_2_0_waybel_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['10','11','18'])).

thf('20',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( ( k5_waybel_0 @ sk_A @ sk_B )
      = ( a_2_0_waybel_0 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k5_waybel_0 @ sk_A @ sk_B )
      = ( a_2_0_waybel_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['5','21'])).

thf('23',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k5_waybel_0 @ sk_A @ sk_B )
      = ( a_2_0_waybel_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('25',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('26',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf(fraenkel_a_2_0_waybel_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v2_struct_0 @ B )
        & ( l1_orders_2 @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) )
     => ( ( r2_hidden @ A @ ( a_2_0_waybel_0 @ B @ C ) )
      <=> ? [D: $i] :
            ( ? [E: $i] :
                ( ( r2_hidden @ E @ C )
                & ( r1_orders_2 @ B @ D @ E )
                & ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) )
            & ( A = D )
            & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) )).

thf('28',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r2_hidden @ ( sk_E @ X12 @ X11 @ X13 ) @ X12 )
      | ~ ( r2_hidden @ X13 @ ( a_2_0_waybel_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_waybel_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_waybel_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_waybel_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) @ ( k1_tarski @ sk_B ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 ) @ ( k1_tarski @ sk_B ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['2','33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( ( r2_hidden @ ( sk_E @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 ) @ ( k1_tarski @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('37',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X5 @ X4 )
      | ( X5 = X2 )
      | ( X4
       != ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('38',plain,(
    ! [X2: $i,X5: $i] :
      ( ( X5 = X2 )
      | ~ ( r2_hidden @ X5 @ ( k1_tarski @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( ( sk_E @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 )
        = sk_B ) )
   <= ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ~ ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ~ ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k5_waybel_0 @ sk_A @ sk_B )
      = ( a_2_0_waybel_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('43',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_C_1 @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('47',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r2_hidden @ X13 @ ( a_2_0_waybel_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X11 ) )
      | ( X13 != X14 )
      | ~ ( r2_hidden @ X15 @ X12 )
      | ~ ( r1_orders_2 @ X11 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_waybel_0])).

thf('48',plain,(
    ! [X11: $i,X12: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r1_orders_2 @ X11 @ X14 @ X15 )
      | ~ ( r2_hidden @ X15 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X11 ) )
      | ( r2_hidden @ X14 @ ( a_2_0_waybel_0 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v2_struct_0 @ X11 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_0_waybel_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['46','48'])).

thf('50',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_0_waybel_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ sk_B ) )
      | ~ ( r1_orders_2 @ sk_A @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ sk_C_1 @ ( a_2_0_waybel_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( a_2_0_waybel_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','52'])).

thf('54',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( X3 != X2 )
      | ( r2_hidden @ X3 @ X4 )
      | ( X4
       != ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('55',plain,(
    ! [X2: $i] :
      ( r2_hidden @ X2 @ ( k1_tarski @ X2 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C_1 @ ( a_2_0_waybel_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['53','55'])).

thf('57',plain,
    ( ( ( r2_hidden @ sk_C_1 @ ( a_2_0_waybel_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['43','56'])).

thf('58',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_C_1 @ ( a_2_0_waybel_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(clc,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['42','59'])).

thf('61',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) )
   <= ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ~ ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
   <= ~ ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['40'])).

thf('63',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
      & ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('64',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('65',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
      & ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('67',plain,(
    ! [X9: $i] :
      ( ( l1_struct_0 @ X9 )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('68',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
      & ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['65','68'])).

thf('70',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
    | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['1'])).

thf('73',plain,(
    r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['41','71','72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_E @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 )
      = sk_B ) ),
    inference(simpl_trail,[status(thm)],['39','73'])).

thf('75',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('76',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k5_waybel_0 @ sk_A @ sk_B )
      = ( a_2_0_waybel_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('77',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('78',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( X13
        = ( sk_D @ X12 @ X11 @ X13 ) )
      | ~ ( r2_hidden @ X13 @ ( a_2_0_waybel_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_waybel_0])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_waybel_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( X0
        = ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_waybel_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( X0
        = ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( X0
        = ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['76','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( sk_C_1
        = ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['75','83'])).

thf('85',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ( sk_C_1
        = ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['41','71','72'])).

thf('88',plain,
    ( ( sk_C_1
      = ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['1'])).

thf('90',plain,(
    r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['41','71','72'])).

thf('91',plain,(
    r2_hidden @ sk_C_1 @ ( k5_waybel_0 @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k5_waybel_0 @ sk_A @ sk_B )
      = ( a_2_0_waybel_0 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('93',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('94',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r1_orders_2 @ X11 @ ( sk_D @ X12 @ X11 @ X13 ) @ ( sk_E @ X12 @ X11 @ X13 ) )
      | ~ ( r2_hidden @ X13 @ ( a_2_0_waybel_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_waybel_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_waybel_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) @ ( sk_E @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( a_2_0_waybel_0 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) @ ( sk_E @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) @ ( sk_E @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['92','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) @ ( sk_E @ ( k1_tarski @ sk_B ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k5_waybel_0 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 ) @ ( sk_E @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['91','99'])).

thf('101',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( r1_orders_2 @ sk_A @ ( sk_D @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 ) @ ( sk_E @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C_1 @ ( sk_E @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['88','102'])).

thf('104',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_C_1 @ ( sk_E @ ( k1_tarski @ sk_B ) @ sk_A @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['74','104'])).

thf('106',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B )
   <= ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(split,[status(esa)],['40'])).

thf('108',plain,(
    ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['41','71'])).

thf('109',plain,(
    ~ ( r1_orders_2 @ sk_A @ sk_C_1 @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['107','108'])).

thf('110',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('112',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['66','67'])).

thf('114',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['0','114'])).


%------------------------------------------------------------------------------
