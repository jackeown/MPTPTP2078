%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8xufjTIlPQ

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:57 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 859 expanded)
%              Number of leaves         :   32 ( 258 expanded)
%              Depth                    :   35
%              Number of atoms          : 1636 (16055 expanded)
%              Number of equality atoms :   41 ( 122 expanded)
%              Maximal formula depth    :   20 (   6 average)

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

thf(a_2_0_orders_2_type,type,(
    a_2_0_orders_2: $i > $i > $i )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

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
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( ( k6_domain_1 @ X16 @ X17 )
        = ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
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

thf('7',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ X19 ) @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ~ ( l1_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t35_orders_2])).

thf('8',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

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

thf('14',plain,(
    ! [X11: $i,X12: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r2_hidden @ X14 @ ( a_2_0_orders_2 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X11 ) )
      | ( X14 != X15 )
      | ( r2_hidden @ ( sk_E @ X15 @ X12 @ X11 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('15',plain,(
    ! [X11: $i,X12: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_E @ X15 @ X12 @ X11 ) @ X12 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X11 ) )
      | ( r2_hidden @ X15 @ ( a_2_0_orders_2 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v2_struct_0 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
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
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

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

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ( ( k1_orders_2 @ X9 @ X8 )
        = ( a_2_0_orders_2 @ X9 @ X8 ) )
      | ~ ( l1_orders_2 @ X9 )
      | ~ ( v5_orders_2 @ X9 )
      | ~ ( v4_orders_2 @ X9 )
      | ~ ( v3_orders_2 @ X9 )
      | ( v2_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d12_orders_2])).

thf('23',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['23','24','25','26','27'])).

thf('29',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_hidden @ ( sk_E @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['16','17','18','19','20','30'])).

thf('32',plain,
    ( ( r2_hidden @ ( sk_E @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['5','31'])).

thf('33',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['33'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('36',plain,(
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

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('38',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('41',plain,
    ( ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
    | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['41'])).

thf('43',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X11 ) )
      | ( r2_orders_2 @ X11 @ X13 @ ( sk_D_1 @ X12 @ X11 @ X14 ) )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( a_2_0_orders_2 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( r2_hidden @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_orders_2 @ sk_A @ X1 @ ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('47',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ~ ( r2_hidden @ X1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      | ( r2_orders_2 @ sk_A @ X1 @ ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A @ X0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47','48','49','50'])).

thf('52',plain,
    ( ! [X0: $i] :
        ( ( v2_struct_0 @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A @ sk_C ) )
        | ~ ( r2_hidden @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['42','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ X0 @ ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A @ sk_C ) )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['40','52'])).

thf('54',plain,
    ( ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['41'])).

thf('55',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('56',plain,(
    ! [X11: $i,X12: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( X14
        = ( sk_D_1 @ X12 @ X11 @ X14 ) )
      | ~ ( r2_hidden @ X14 @ ( a_2_0_orders_2 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('59',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
      | ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A @ X0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['57','58','59','60','61','62'])).

thf('64',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A @ X0 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_C
      = ( sk_D_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['54','65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
        | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
        | ( r2_orders_2 @ sk_A @ X0 @ sk_C )
        | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
        | ( v2_struct_0 @ sk_A ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['53','66'])).

thf('68',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['39','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) )
   <= ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['33'])).

thf('74',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('75',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('76',plain,
    ( ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ sk_A ) )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('78',plain,(
    ! [X10: $i] :
      ( ( l1_struct_0 @ X10 )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('79',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
   <= ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
      & ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['76','79'])).

thf('81',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['35','82'])).

thf('84',plain,(
    ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(simpl_trail,[status(thm)],['34','83'])).

thf('85',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ ( sk_E @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['32','84'])).

thf('86',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    r2_hidden @ ( sk_E @ sk_C @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( r2_hidden @ ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['4','87'])).

thf('89',plain,
    ( ( r2_hidden @ ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','88'])).

thf('90',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('92',plain,(
    ! [X0: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ( X4 = X3 )
      | ( X4 = X0 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('93',plain,(
    ! [X0: $i,X3: $i,X4: $i] :
      ( ( X4 = X0 )
      | ( X4 = X3 )
      | ~ ( r2_hidden @ X4 @ ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['91','93'])).

thf('95',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( sk_E @ sk_C @ ( k1_tarski @ sk_B ) @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['90','95'])).

thf('97',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('98',plain,(
    m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('99',plain,
    ( ( m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X11: $i,X12: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( r2_hidden @ X14 @ ( a_2_0_orders_2 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X11 ) )
      | ( X14 != X15 )
      | ~ ( r2_orders_2 @ X11 @ ( sk_E @ X15 @ X12 @ X11 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('101',plain,(
    ! [X11: $i,X12: $i,X15: $i] :
      ( ~ ( r2_orders_2 @ X11 @ ( sk_E @ X15 @ X12 @ X11 ) @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X11 ) )
      | ( r2_hidden @ X15 @ ( a_2_0_orders_2 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( v2_struct_0 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,(
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
    inference('sup-',[status(thm)],['99','101'])).

thf('103',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
      | ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ X0 @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( u1_struct_0 @ sk_A ) )
      | ~ ( r2_orders_2 @ sk_A @ ( sk_E @ X0 @ ( k1_tarski @ sk_B ) @ sk_A ) @ X0 ) ) ),
    inference(demod,[status(thm)],['102','103','104','105','106'])).

thf('108',plain,
    ( ~ ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['96','107'])).

thf('109',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
   <= ( r2_orders_2 @ sk_A @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['41'])).

thf('110',plain,
    ( ( r2_orders_2 @ sk_A @ sk_B @ sk_C )
    | ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['41'])).

thf('111',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['35','82','110'])).

thf('112',plain,(
    r2_orders_2 @ sk_A @ sk_B @ sk_C ),
    inference(simpl_trail,[status(thm)],['109','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['108','112','113'])).

thf('115',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('119',plain,
    ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
    = ( a_2_0_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('120',plain,
    ( ( ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) )
      = ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,
    ( ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference(split,[status(esa)],['33'])).

thf('122',plain,
    ( ( ~ ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
      | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) )
   <= ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( r2_hidden @ sk_C @ ( k1_orders_2 @ sk_A @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) ) ) ),
    inference('sat_resolution*',[status(thm)],['35','82'])).

thf('124',plain,
    ( ~ ( r2_hidden @ sk_C @ ( a_2_0_orders_2 @ sk_A @ ( k1_tarski @ sk_B ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['122','123'])).

thf('125',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['117','124'])).

thf('126',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('127',plain,
    ( ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['77','78'])).

thf('129',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    $false ),
    inference(demod,[status(thm)],['0','129'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8xufjTIlPQ
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:04:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.45/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.68  % Solved by: fo/fo7.sh
% 0.45/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.68  % done 382 iterations in 0.230s
% 0.45/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.68  % SZS output start Refutation
% 0.45/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.68  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.68  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.45/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.68  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.45/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.68  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.45/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.45/0.68  thf(v6_orders_2_type, type, v6_orders_2: $i > $i > $o).
% 0.45/0.68  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.45/0.68  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.45/0.68  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.68  thf(a_2_0_orders_2_type, type, a_2_0_orders_2: $i > $i > $i).
% 0.45/0.68  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 0.45/0.68  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.45/0.68  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.45/0.68  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.45/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.68  thf(t51_orders_2, conjecture,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.45/0.68         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.68           ( ![C:$i]:
% 0.45/0.68             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.68               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.45/0.68                 ( r2_hidden @
% 0.45/0.68                   C @ 
% 0.45/0.68                   ( k1_orders_2 @
% 0.45/0.68                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ) ))).
% 0.45/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.68    (~( ![A:$i]:
% 0.45/0.68        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.45/0.68            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.45/0.68          ( ![B:$i]:
% 0.45/0.68            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.68              ( ![C:$i]:
% 0.45/0.68                ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.68                  ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.45/0.68                    ( r2_hidden @
% 0.45/0.68                      C @ 
% 0.45/0.68                      ( k1_orders_2 @
% 0.45/0.68                        A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ) ) ) )),
% 0.45/0.68    inference('cnf.neg', [status(esa)], [t51_orders_2])).
% 0.45/0.68  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(redefinition_k6_domain_1, axiom,
% 0.45/0.68    (![A:$i,B:$i]:
% 0.45/0.68     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.45/0.68       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.45/0.68  thf('2', plain,
% 0.45/0.68      (![X16 : $i, X17 : $i]:
% 0.45/0.68         ((v1_xboole_0 @ X16)
% 0.45/0.68          | ~ (m1_subset_1 @ X17 @ X16)
% 0.45/0.68          | ((k6_domain_1 @ X16 @ X17) = (k1_tarski @ X17)))),
% 0.45/0.68      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.45/0.68  thf('3', plain,
% 0.45/0.68      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.68  thf('4', plain,
% 0.45/0.68      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.68  thf('5', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('6', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(t35_orders_2, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.68           ( ( v6_orders_2 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) & 
% 0.45/0.68             ( m1_subset_1 @
% 0.45/0.68               ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ 
% 0.45/0.68               ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) ) ) ))).
% 0.45/0.68  thf('7', plain,
% 0.45/0.68      (![X18 : $i, X19 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 0.45/0.68          | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ X19) @ X18) @ 
% 0.45/0.68             (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.45/0.68          | ~ (l1_orders_2 @ X19)
% 0.45/0.68          | ~ (v3_orders_2 @ X19)
% 0.45/0.68          | (v2_struct_0 @ X19))),
% 0.45/0.68      inference('cnf', [status(esa)], [t35_orders_2])).
% 0.45/0.68  thf('8', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | ~ (v3_orders_2 @ sk_A)
% 0.45/0.68        | ~ (l1_orders_2 @ sk_A)
% 0.45/0.68        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.45/0.68           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.68  thf('9', plain, ((v3_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('10', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('11', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | (m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.45/0.68           (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 0.45/0.68      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.45/0.68  thf('12', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('13', plain,
% 0.45/0.68      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.45/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('clc', [status(thm)], ['11', '12'])).
% 0.45/0.68  thf(fraenkel_a_2_0_orders_2, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.45/0.68         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.45/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.45/0.68       ( ( r2_hidden @ A @ ( a_2_0_orders_2 @ B @ C ) ) <=>
% 0.45/0.68         ( ?[D:$i]:
% 0.45/0.68           ( ( ![E:$i]:
% 0.45/0.68               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.45/0.68                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ E @ D ) ) ) ) & 
% 0.45/0.68             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.45/0.68  thf('14', plain,
% 0.45/0.68      (![X11 : $i, X12 : $i, X14 : $i, X15 : $i]:
% 0.45/0.68         (~ (l1_orders_2 @ X11)
% 0.45/0.68          | ~ (v5_orders_2 @ X11)
% 0.45/0.68          | ~ (v4_orders_2 @ X11)
% 0.45/0.68          | ~ (v3_orders_2 @ X11)
% 0.45/0.68          | (v2_struct_0 @ X11)
% 0.45/0.68          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.45/0.68          | (r2_hidden @ X14 @ (a_2_0_orders_2 @ X11 @ X12))
% 0.45/0.68          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X11))
% 0.45/0.68          | ((X14) != (X15))
% 0.45/0.68          | (r2_hidden @ (sk_E @ X15 @ X12 @ X11) @ X12))),
% 0.45/0.68      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.45/0.68  thf('15', plain,
% 0.45/0.68      (![X11 : $i, X12 : $i, X15 : $i]:
% 0.45/0.68         ((r2_hidden @ (sk_E @ X15 @ X12 @ X11) @ X12)
% 0.45/0.68          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X11))
% 0.45/0.68          | (r2_hidden @ X15 @ (a_2_0_orders_2 @ X11 @ X12))
% 0.45/0.68          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.45/0.68          | (v2_struct_0 @ X11)
% 0.45/0.68          | ~ (v3_orders_2 @ X11)
% 0.45/0.68          | ~ (v4_orders_2 @ X11)
% 0.45/0.68          | ~ (v5_orders_2 @ X11)
% 0.45/0.68          | ~ (l1_orders_2 @ X11))),
% 0.45/0.68      inference('simplify', [status(thm)], ['14'])).
% 0.45/0.68  thf('16', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (l1_orders_2 @ sk_A)
% 0.45/0.68          | ~ (v5_orders_2 @ sk_A)
% 0.45/0.68          | ~ (v4_orders_2 @ sk_A)
% 0.45/0.68          | ~ (v3_orders_2 @ sk_A)
% 0.45/0.68          | (v2_struct_0 @ sk_A)
% 0.45/0.68          | (r2_hidden @ X0 @ 
% 0.45/0.68             (a_2_0_orders_2 @ sk_A @ 
% 0.45/0.68              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.45/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68          | (r2_hidden @ 
% 0.45/0.68             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.45/0.68             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['13', '15'])).
% 0.45/0.68  thf('17', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('18', plain, ((v5_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('19', plain, ((v4_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('20', plain, ((v3_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('21', plain,
% 0.45/0.68      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.45/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('clc', [status(thm)], ['11', '12'])).
% 0.45/0.68  thf(d12_orders_2, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.45/0.68         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68           ( ( k1_orders_2 @ A @ B ) = ( a_2_0_orders_2 @ A @ B ) ) ) ) ))).
% 0.45/0.68  thf('22', plain,
% 0.45/0.68      (![X8 : $i, X9 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.45/0.68          | ((k1_orders_2 @ X9 @ X8) = (a_2_0_orders_2 @ X9 @ X8))
% 0.45/0.68          | ~ (l1_orders_2 @ X9)
% 0.45/0.68          | ~ (v5_orders_2 @ X9)
% 0.45/0.68          | ~ (v4_orders_2 @ X9)
% 0.45/0.68          | ~ (v3_orders_2 @ X9)
% 0.45/0.68          | (v2_struct_0 @ X9))),
% 0.45/0.68      inference('cnf', [status(esa)], [d12_orders_2])).
% 0.45/0.68  thf('23', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | ~ (v3_orders_2 @ sk_A)
% 0.45/0.68        | ~ (v4_orders_2 @ sk_A)
% 0.45/0.68        | ~ (v5_orders_2 @ sk_A)
% 0.45/0.68        | ~ (l1_orders_2 @ sk_A)
% 0.45/0.68        | ((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.45/0.68            = (a_2_0_orders_2 @ sk_A @ 
% 0.45/0.68               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.68  thf('24', plain, ((v3_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('25', plain, ((v4_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('26', plain, ((v5_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('27', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('28', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | ((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.45/0.68            = (a_2_0_orders_2 @ sk_A @ 
% 0.45/0.68               (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.45/0.68      inference('demod', [status(thm)], ['23', '24', '25', '26', '27'])).
% 0.45/0.68  thf('29', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('30', plain,
% 0.45/0.68      (((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.45/0.68         = (a_2_0_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['28', '29'])).
% 0.45/0.68  thf('31', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((v2_struct_0 @ sk_A)
% 0.45/0.68          | (r2_hidden @ X0 @ 
% 0.45/0.68             (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.45/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68          | (r2_hidden @ 
% 0.45/0.68             (sk_E @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.45/0.68             (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.45/0.68      inference('demod', [status(thm)], ['16', '17', '18', '19', '20', '30'])).
% 0.45/0.68  thf('32', plain,
% 0.45/0.68      (((r2_hidden @ 
% 0.45/0.68         (sk_E @ sk_C @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.45/0.68         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.45/0.68        | (r2_hidden @ sk_C @ 
% 0.45/0.68           (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.45/0.68        | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['5', '31'])).
% 0.45/0.68  thf('33', plain,
% 0.45/0.68      ((~ (r2_hidden @ sk_C @ 
% 0.45/0.68           (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.45/0.68        | ~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('34', plain,
% 0.45/0.68      ((~ (r2_hidden @ sk_C @ 
% 0.45/0.68           (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.45/0.68         <= (~
% 0.45/0.68             ((r2_hidden @ sk_C @ 
% 0.45/0.68               (k1_orders_2 @ sk_A @ 
% 0.45/0.68                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.45/0.68      inference('split', [status(esa)], ['33'])).
% 0.45/0.68  thf('35', plain,
% 0.45/0.68      (~
% 0.45/0.68       ((r2_hidden @ sk_C @ 
% 0.45/0.68         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))) | 
% 0.45/0.68       ~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.45/0.68      inference('split', [status(esa)], ['33'])).
% 0.45/0.68  thf(t69_enumset1, axiom,
% 0.45/0.68    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.68  thf('36', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.45/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.68  thf(d2_tarski, axiom,
% 0.45/0.68    (![A:$i,B:$i,C:$i]:
% 0.45/0.68     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.45/0.68       ( ![D:$i]:
% 0.45/0.68         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.45/0.68  thf('37', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.45/0.68         (((X1) != (X0))
% 0.45/0.68          | (r2_hidden @ X1 @ X2)
% 0.45/0.68          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.45/0.68      inference('cnf', [status(esa)], [d2_tarski])).
% 0.45/0.68  thf('38', plain,
% 0.45/0.68      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.45/0.68      inference('simplify', [status(thm)], ['37'])).
% 0.45/0.68  thf('39', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.68      inference('sup+', [status(thm)], ['36', '38'])).
% 0.45/0.68  thf('40', plain,
% 0.45/0.68      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.68  thf('41', plain,
% 0.45/0.68      (((r2_hidden @ sk_C @ 
% 0.45/0.68         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.45/0.68        | (r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('42', plain,
% 0.45/0.68      (((r2_hidden @ sk_C @ 
% 0.45/0.68         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.45/0.68         <= (((r2_hidden @ sk_C @ 
% 0.45/0.68               (k1_orders_2 @ sk_A @ 
% 0.45/0.68                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.45/0.68      inference('split', [status(esa)], ['41'])).
% 0.45/0.68  thf('43', plain,
% 0.45/0.68      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.45/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('clc', [status(thm)], ['11', '12'])).
% 0.45/0.68  thf('44', plain,
% 0.45/0.68      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.68         (~ (l1_orders_2 @ X11)
% 0.45/0.68          | ~ (v5_orders_2 @ X11)
% 0.45/0.68          | ~ (v4_orders_2 @ X11)
% 0.45/0.68          | ~ (v3_orders_2 @ X11)
% 0.45/0.68          | (v2_struct_0 @ X11)
% 0.45/0.68          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.45/0.68          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X11))
% 0.45/0.68          | (r2_orders_2 @ X11 @ X13 @ (sk_D_1 @ X12 @ X11 @ X14))
% 0.45/0.68          | ~ (r2_hidden @ X13 @ X12)
% 0.45/0.68          | ~ (r2_hidden @ X14 @ (a_2_0_orders_2 @ X11 @ X12)))),
% 0.45/0.68      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.45/0.68  thf('45', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X0 @ 
% 0.45/0.68             (a_2_0_orders_2 @ sk_A @ 
% 0.45/0.68              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.45/0.68          | ~ (r2_hidden @ X1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.45/0.68          | (r2_orders_2 @ sk_A @ X1 @ 
% 0.45/0.68             (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A @ X0))
% 0.45/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.45/0.68          | (v2_struct_0 @ sk_A)
% 0.45/0.68          | ~ (v3_orders_2 @ sk_A)
% 0.45/0.68          | ~ (v4_orders_2 @ sk_A)
% 0.45/0.68          | ~ (v5_orders_2 @ sk_A)
% 0.45/0.68          | ~ (l1_orders_2 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['43', '44'])).
% 0.45/0.68  thf('46', plain,
% 0.45/0.68      (((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.45/0.68         = (a_2_0_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['28', '29'])).
% 0.45/0.68  thf('47', plain, ((v3_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('48', plain, ((v4_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('49', plain, ((v5_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('50', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('51', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X0 @ 
% 0.45/0.68             (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.45/0.68          | ~ (r2_hidden @ X1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.45/0.68          | (r2_orders_2 @ sk_A @ X1 @ 
% 0.45/0.68             (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A @ X0))
% 0.45/0.68          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ sk_A))
% 0.45/0.68          | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['45', '46', '47', '48', '49', '50'])).
% 0.45/0.68  thf('52', plain,
% 0.45/0.68      ((![X0 : $i]:
% 0.45/0.68          ((v2_struct_0 @ sk_A)
% 0.45/0.68           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68           | (r2_orders_2 @ sk_A @ X0 @ 
% 0.45/0.68              (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A @ 
% 0.45/0.68               sk_C))
% 0.45/0.68           | ~ (r2_hidden @ X0 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.45/0.68         <= (((r2_hidden @ sk_C @ 
% 0.45/0.68               (k1_orders_2 @ sk_A @ 
% 0.45/0.68                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['42', '51'])).
% 0.45/0.68  thf('53', plain,
% 0.45/0.68      ((![X0 : $i]:
% 0.45/0.68          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.45/0.68           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68           | (r2_orders_2 @ sk_A @ X0 @ 
% 0.45/0.68              (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A @ 
% 0.45/0.68               sk_C))
% 0.45/0.68           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68           | (v2_struct_0 @ sk_A)))
% 0.45/0.68         <= (((r2_hidden @ sk_C @ 
% 0.45/0.68               (k1_orders_2 @ sk_A @ 
% 0.45/0.68                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['40', '52'])).
% 0.45/0.68  thf('54', plain,
% 0.45/0.68      (((r2_hidden @ sk_C @ 
% 0.45/0.68         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.45/0.68         <= (((r2_hidden @ sk_C @ 
% 0.45/0.68               (k1_orders_2 @ sk_A @ 
% 0.45/0.68                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.45/0.68      inference('split', [status(esa)], ['41'])).
% 0.45/0.68  thf('55', plain,
% 0.45/0.68      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.45/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('clc', [status(thm)], ['11', '12'])).
% 0.45/0.68  thf('56', plain,
% 0.45/0.68      (![X11 : $i, X12 : $i, X14 : $i]:
% 0.45/0.68         (~ (l1_orders_2 @ X11)
% 0.45/0.68          | ~ (v5_orders_2 @ X11)
% 0.45/0.68          | ~ (v4_orders_2 @ X11)
% 0.45/0.68          | ~ (v3_orders_2 @ X11)
% 0.45/0.68          | (v2_struct_0 @ X11)
% 0.45/0.68          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.45/0.68          | ((X14) = (sk_D_1 @ X12 @ X11 @ X14))
% 0.45/0.68          | ~ (r2_hidden @ X14 @ (a_2_0_orders_2 @ X11 @ X12)))),
% 0.45/0.68      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.45/0.68  thf('57', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X0 @ 
% 0.45/0.68             (a_2_0_orders_2 @ sk_A @ 
% 0.45/0.68              (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.45/0.68          | ((X0)
% 0.45/0.68              = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A @ 
% 0.45/0.68                 X0))
% 0.45/0.68          | (v2_struct_0 @ sk_A)
% 0.45/0.68          | ~ (v3_orders_2 @ sk_A)
% 0.45/0.68          | ~ (v4_orders_2 @ sk_A)
% 0.45/0.68          | ~ (v5_orders_2 @ sk_A)
% 0.45/0.68          | ~ (l1_orders_2 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.68  thf('58', plain,
% 0.45/0.68      (((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.45/0.68         = (a_2_0_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['28', '29'])).
% 0.45/0.68  thf('59', plain, ((v3_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('60', plain, ((v4_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('61', plain, ((v5_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('62', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('63', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X0 @ 
% 0.45/0.68             (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))
% 0.45/0.68          | ((X0)
% 0.45/0.68              = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A @ 
% 0.45/0.68                 X0))
% 0.45/0.68          | (v2_struct_0 @ sk_A))),
% 0.45/0.68      inference('demod', [status(thm)], ['57', '58', '59', '60', '61', '62'])).
% 0.45/0.68  thf('64', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('65', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (((X0)
% 0.45/0.68            = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A @ X0))
% 0.45/0.68          | ~ (r2_hidden @ X0 @ 
% 0.45/0.68               (k1_orders_2 @ sk_A @ 
% 0.45/0.68                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.45/0.68      inference('clc', [status(thm)], ['63', '64'])).
% 0.45/0.68  thf('66', plain,
% 0.45/0.68      ((((sk_C)
% 0.45/0.68          = (sk_D_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A @ sk_C)))
% 0.45/0.68         <= (((r2_hidden @ sk_C @ 
% 0.45/0.68               (k1_orders_2 @ sk_A @ 
% 0.45/0.68                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['54', '65'])).
% 0.45/0.68  thf('67', plain,
% 0.45/0.68      ((![X0 : $i]:
% 0.45/0.68          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.45/0.68           | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68           | (r2_orders_2 @ sk_A @ X0 @ sk_C)
% 0.45/0.68           | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68           | (v2_struct_0 @ sk_A)))
% 0.45/0.68         <= (((r2_hidden @ sk_C @ 
% 0.45/0.68               (k1_orders_2 @ sk_A @ 
% 0.45/0.68                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.45/0.68      inference('demod', [status(thm)], ['53', '66'])).
% 0.45/0.68  thf('68', plain,
% 0.45/0.68      ((((v2_struct_0 @ sk_A)
% 0.45/0.68         | ~ (m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))
% 0.45/0.68         | (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.45/0.68         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.45/0.68         <= (((r2_hidden @ sk_C @ 
% 0.45/0.68               (k1_orders_2 @ sk_A @ 
% 0.45/0.68                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['39', '67'])).
% 0.45/0.68  thf('69', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('70', plain,
% 0.45/0.68      ((((v2_struct_0 @ sk_A)
% 0.45/0.68         | (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.45/0.68         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.45/0.68         <= (((r2_hidden @ sk_C @ 
% 0.45/0.68               (k1_orders_2 @ sk_A @ 
% 0.45/0.68                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.45/0.68      inference('demod', [status(thm)], ['68', '69'])).
% 0.45/0.68  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('72', plain,
% 0.45/0.68      ((((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68         | (r2_orders_2 @ sk_A @ sk_B @ sk_C)))
% 0.45/0.68         <= (((r2_hidden @ sk_C @ 
% 0.45/0.68               (k1_orders_2 @ sk_A @ 
% 0.45/0.68                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.45/0.68      inference('clc', [status(thm)], ['70', '71'])).
% 0.45/0.68  thf('73', plain,
% 0.45/0.68      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.45/0.68         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.45/0.68      inference('split', [status(esa)], ['33'])).
% 0.45/0.68  thf('74', plain,
% 0.45/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.45/0.68             ((r2_hidden @ sk_C @ 
% 0.45/0.68               (k1_orders_2 @ sk_A @ 
% 0.45/0.68                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['72', '73'])).
% 0.45/0.68  thf(fc2_struct_0, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.68       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.68  thf('75', plain,
% 0.45/0.68      (![X7 : $i]:
% 0.45/0.68         (~ (v1_xboole_0 @ (u1_struct_0 @ X7))
% 0.45/0.68          | ~ (l1_struct_0 @ X7)
% 0.45/0.68          | (v2_struct_0 @ X7))),
% 0.45/0.68      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.68  thf('76', plain,
% 0.45/0.68      ((((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A)))
% 0.45/0.68         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.45/0.68             ((r2_hidden @ sk_C @ 
% 0.45/0.68               (k1_orders_2 @ sk_A @ 
% 0.45/0.68                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['74', '75'])).
% 0.45/0.68  thf('77', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf(dt_l1_orders_2, axiom,
% 0.45/0.68    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.68  thf('78', plain,
% 0.45/0.68      (![X10 : $i]: ((l1_struct_0 @ X10) | ~ (l1_orders_2 @ X10))),
% 0.45/0.68      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.45/0.68  thf('79', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.68      inference('sup-', [status(thm)], ['77', '78'])).
% 0.45/0.68  thf('80', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A))
% 0.45/0.68         <= (~ ((r2_orders_2 @ sk_A @ sk_B @ sk_C)) & 
% 0.45/0.68             ((r2_hidden @ sk_C @ 
% 0.45/0.68               (k1_orders_2 @ sk_A @ 
% 0.45/0.68                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.45/0.68      inference('demod', [status(thm)], ['76', '79'])).
% 0.45/0.68  thf('81', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('82', plain,
% 0.45/0.68      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.45/0.68       ~
% 0.45/0.68       ((r2_hidden @ sk_C @ 
% 0.45/0.68         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['80', '81'])).
% 0.45/0.68  thf('83', plain,
% 0.45/0.68      (~
% 0.45/0.68       ((r2_hidden @ sk_C @ 
% 0.45/0.68         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.45/0.68      inference('sat_resolution*', [status(thm)], ['35', '82'])).
% 0.45/0.68  thf('84', plain,
% 0.45/0.68      (~ (r2_hidden @ sk_C @ 
% 0.45/0.68          (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.45/0.68      inference('simpl_trail', [status(thm)], ['34', '83'])).
% 0.45/0.68  thf('85', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | (r2_hidden @ 
% 0.45/0.68           (sk_E @ sk_C @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.45/0.68           (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['32', '84'])).
% 0.45/0.68  thf('86', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('87', plain,
% 0.45/0.68      ((r2_hidden @ 
% 0.45/0.68        (sk_E @ sk_C @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ sk_A) @ 
% 0.45/0.68        (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))),
% 0.45/0.68      inference('clc', [status(thm)], ['85', '86'])).
% 0.45/0.68  thf('88', plain,
% 0.45/0.68      (((r2_hidden @ (sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.45/0.68         (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['4', '87'])).
% 0.45/0.68  thf('89', plain,
% 0.45/0.68      (((r2_hidden @ (sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.45/0.68         (k1_tarski @ sk_B))
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['3', '88'])).
% 0.45/0.68  thf('90', plain,
% 0.45/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | (r2_hidden @ (sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.45/0.68           (k1_tarski @ sk_B)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['89'])).
% 0.45/0.68  thf('91', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.45/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.68  thf('92', plain,
% 0.45/0.68      (![X0 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X4 @ X2)
% 0.45/0.68          | ((X4) = (X3))
% 0.45/0.68          | ((X4) = (X0))
% 0.45/0.68          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.45/0.68      inference('cnf', [status(esa)], [d2_tarski])).
% 0.45/0.68  thf('93', plain,
% 0.45/0.68      (![X0 : $i, X3 : $i, X4 : $i]:
% 0.45/0.68         (((X4) = (X0))
% 0.45/0.68          | ((X4) = (X3))
% 0.45/0.68          | ~ (r2_hidden @ X4 @ (k2_tarski @ X3 @ X0)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['92'])).
% 0.45/0.68  thf('94', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X1) = (X0)) | ((X1) = (X0)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['91', '93'])).
% 0.45/0.68  thf('95', plain,
% 0.45/0.68      (![X0 : $i, X1 : $i]:
% 0.45/0.68         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['94'])).
% 0.45/0.68  thf('96', plain,
% 0.45/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | ((sk_E @ sk_C @ (k1_tarski @ sk_B) @ sk_A) = (sk_B)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['90', '95'])).
% 0.45/0.68  thf('97', plain,
% 0.45/0.68      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.68  thf('98', plain,
% 0.45/0.68      ((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.45/0.68        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('clc', [status(thm)], ['11', '12'])).
% 0.45/0.68  thf('99', plain,
% 0.45/0.68      (((m1_subset_1 @ (k1_tarski @ sk_B) @ 
% 0.45/0.68         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['97', '98'])).
% 0.45/0.68  thf('100', plain,
% 0.45/0.68      (![X11 : $i, X12 : $i, X14 : $i, X15 : $i]:
% 0.45/0.68         (~ (l1_orders_2 @ X11)
% 0.45/0.68          | ~ (v5_orders_2 @ X11)
% 0.45/0.68          | ~ (v4_orders_2 @ X11)
% 0.45/0.68          | ~ (v3_orders_2 @ X11)
% 0.45/0.68          | (v2_struct_0 @ X11)
% 0.45/0.68          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.45/0.68          | (r2_hidden @ X14 @ (a_2_0_orders_2 @ X11 @ X12))
% 0.45/0.68          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X11))
% 0.45/0.68          | ((X14) != (X15))
% 0.45/0.68          | ~ (r2_orders_2 @ X11 @ (sk_E @ X15 @ X12 @ X11) @ X15))),
% 0.45/0.68      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 0.45/0.68  thf('101', plain,
% 0.45/0.68      (![X11 : $i, X12 : $i, X15 : $i]:
% 0.45/0.68         (~ (r2_orders_2 @ X11 @ (sk_E @ X15 @ X12 @ X11) @ X15)
% 0.45/0.68          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X11))
% 0.45/0.68          | (r2_hidden @ X15 @ (a_2_0_orders_2 @ X11 @ X12))
% 0.45/0.68          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.45/0.68          | (v2_struct_0 @ X11)
% 0.45/0.68          | ~ (v3_orders_2 @ X11)
% 0.45/0.68          | ~ (v4_orders_2 @ X11)
% 0.45/0.68          | ~ (v5_orders_2 @ X11)
% 0.45/0.68          | ~ (l1_orders_2 @ X11))),
% 0.45/0.68      inference('simplify', [status(thm)], ['100'])).
% 0.45/0.68  thf('102', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68          | ~ (l1_orders_2 @ sk_A)
% 0.45/0.68          | ~ (v5_orders_2 @ sk_A)
% 0.45/0.68          | ~ (v4_orders_2 @ sk_A)
% 0.45/0.68          | ~ (v3_orders_2 @ sk_A)
% 0.45/0.68          | (v2_struct_0 @ sk_A)
% 0.45/0.68          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.45/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68          | ~ (r2_orders_2 @ sk_A @ (sk_E @ X0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.45/0.68               X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['99', '101'])).
% 0.45/0.68  thf('103', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('104', plain, ((v5_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('105', plain, ((v4_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('106', plain, ((v3_orders_2 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('107', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         ((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68          | (v2_struct_0 @ sk_A)
% 0.45/0.68          | (r2_hidden @ X0 @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.45/0.68          | ~ (m1_subset_1 @ X0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68          | ~ (r2_orders_2 @ sk_A @ (sk_E @ X0 @ (k1_tarski @ sk_B) @ sk_A) @ 
% 0.45/0.68               X0))),
% 0.45/0.68      inference('demod', [status(thm)], ['102', '103', '104', '105', '106'])).
% 0.45/0.68  thf('108', plain,
% 0.45/0.68      ((~ (r2_orders_2 @ sk_A @ sk_B @ sk_C)
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | ~ (m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.45/0.68        | (v2_struct_0 @ sk_A)
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['96', '107'])).
% 0.45/0.68  thf('109', plain,
% 0.45/0.68      (((r2_orders_2 @ sk_A @ sk_B @ sk_C))
% 0.45/0.68         <= (((r2_orders_2 @ sk_A @ sk_B @ sk_C)))),
% 0.45/0.68      inference('split', [status(esa)], ['41'])).
% 0.45/0.68  thf('110', plain,
% 0.45/0.68      (((r2_orders_2 @ sk_A @ sk_B @ sk_C)) | 
% 0.45/0.68       ((r2_hidden @ sk_C @ 
% 0.45/0.68         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.45/0.68      inference('split', [status(esa)], ['41'])).
% 0.45/0.68  thf('111', plain, (((r2_orders_2 @ sk_A @ sk_B @ sk_C))),
% 0.45/0.68      inference('sat_resolution*', [status(thm)], ['35', '82', '110'])).
% 0.45/0.68  thf('112', plain, ((r2_orders_2 @ sk_A @ sk_B @ sk_C)),
% 0.45/0.68      inference('simpl_trail', [status(thm)], ['109', '111'])).
% 0.45/0.68  thf('113', plain, ((m1_subset_1 @ sk_C @ (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('114', plain,
% 0.45/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.45/0.68        | (v2_struct_0 @ sk_A)
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('demod', [status(thm)], ['108', '112', '113'])).
% 0.45/0.68  thf('115', plain,
% 0.45/0.68      (((v2_struct_0 @ sk_A)
% 0.45/0.68        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('simplify', [status(thm)], ['114'])).
% 0.45/0.68  thf('116', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.68  thf('117', plain,
% 0.45/0.68      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.45/0.68        | (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B))))),
% 0.45/0.68      inference('clc', [status(thm)], ['115', '116'])).
% 0.45/0.68  thf('118', plain,
% 0.45/0.68      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.45/0.68  thf('119', plain,
% 0.45/0.68      (((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.45/0.68         = (a_2_0_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))),
% 0.45/0.68      inference('clc', [status(thm)], ['28', '29'])).
% 0.45/0.68  thf('120', plain,
% 0.45/0.68      ((((k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))
% 0.45/0.68          = (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('sup+', [status(thm)], ['118', '119'])).
% 0.45/0.68  thf('121', plain,
% 0.45/0.68      ((~ (r2_hidden @ sk_C @ 
% 0.45/0.68           (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))
% 0.45/0.68         <= (~
% 0.45/0.68             ((r2_hidden @ sk_C @ 
% 0.45/0.68               (k1_orders_2 @ sk_A @ 
% 0.45/0.68                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.45/0.68      inference('split', [status(esa)], ['33'])).
% 0.45/0.68  thf('122', plain,
% 0.45/0.68      (((~ (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.45/0.68         | (v1_xboole_0 @ (u1_struct_0 @ sk_A))))
% 0.45/0.68         <= (~
% 0.45/0.68             ((r2_hidden @ sk_C @ 
% 0.45/0.68               (k1_orders_2 @ sk_A @ 
% 0.45/0.68                (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B)))))),
% 0.45/0.68      inference('sup-', [status(thm)], ['120', '121'])).
% 0.45/0.68  thf('123', plain,
% 0.45/0.68      (~
% 0.45/0.68       ((r2_hidden @ sk_C @ 
% 0.45/0.68         (k1_orders_2 @ sk_A @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B))))),
% 0.45/0.68      inference('sat_resolution*', [status(thm)], ['35', '82'])).
% 0.45/0.68  thf('124', plain,
% 0.45/0.68      ((~ (r2_hidden @ sk_C @ (a_2_0_orders_2 @ sk_A @ (k1_tarski @ sk_B)))
% 0.45/0.68        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.45/0.68      inference('simpl_trail', [status(thm)], ['122', '123'])).
% 0.45/0.68  thf('125', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 0.45/0.68      inference('clc', [status(thm)], ['117', '124'])).
% 0.45/0.68  thf('126', plain,
% 0.45/0.68      (![X7 : $i]:
% 0.45/0.68         (~ (v1_xboole_0 @ (u1_struct_0 @ X7))
% 0.45/0.68          | ~ (l1_struct_0 @ X7)
% 0.45/0.68          | (v2_struct_0 @ X7))),
% 0.45/0.68      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.68  thf('127', plain, (((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.68      inference('sup-', [status(thm)], ['125', '126'])).
% 0.45/0.68  thf('128', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.68      inference('sup-', [status(thm)], ['77', '78'])).
% 0.45/0.68  thf('129', plain, ((v2_struct_0 @ sk_A)),
% 0.45/0.68      inference('demod', [status(thm)], ['127', '128'])).
% 0.45/0.68  thf('130', plain, ($false), inference('demod', [status(thm)], ['0', '129'])).
% 0.45/0.68  
% 0.45/0.68  % SZS output end Refutation
% 0.45/0.68  
% 0.45/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
