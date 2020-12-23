%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v83h7GFLoJ

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:42 EST 2020

% Result     : Theorem 47.34s
% Output     : Refutation 47.34s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 177 expanded)
%              Number of leaves         :   29 (  66 expanded)
%              Depth                    :   28
%              Number of atoms          :  989 (1908 expanded)
%              Number of equality atoms :   31 (  86 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(t45_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( k2_orders_2 @ A @ ( k1_struct_0 @ A ) )
        = ( u1_struct_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ( ( k2_orders_2 @ A @ ( k1_struct_0 @ A ) )
          = ( u1_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_orders_2])).

thf('0',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('1',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('2',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_orders_2 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_orders_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_orders_2 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X9: $i] :
      ( ( ( k1_struct_0 @ X9 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('7',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ( ( k2_orders_2 @ X11 @ X10 )
        = ( a_2_1_orders_2 @ X11 @ X10 ) )
      | ~ ( l1_orders_2 @ X11 )
      | ~ ( v5_orders_2 @ X11 )
      | ~ ( v4_orders_2 @ X11 )
      | ~ ( v3_orders_2 @ X11 )
      | ( v2_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ k1_xboole_0 )
        = ( a_2_1_orders_2 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X9: $i] :
      ( ( ( k1_struct_0 @ X9 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('11',plain,(
    ! [X9: $i] :
      ( ( ( k1_struct_0 @ X9 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('12',plain,(
    ! [X9: $i] :
      ( ( ( k1_struct_0 @ X9 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('13',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k1_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_orders_2 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_orders_2])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( k2_orders_2 @ X0 @ ( k1_struct_0 @ X1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t49_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ C @ A )
           => ( r2_hidden @ C @ B ) )
       => ( A = B ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X1 @ X2 ) @ X2 )
      | ( X2 = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_orders_2 @ X0 @ ( k1_struct_0 @ X1 ) ) )
      | ( m1_subset_1 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k1_struct_0 @ X1 ) ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C @ ( k2_orders_2 @ X0 @ k1_xboole_0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_orders_2 @ X0 @ ( k1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_orders_2 @ X0 @ ( k1_struct_0 @ X1 ) ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ ( k2_orders_2 @ X0 @ k1_xboole_0 ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X9: $i] :
      ( ( ( k1_struct_0 @ X9 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('22',plain,(
    ! [X9: $i] :
      ( ( ( k1_struct_0 @ X9 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_struct_0 @ X1 )
        = ( k1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ sk_A ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) )
       != ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) )
       != ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
       != ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_C @ ( k2_orders_2 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','27'])).

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

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ sk_A )
       != ( u1_struct_0 @ sk_A ) )
      | ( m1_subset_1 @ ( sk_C @ ( k2_orders_2 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( k2_orders_2 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ ( k2_orders_2 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C @ ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['10','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ sk_A ) ) @ ( u1_struct_0 @ sk_A ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['37'])).

thf('39',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('40',plain,(
    ! [X15: $i,X16: $i,X18: $i,X19: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( r2_hidden @ X18 @ ( a_2_1_orders_2 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X15 ) )
      | ( X18 != X19 )
      | ( r2_hidden @ ( sk_E @ X19 @ X16 @ X15 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('41',plain,(
    ! [X15: $i,X16: $i,X19: $i] :
      ( ( r2_hidden @ ( sk_E @ X19 @ X16 @ X15 ) @ X16 )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X15 ) )
      | ( r2_hidden @ X19 @ ( a_2_1_orders_2 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( v2_struct_0 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( l1_orders_2 @ X15 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ sk_A ) ) @ ( a_2_1_orders_2 @ sk_A @ k1_xboole_0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( l1_orders_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','42'])).

thf('44',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 @ sk_A ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ sk_A ) ) @ ( a_2_1_orders_2 @ sk_A @ k1_xboole_0 ) )
      | ( v2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['43','44','45','46','47'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('49',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ X8 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ sk_A ) ) @ ( a_2_1_orders_2 @ sk_A @ k1_xboole_0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_E @ ( sk_C @ ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ sk_A ) ) @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ sk_A ) ) @ ( a_2_1_orders_2 @ sk_A @ k1_xboole_0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ sk_A ) ) @ ( a_2_1_orders_2 @ sk_A @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ sk_A ) ) @ ( k2_orders_2 @ sk_A @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','54'])).

thf('56',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ sk_A ) ) @ ( k2_orders_2 @ sk_A @ k1_xboole_0 ) )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ sk_A ) ) @ ( k2_orders_2 @ sk_A @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k2_orders_2 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) @ ( k2_orders_2 @ sk_A @ k1_xboole_0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ ( k2_orders_2 @ sk_A @ k1_xboole_0 ) @ ( u1_struct_0 @ sk_A ) ) @ ( k2_orders_2 @ sk_A @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X1 @ X2 ) @ X1 )
      | ( X2 = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t49_subset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ ( k2_orders_2 @ sk_A @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( ( u1_struct_0 @ sk_A )
        = ( k2_orders_2 @ sk_A @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X9: $i] :
      ( ( ( k1_struct_0 @ X9 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('68',plain,(
    ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ sk_A ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( ( k2_orders_2 @ sk_A @ k1_xboole_0 )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['0','1'])).

thf('71',plain,(
    ( k2_orders_2 @ sk_A @ k1_xboole_0 )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ ( k2_orders_2 @ sk_A @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ sk_A )
      | ~ ( v5_orders_2 @ sk_A )
      | ~ ( v4_orders_2 @ sk_A )
      | ~ ( v3_orders_2 @ sk_A )
      | ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','72'])).

thf('74',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ sk_A )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77'])).

thf('79',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ~ ( l1_struct_0 @ X0 ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference('sup-',[status(thm)],['2','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.v83h7GFLoJ
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:14:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 47.34/47.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 47.34/47.52  % Solved by: fo/fo7.sh
% 47.34/47.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 47.34/47.52  % done 3135 iterations in 47.058s
% 47.34/47.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 47.34/47.52  % SZS output start Refutation
% 47.34/47.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 47.34/47.52  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 47.34/47.52  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 47.34/47.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 47.34/47.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 47.34/47.52  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 47.34/47.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 47.34/47.52  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 47.34/47.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 47.34/47.52  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 47.34/47.52  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 47.34/47.52  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 47.34/47.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 47.34/47.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 47.34/47.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 47.34/47.52  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 47.34/47.52  thf(sk_A_type, type, sk_A: $i).
% 47.34/47.52  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 47.34/47.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 47.34/47.52  thf(t45_orders_2, conjecture,
% 47.34/47.52    (![A:$i]:
% 47.34/47.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 47.34/47.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 47.34/47.52       ( ( k2_orders_2 @ A @ ( k1_struct_0 @ A ) ) = ( u1_struct_0 @ A ) ) ))).
% 47.34/47.52  thf(zf_stmt_0, negated_conjecture,
% 47.34/47.52    (~( ![A:$i]:
% 47.34/47.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 47.34/47.52            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 47.34/47.52          ( ( k2_orders_2 @ A @ ( k1_struct_0 @ A ) ) = ( u1_struct_0 @ A ) ) ) )),
% 47.34/47.52    inference('cnf.neg', [status(esa)], [t45_orders_2])).
% 47.34/47.52  thf('0', plain, ((l1_orders_2 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf(dt_l1_orders_2, axiom,
% 47.34/47.52    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 47.34/47.52  thf('1', plain, (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_orders_2 @ X14))),
% 47.34/47.52      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 47.34/47.52  thf('2', plain, ((l1_struct_0 @ sk_A)),
% 47.34/47.52      inference('sup-', [status(thm)], ['0', '1'])).
% 47.34/47.52  thf(t4_subset_1, axiom,
% 47.34/47.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 47.34/47.52  thf('3', plain,
% 47.34/47.52      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 47.34/47.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 47.34/47.52  thf(dt_k2_orders_2, axiom,
% 47.34/47.52    (![A:$i,B:$i]:
% 47.34/47.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 47.34/47.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 47.34/47.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 47.34/47.52       ( m1_subset_1 @
% 47.34/47.52         ( k2_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 47.34/47.52  thf('4', plain,
% 47.34/47.52      (![X12 : $i, X13 : $i]:
% 47.34/47.52         (~ (l1_orders_2 @ X12)
% 47.34/47.52          | ~ (v5_orders_2 @ X12)
% 47.34/47.52          | ~ (v4_orders_2 @ X12)
% 47.34/47.52          | ~ (v3_orders_2 @ X12)
% 47.34/47.52          | (v2_struct_0 @ X12)
% 47.34/47.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 47.34/47.52          | (m1_subset_1 @ (k2_orders_2 @ X12 @ X13) @ 
% 47.34/47.52             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 47.34/47.52      inference('cnf', [status(esa)], [dt_k2_orders_2])).
% 47.34/47.52  thf('5', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         ((m1_subset_1 @ (k2_orders_2 @ X0 @ k1_xboole_0) @ 
% 47.34/47.52           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 47.34/47.52          | (v2_struct_0 @ X0)
% 47.34/47.52          | ~ (v3_orders_2 @ X0)
% 47.34/47.52          | ~ (v4_orders_2 @ X0)
% 47.34/47.52          | ~ (v5_orders_2 @ X0)
% 47.34/47.52          | ~ (l1_orders_2 @ X0))),
% 47.34/47.52      inference('sup-', [status(thm)], ['3', '4'])).
% 47.34/47.52  thf(d2_struct_0, axiom,
% 47.34/47.52    (![A:$i]:
% 47.34/47.52     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 47.34/47.52  thf('6', plain,
% 47.34/47.52      (![X9 : $i]:
% 47.34/47.52         (((k1_struct_0 @ X9) = (k1_xboole_0)) | ~ (l1_struct_0 @ X9))),
% 47.34/47.52      inference('cnf', [status(esa)], [d2_struct_0])).
% 47.34/47.52  thf('7', plain,
% 47.34/47.52      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 47.34/47.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 47.34/47.52  thf(d13_orders_2, axiom,
% 47.34/47.52    (![A:$i]:
% 47.34/47.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 47.34/47.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 47.34/47.52       ( ![B:$i]:
% 47.34/47.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 47.34/47.52           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 47.34/47.52  thf('8', plain,
% 47.34/47.52      (![X10 : $i, X11 : $i]:
% 47.34/47.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 47.34/47.52          | ((k2_orders_2 @ X11 @ X10) = (a_2_1_orders_2 @ X11 @ X10))
% 47.34/47.52          | ~ (l1_orders_2 @ X11)
% 47.34/47.52          | ~ (v5_orders_2 @ X11)
% 47.34/47.52          | ~ (v4_orders_2 @ X11)
% 47.34/47.52          | ~ (v3_orders_2 @ X11)
% 47.34/47.52          | (v2_struct_0 @ X11))),
% 47.34/47.52      inference('cnf', [status(esa)], [d13_orders_2])).
% 47.34/47.52  thf('9', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         ((v2_struct_0 @ X0)
% 47.34/47.52          | ~ (v3_orders_2 @ X0)
% 47.34/47.52          | ~ (v4_orders_2 @ X0)
% 47.34/47.52          | ~ (v5_orders_2 @ X0)
% 47.34/47.52          | ~ (l1_orders_2 @ X0)
% 47.34/47.52          | ((k2_orders_2 @ X0 @ k1_xboole_0)
% 47.34/47.52              = (a_2_1_orders_2 @ X0 @ k1_xboole_0)))),
% 47.34/47.52      inference('sup-', [status(thm)], ['7', '8'])).
% 47.34/47.52  thf('10', plain,
% 47.34/47.52      (![X9 : $i]:
% 47.34/47.52         (((k1_struct_0 @ X9) = (k1_xboole_0)) | ~ (l1_struct_0 @ X9))),
% 47.34/47.52      inference('cnf', [status(esa)], [d2_struct_0])).
% 47.34/47.52  thf('11', plain,
% 47.34/47.52      (![X9 : $i]:
% 47.34/47.52         (((k1_struct_0 @ X9) = (k1_xboole_0)) | ~ (l1_struct_0 @ X9))),
% 47.34/47.52      inference('cnf', [status(esa)], [d2_struct_0])).
% 47.34/47.52  thf('12', plain,
% 47.34/47.52      (![X9 : $i]:
% 47.34/47.52         (((k1_struct_0 @ X9) = (k1_xboole_0)) | ~ (l1_struct_0 @ X9))),
% 47.34/47.52      inference('cnf', [status(esa)], [d2_struct_0])).
% 47.34/47.52  thf('13', plain,
% 47.34/47.52      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 47.34/47.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 47.34/47.52  thf('14', plain,
% 47.34/47.52      (![X0 : $i, X1 : $i]:
% 47.34/47.52         ((m1_subset_1 @ (k1_struct_0 @ X0) @ (k1_zfmisc_1 @ X1))
% 47.34/47.52          | ~ (l1_struct_0 @ X0))),
% 47.34/47.52      inference('sup+', [status(thm)], ['12', '13'])).
% 47.34/47.52  thf('15', plain,
% 47.34/47.52      (![X12 : $i, X13 : $i]:
% 47.34/47.52         (~ (l1_orders_2 @ X12)
% 47.34/47.52          | ~ (v5_orders_2 @ X12)
% 47.34/47.52          | ~ (v4_orders_2 @ X12)
% 47.34/47.52          | ~ (v3_orders_2 @ X12)
% 47.34/47.52          | (v2_struct_0 @ X12)
% 47.34/47.52          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 47.34/47.52          | (m1_subset_1 @ (k2_orders_2 @ X12 @ X13) @ 
% 47.34/47.52             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 47.34/47.52      inference('cnf', [status(esa)], [dt_k2_orders_2])).
% 47.34/47.52  thf('16', plain,
% 47.34/47.52      (![X0 : $i, X1 : $i]:
% 47.34/47.52         (~ (l1_struct_0 @ X1)
% 47.34/47.52          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k1_struct_0 @ X1)) @ 
% 47.34/47.52             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 47.34/47.52          | (v2_struct_0 @ X0)
% 47.34/47.52          | ~ (v3_orders_2 @ X0)
% 47.34/47.52          | ~ (v4_orders_2 @ X0)
% 47.34/47.52          | ~ (v5_orders_2 @ X0)
% 47.34/47.52          | ~ (l1_orders_2 @ X0))),
% 47.34/47.52      inference('sup-', [status(thm)], ['14', '15'])).
% 47.34/47.52  thf(t49_subset_1, axiom,
% 47.34/47.52    (![A:$i,B:$i]:
% 47.34/47.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 47.34/47.52       ( ( ![C:$i]: ( ( m1_subset_1 @ C @ A ) => ( r2_hidden @ C @ B ) ) ) =>
% 47.34/47.52         ( ( A ) = ( B ) ) ) ))).
% 47.34/47.52  thf('17', plain,
% 47.34/47.52      (![X1 : $i, X2 : $i]:
% 47.34/47.52         ((m1_subset_1 @ (sk_C @ X1 @ X2) @ X2)
% 47.34/47.52          | ((X2) = (X1))
% 47.34/47.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 47.34/47.52      inference('cnf', [status(esa)], [t49_subset_1])).
% 47.34/47.52  thf('18', plain,
% 47.34/47.52      (![X0 : $i, X1 : $i]:
% 47.34/47.52         (~ (l1_orders_2 @ X0)
% 47.34/47.52          | ~ (v5_orders_2 @ X0)
% 47.34/47.52          | ~ (v4_orders_2 @ X0)
% 47.34/47.52          | ~ (v3_orders_2 @ X0)
% 47.34/47.52          | (v2_struct_0 @ X0)
% 47.34/47.52          | ~ (l1_struct_0 @ X1)
% 47.34/47.52          | ((u1_struct_0 @ X0) = (k2_orders_2 @ X0 @ (k1_struct_0 @ X1)))
% 47.34/47.52          | (m1_subset_1 @ 
% 47.34/47.52             (sk_C @ (k2_orders_2 @ X0 @ (k1_struct_0 @ X1)) @ 
% 47.34/47.52              (u1_struct_0 @ X0)) @ 
% 47.34/47.52             (u1_struct_0 @ X0)))),
% 47.34/47.52      inference('sup-', [status(thm)], ['16', '17'])).
% 47.34/47.52  thf('19', plain,
% 47.34/47.52      (![X0 : $i, X1 : $i]:
% 47.34/47.52         ((m1_subset_1 @ 
% 47.34/47.52           (sk_C @ (k2_orders_2 @ X0 @ k1_xboole_0) @ (u1_struct_0 @ X0)) @ 
% 47.34/47.52           (u1_struct_0 @ X0))
% 47.34/47.52          | ~ (l1_struct_0 @ X1)
% 47.34/47.52          | ((u1_struct_0 @ X0) = (k2_orders_2 @ X0 @ (k1_struct_0 @ X1)))
% 47.34/47.52          | ~ (l1_struct_0 @ X1)
% 47.34/47.52          | (v2_struct_0 @ X0)
% 47.34/47.52          | ~ (v3_orders_2 @ X0)
% 47.34/47.52          | ~ (v4_orders_2 @ X0)
% 47.34/47.52          | ~ (v5_orders_2 @ X0)
% 47.34/47.52          | ~ (l1_orders_2 @ X0))),
% 47.34/47.52      inference('sup+', [status(thm)], ['11', '18'])).
% 47.34/47.52  thf('20', plain,
% 47.34/47.52      (![X0 : $i, X1 : $i]:
% 47.34/47.52         (~ (l1_orders_2 @ X0)
% 47.34/47.52          | ~ (v5_orders_2 @ X0)
% 47.34/47.52          | ~ (v4_orders_2 @ X0)
% 47.34/47.52          | ~ (v3_orders_2 @ X0)
% 47.34/47.52          | (v2_struct_0 @ X0)
% 47.34/47.52          | ((u1_struct_0 @ X0) = (k2_orders_2 @ X0 @ (k1_struct_0 @ X1)))
% 47.34/47.52          | ~ (l1_struct_0 @ X1)
% 47.34/47.52          | (m1_subset_1 @ 
% 47.34/47.52             (sk_C @ (k2_orders_2 @ X0 @ k1_xboole_0) @ (u1_struct_0 @ X0)) @ 
% 47.34/47.52             (u1_struct_0 @ X0)))),
% 47.34/47.52      inference('simplify', [status(thm)], ['19'])).
% 47.34/47.52  thf('21', plain,
% 47.34/47.52      (![X9 : $i]:
% 47.34/47.52         (((k1_struct_0 @ X9) = (k1_xboole_0)) | ~ (l1_struct_0 @ X9))),
% 47.34/47.52      inference('cnf', [status(esa)], [d2_struct_0])).
% 47.34/47.52  thf('22', plain,
% 47.34/47.52      (![X9 : $i]:
% 47.34/47.52         (((k1_struct_0 @ X9) = (k1_xboole_0)) | ~ (l1_struct_0 @ X9))),
% 47.34/47.52      inference('cnf', [status(esa)], [d2_struct_0])).
% 47.34/47.52  thf('23', plain,
% 47.34/47.52      (![X0 : $i, X1 : $i]:
% 47.34/47.52         (((k1_struct_0 @ X1) = (k1_struct_0 @ X0))
% 47.34/47.52          | ~ (l1_struct_0 @ X0)
% 47.34/47.52          | ~ (l1_struct_0 @ X1))),
% 47.34/47.52      inference('sup+', [status(thm)], ['21', '22'])).
% 47.34/47.52  thf('24', plain,
% 47.34/47.52      (((k2_orders_2 @ sk_A @ (k1_struct_0 @ sk_A)) != (u1_struct_0 @ sk_A))),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('25', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         (((k2_orders_2 @ sk_A @ (k1_struct_0 @ X0)) != (u1_struct_0 @ sk_A))
% 47.34/47.52          | ~ (l1_struct_0 @ X0)
% 47.34/47.52          | ~ (l1_struct_0 @ sk_A))),
% 47.34/47.52      inference('sup-', [status(thm)], ['23', '24'])).
% 47.34/47.52  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 47.34/47.52      inference('sup-', [status(thm)], ['0', '1'])).
% 47.34/47.52  thf('27', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         (((k2_orders_2 @ sk_A @ (k1_struct_0 @ X0)) != (u1_struct_0 @ sk_A))
% 47.34/47.52          | ~ (l1_struct_0 @ X0))),
% 47.34/47.52      inference('demod', [status(thm)], ['25', '26'])).
% 47.34/47.52  thf('28', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         (((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 47.34/47.52          | (m1_subset_1 @ 
% 47.34/47.52             (sk_C @ (k2_orders_2 @ sk_A @ k1_xboole_0) @ (u1_struct_0 @ sk_A)) @ 
% 47.34/47.52             (u1_struct_0 @ sk_A))
% 47.34/47.52          | ~ (l1_struct_0 @ X0)
% 47.34/47.52          | (v2_struct_0 @ sk_A)
% 47.34/47.52          | ~ (v3_orders_2 @ sk_A)
% 47.34/47.52          | ~ (v4_orders_2 @ sk_A)
% 47.34/47.52          | ~ (v5_orders_2 @ sk_A)
% 47.34/47.52          | ~ (l1_orders_2 @ sk_A)
% 47.34/47.52          | ~ (l1_struct_0 @ X0))),
% 47.34/47.52      inference('sup-', [status(thm)], ['20', '27'])).
% 47.34/47.52  thf('29', plain, ((v3_orders_2 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('30', plain, ((v4_orders_2 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('31', plain, ((v5_orders_2 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('32', plain, ((l1_orders_2 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('33', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         (((u1_struct_0 @ sk_A) != (u1_struct_0 @ sk_A))
% 47.34/47.52          | (m1_subset_1 @ 
% 47.34/47.52             (sk_C @ (k2_orders_2 @ sk_A @ k1_xboole_0) @ (u1_struct_0 @ sk_A)) @ 
% 47.34/47.52             (u1_struct_0 @ sk_A))
% 47.34/47.52          | ~ (l1_struct_0 @ X0)
% 47.34/47.52          | (v2_struct_0 @ sk_A)
% 47.34/47.52          | ~ (l1_struct_0 @ X0))),
% 47.34/47.52      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 47.34/47.52  thf('34', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         ((v2_struct_0 @ sk_A)
% 47.34/47.52          | ~ (l1_struct_0 @ X0)
% 47.34/47.52          | (m1_subset_1 @ 
% 47.34/47.52             (sk_C @ (k2_orders_2 @ sk_A @ k1_xboole_0) @ (u1_struct_0 @ sk_A)) @ 
% 47.34/47.52             (u1_struct_0 @ sk_A)))),
% 47.34/47.52      inference('simplify', [status(thm)], ['33'])).
% 47.34/47.52  thf('35', plain, (~ (v2_struct_0 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('36', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         ((m1_subset_1 @ 
% 47.34/47.52           (sk_C @ (k2_orders_2 @ sk_A @ k1_xboole_0) @ (u1_struct_0 @ sk_A)) @ 
% 47.34/47.52           (u1_struct_0 @ sk_A))
% 47.34/47.52          | ~ (l1_struct_0 @ X0))),
% 47.34/47.52      inference('clc', [status(thm)], ['34', '35'])).
% 47.34/47.52  thf('37', plain,
% 47.34/47.52      (![X0 : $i, X1 : $i]:
% 47.34/47.52         ((m1_subset_1 @ 
% 47.34/47.52           (sk_C @ (k2_orders_2 @ sk_A @ (k1_struct_0 @ X0)) @ 
% 47.34/47.52            (u1_struct_0 @ sk_A)) @ 
% 47.34/47.52           (u1_struct_0 @ sk_A))
% 47.34/47.52          | ~ (l1_struct_0 @ X0)
% 47.34/47.52          | ~ (l1_struct_0 @ X1))),
% 47.34/47.52      inference('sup+', [status(thm)], ['10', '36'])).
% 47.34/47.52  thf('38', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         ((m1_subset_1 @ 
% 47.34/47.52           (sk_C @ (k2_orders_2 @ sk_A @ (k1_struct_0 @ X0)) @ 
% 47.34/47.52            (u1_struct_0 @ sk_A)) @ 
% 47.34/47.52           (u1_struct_0 @ sk_A))
% 47.34/47.52          | ~ (l1_struct_0 @ X0))),
% 47.34/47.52      inference('condensation', [status(thm)], ['37'])).
% 47.34/47.52  thf('39', plain,
% 47.34/47.52      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 47.34/47.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 47.34/47.52  thf(fraenkel_a_2_1_orders_2, axiom,
% 47.34/47.52    (![A:$i,B:$i,C:$i]:
% 47.34/47.52     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 47.34/47.52         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 47.34/47.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 47.34/47.52       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 47.34/47.52         ( ?[D:$i]:
% 47.34/47.52           ( ( ![E:$i]:
% 47.34/47.52               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 47.34/47.52                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 47.34/47.52             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 47.34/47.52  thf('40', plain,
% 47.34/47.52      (![X15 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 47.34/47.52         (~ (l1_orders_2 @ X15)
% 47.34/47.52          | ~ (v5_orders_2 @ X15)
% 47.34/47.52          | ~ (v4_orders_2 @ X15)
% 47.34/47.52          | ~ (v3_orders_2 @ X15)
% 47.34/47.52          | (v2_struct_0 @ X15)
% 47.34/47.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 47.34/47.52          | (r2_hidden @ X18 @ (a_2_1_orders_2 @ X15 @ X16))
% 47.34/47.52          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X15))
% 47.34/47.52          | ((X18) != (X19))
% 47.34/47.52          | (r2_hidden @ (sk_E @ X19 @ X16 @ X15) @ X16))),
% 47.34/47.52      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 47.34/47.52  thf('41', plain,
% 47.34/47.52      (![X15 : $i, X16 : $i, X19 : $i]:
% 47.34/47.52         ((r2_hidden @ (sk_E @ X19 @ X16 @ X15) @ X16)
% 47.34/47.52          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X15))
% 47.34/47.52          | (r2_hidden @ X19 @ (a_2_1_orders_2 @ X15 @ X16))
% 47.34/47.52          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 47.34/47.52          | (v2_struct_0 @ X15)
% 47.34/47.52          | ~ (v3_orders_2 @ X15)
% 47.34/47.52          | ~ (v4_orders_2 @ X15)
% 47.34/47.52          | ~ (v5_orders_2 @ X15)
% 47.34/47.52          | ~ (l1_orders_2 @ X15))),
% 47.34/47.52      inference('simplify', [status(thm)], ['40'])).
% 47.34/47.52  thf('42', plain,
% 47.34/47.52      (![X0 : $i, X1 : $i]:
% 47.34/47.52         (~ (l1_orders_2 @ X0)
% 47.34/47.52          | ~ (v5_orders_2 @ X0)
% 47.34/47.52          | ~ (v4_orders_2 @ X0)
% 47.34/47.52          | ~ (v3_orders_2 @ X0)
% 47.34/47.52          | (v2_struct_0 @ X0)
% 47.34/47.52          | (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ k1_xboole_0))
% 47.34/47.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 47.34/47.52          | (r2_hidden @ (sk_E @ X1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 47.34/47.52      inference('sup-', [status(thm)], ['39', '41'])).
% 47.34/47.52  thf('43', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         (~ (l1_struct_0 @ X0)
% 47.34/47.52          | (r2_hidden @ 
% 47.34/47.52             (sk_E @ 
% 47.34/47.52              (sk_C @ (k2_orders_2 @ sk_A @ (k1_struct_0 @ X0)) @ 
% 47.34/47.52               (u1_struct_0 @ sk_A)) @ 
% 47.34/47.52              k1_xboole_0 @ sk_A) @ 
% 47.34/47.52             k1_xboole_0)
% 47.34/47.52          | (r2_hidden @ 
% 47.34/47.52             (sk_C @ (k2_orders_2 @ sk_A @ (k1_struct_0 @ X0)) @ 
% 47.34/47.52              (u1_struct_0 @ sk_A)) @ 
% 47.34/47.52             (a_2_1_orders_2 @ sk_A @ k1_xboole_0))
% 47.34/47.52          | (v2_struct_0 @ sk_A)
% 47.34/47.52          | ~ (v3_orders_2 @ sk_A)
% 47.34/47.52          | ~ (v4_orders_2 @ sk_A)
% 47.34/47.52          | ~ (v5_orders_2 @ sk_A)
% 47.34/47.52          | ~ (l1_orders_2 @ sk_A))),
% 47.34/47.52      inference('sup-', [status(thm)], ['38', '42'])).
% 47.34/47.52  thf('44', plain, ((v3_orders_2 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('45', plain, ((v4_orders_2 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('46', plain, ((v5_orders_2 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('47', plain, ((l1_orders_2 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('48', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         (~ (l1_struct_0 @ X0)
% 47.34/47.52          | (r2_hidden @ 
% 47.34/47.52             (sk_E @ 
% 47.34/47.52              (sk_C @ (k2_orders_2 @ sk_A @ (k1_struct_0 @ X0)) @ 
% 47.34/47.52               (u1_struct_0 @ sk_A)) @ 
% 47.34/47.52              k1_xboole_0 @ sk_A) @ 
% 47.34/47.52             k1_xboole_0)
% 47.34/47.52          | (r2_hidden @ 
% 47.34/47.52             (sk_C @ (k2_orders_2 @ sk_A @ (k1_struct_0 @ X0)) @ 
% 47.34/47.52              (u1_struct_0 @ sk_A)) @ 
% 47.34/47.52             (a_2_1_orders_2 @ sk_A @ k1_xboole_0))
% 47.34/47.52          | (v2_struct_0 @ sk_A))),
% 47.34/47.52      inference('demod', [status(thm)], ['43', '44', '45', '46', '47'])).
% 47.34/47.52  thf(t7_ordinal1, axiom,
% 47.34/47.52    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 47.34/47.52  thf('49', plain,
% 47.34/47.52      (![X7 : $i, X8 : $i]: (~ (r2_hidden @ X7 @ X8) | ~ (r1_tarski @ X8 @ X7))),
% 47.34/47.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 47.34/47.52  thf('50', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         ((v2_struct_0 @ sk_A)
% 47.34/47.52          | (r2_hidden @ 
% 47.34/47.52             (sk_C @ (k2_orders_2 @ sk_A @ (k1_struct_0 @ X0)) @ 
% 47.34/47.52              (u1_struct_0 @ sk_A)) @ 
% 47.34/47.52             (a_2_1_orders_2 @ sk_A @ k1_xboole_0))
% 47.34/47.52          | ~ (l1_struct_0 @ X0)
% 47.34/47.52          | ~ (r1_tarski @ k1_xboole_0 @ 
% 47.34/47.52               (sk_E @ 
% 47.34/47.52                (sk_C @ (k2_orders_2 @ sk_A @ (k1_struct_0 @ X0)) @ 
% 47.34/47.52                 (u1_struct_0 @ sk_A)) @ 
% 47.34/47.52                k1_xboole_0 @ sk_A)))),
% 47.34/47.52      inference('sup-', [status(thm)], ['48', '49'])).
% 47.34/47.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 47.34/47.52  thf('51', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 47.34/47.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 47.34/47.52  thf('52', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         ((v2_struct_0 @ sk_A)
% 47.34/47.52          | (r2_hidden @ 
% 47.34/47.52             (sk_C @ (k2_orders_2 @ sk_A @ (k1_struct_0 @ X0)) @ 
% 47.34/47.52              (u1_struct_0 @ sk_A)) @ 
% 47.34/47.52             (a_2_1_orders_2 @ sk_A @ k1_xboole_0))
% 47.34/47.52          | ~ (l1_struct_0 @ X0))),
% 47.34/47.52      inference('demod', [status(thm)], ['50', '51'])).
% 47.34/47.52  thf('53', plain, (~ (v2_struct_0 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('54', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         (~ (l1_struct_0 @ X0)
% 47.34/47.52          | (r2_hidden @ 
% 47.34/47.52             (sk_C @ (k2_orders_2 @ sk_A @ (k1_struct_0 @ X0)) @ 
% 47.34/47.52              (u1_struct_0 @ sk_A)) @ 
% 47.34/47.52             (a_2_1_orders_2 @ sk_A @ k1_xboole_0)))),
% 47.34/47.52      inference('clc', [status(thm)], ['52', '53'])).
% 47.34/47.52  thf('55', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         ((r2_hidden @ 
% 47.34/47.52           (sk_C @ (k2_orders_2 @ sk_A @ (k1_struct_0 @ X0)) @ 
% 47.34/47.52            (u1_struct_0 @ sk_A)) @ 
% 47.34/47.52           (k2_orders_2 @ sk_A @ k1_xboole_0))
% 47.34/47.52          | ~ (l1_orders_2 @ sk_A)
% 47.34/47.52          | ~ (v5_orders_2 @ sk_A)
% 47.34/47.52          | ~ (v4_orders_2 @ sk_A)
% 47.34/47.52          | ~ (v3_orders_2 @ sk_A)
% 47.34/47.52          | (v2_struct_0 @ sk_A)
% 47.34/47.52          | ~ (l1_struct_0 @ X0))),
% 47.34/47.52      inference('sup+', [status(thm)], ['9', '54'])).
% 47.34/47.52  thf('56', plain, ((l1_orders_2 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('57', plain, ((v5_orders_2 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('58', plain, ((v4_orders_2 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('59', plain, ((v3_orders_2 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('60', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         ((r2_hidden @ 
% 47.34/47.52           (sk_C @ (k2_orders_2 @ sk_A @ (k1_struct_0 @ X0)) @ 
% 47.34/47.52            (u1_struct_0 @ sk_A)) @ 
% 47.34/47.52           (k2_orders_2 @ sk_A @ k1_xboole_0))
% 47.34/47.52          | (v2_struct_0 @ sk_A)
% 47.34/47.52          | ~ (l1_struct_0 @ X0))),
% 47.34/47.52      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 47.34/47.52  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('62', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         (~ (l1_struct_0 @ X0)
% 47.34/47.52          | (r2_hidden @ 
% 47.34/47.52             (sk_C @ (k2_orders_2 @ sk_A @ (k1_struct_0 @ X0)) @ 
% 47.34/47.52              (u1_struct_0 @ sk_A)) @ 
% 47.34/47.52             (k2_orders_2 @ sk_A @ k1_xboole_0)))),
% 47.34/47.52      inference('clc', [status(thm)], ['60', '61'])).
% 47.34/47.52  thf('63', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         ((r2_hidden @ 
% 47.34/47.52           (sk_C @ (k2_orders_2 @ sk_A @ k1_xboole_0) @ (u1_struct_0 @ sk_A)) @ 
% 47.34/47.52           (k2_orders_2 @ sk_A @ k1_xboole_0))
% 47.34/47.52          | ~ (l1_struct_0 @ X0)
% 47.34/47.52          | ~ (l1_struct_0 @ X0))),
% 47.34/47.52      inference('sup+', [status(thm)], ['6', '62'])).
% 47.34/47.52  thf('64', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         (~ (l1_struct_0 @ X0)
% 47.34/47.52          | (r2_hidden @ 
% 47.34/47.52             (sk_C @ (k2_orders_2 @ sk_A @ k1_xboole_0) @ (u1_struct_0 @ sk_A)) @ 
% 47.34/47.52             (k2_orders_2 @ sk_A @ k1_xboole_0)))),
% 47.34/47.52      inference('simplify', [status(thm)], ['63'])).
% 47.34/47.52  thf('65', plain,
% 47.34/47.52      (![X1 : $i, X2 : $i]:
% 47.34/47.52         (~ (r2_hidden @ (sk_C @ X1 @ X2) @ X1)
% 47.34/47.52          | ((X2) = (X1))
% 47.34/47.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 47.34/47.52      inference('cnf', [status(esa)], [t49_subset_1])).
% 47.34/47.52  thf('66', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         (~ (l1_struct_0 @ X0)
% 47.34/47.52          | ~ (m1_subset_1 @ (k2_orders_2 @ sk_A @ k1_xboole_0) @ 
% 47.34/47.52               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 47.34/47.52          | ((u1_struct_0 @ sk_A) = (k2_orders_2 @ sk_A @ k1_xboole_0)))),
% 47.34/47.52      inference('sup-', [status(thm)], ['64', '65'])).
% 47.34/47.52  thf('67', plain,
% 47.34/47.52      (![X9 : $i]:
% 47.34/47.52         (((k1_struct_0 @ X9) = (k1_xboole_0)) | ~ (l1_struct_0 @ X9))),
% 47.34/47.52      inference('cnf', [status(esa)], [d2_struct_0])).
% 47.34/47.52  thf('68', plain,
% 47.34/47.52      (((k2_orders_2 @ sk_A @ (k1_struct_0 @ sk_A)) != (u1_struct_0 @ sk_A))),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('69', plain,
% 47.34/47.52      ((((k2_orders_2 @ sk_A @ k1_xboole_0) != (u1_struct_0 @ sk_A))
% 47.34/47.52        | ~ (l1_struct_0 @ sk_A))),
% 47.34/47.52      inference('sup-', [status(thm)], ['67', '68'])).
% 47.34/47.52  thf('70', plain, ((l1_struct_0 @ sk_A)),
% 47.34/47.52      inference('sup-', [status(thm)], ['0', '1'])).
% 47.34/47.52  thf('71', plain,
% 47.34/47.52      (((k2_orders_2 @ sk_A @ k1_xboole_0) != (u1_struct_0 @ sk_A))),
% 47.34/47.52      inference('demod', [status(thm)], ['69', '70'])).
% 47.34/47.52  thf('72', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         (~ (l1_struct_0 @ X0)
% 47.34/47.52          | ~ (m1_subset_1 @ (k2_orders_2 @ sk_A @ k1_xboole_0) @ 
% 47.34/47.52               (k1_zfmisc_1 @ (u1_struct_0 @ sk_A))))),
% 47.34/47.52      inference('simplify_reflect-', [status(thm)], ['66', '71'])).
% 47.34/47.52  thf('73', plain,
% 47.34/47.52      (![X0 : $i]:
% 47.34/47.52         (~ (l1_orders_2 @ sk_A)
% 47.34/47.52          | ~ (v5_orders_2 @ sk_A)
% 47.34/47.52          | ~ (v4_orders_2 @ sk_A)
% 47.34/47.52          | ~ (v3_orders_2 @ sk_A)
% 47.34/47.52          | (v2_struct_0 @ sk_A)
% 47.34/47.52          | ~ (l1_struct_0 @ X0))),
% 47.34/47.52      inference('sup-', [status(thm)], ['5', '72'])).
% 47.34/47.52  thf('74', plain, ((l1_orders_2 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('75', plain, ((v5_orders_2 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('76', plain, ((v4_orders_2 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('77', plain, ((v3_orders_2 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('78', plain, (![X0 : $i]: ((v2_struct_0 @ sk_A) | ~ (l1_struct_0 @ X0))),
% 47.34/47.52      inference('demod', [status(thm)], ['73', '74', '75', '76', '77'])).
% 47.34/47.52  thf('79', plain, (~ (v2_struct_0 @ sk_A)),
% 47.34/47.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 47.34/47.52  thf('80', plain, (![X0 : $i]: ~ (l1_struct_0 @ X0)),
% 47.34/47.52      inference('clc', [status(thm)], ['78', '79'])).
% 47.34/47.52  thf('81', plain, ($false), inference('sup-', [status(thm)], ['2', '80'])).
% 47.34/47.52  
% 47.34/47.52  % SZS output end Refutation
% 47.34/47.52  
% 47.34/47.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
