%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6sa9rV6PQL

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:39 EST 2020

% Result     : Theorem 5.34s
% Output     : Refutation 5.34s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 298 expanded)
%              Number of leaves         :   32 ( 104 expanded)
%              Depth                    :   25
%              Number of atoms          : 2183 (4148 expanded)
%              Number of equality atoms :   77 ( 198 expanded)
%              Maximal formula depth    :   22 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(a_2_0_orders_2_type,type,(
    a_2_0_orders_2: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t44_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( k1_orders_2 @ A @ ( k2_struct_0 @ A ) )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ( ( k1_orders_2 @ A @ ( k2_struct_0 @ A ) )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t44_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('3',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('4',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X5 ) @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('6',plain,(
    ! [X4: $i] :
      ( ( k2_subset_1 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('7',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( ( k1_orders_2 @ X12 @ X11 )
        = ( a_2_0_orders_2 @ X12 @ X11 ) )
      | ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d12_orders_2])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( a_2_0_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_0_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_0_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('14',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('15',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( X17
        = ( sk_D @ X15 @ X14 @ X17 ) )
      | ~ ( r2_hidden @ X17 @ ( a_2_0_orders_2 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( a_2_0_orders_2 @ X0 @ X1 ) )
      | ( X2
        = ( sk_D @ X1 @ X0 @ X2 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( X1
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( X1
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['2','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_0_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('23',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('24',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('25',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X15 @ X14 @ X17 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( r2_hidden @ X17 @ ( a_2_0_orders_2 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( a_2_0_orders_2 @ X0 @ X1 ) )
      | ( m1_subset_1 @ ( sk_D @ X1 @ X0 @ X2 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('35',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('38',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_0_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('41',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('42',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('43',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( u1_struct_0 @ X14 ) )
      | ( r2_orders_2 @ X14 @ X16 @ ( sk_D @ X15 @ X14 @ X17 ) )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( r2_hidden @ X17 @ ( a_2_0_orders_2 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ X2 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ X2 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ X2 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ X2 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ X1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ X1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_orders_2 @ X0 @ X1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_orders_2 @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( r2_orders_2 @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['36','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('56',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('58',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('59',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( X17
        = ( sk_D @ X15 @ X14 @ X17 ) )
      | ~ ( r2_hidden @ X17 @ ( a_2_0_orders_2 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( X1
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( X1
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('66',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('68',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('69',plain,(
    ! [X14: $i,X15: $i,X17: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X15 @ X14 @ X17 ) @ ( u1_struct_0 @ X14 ) )
      | ~ ( r2_hidden @ X17 @ ( a_2_0_orders_2 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['66','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','73'])).

thf(d10_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( r2_orders_2 @ A @ B @ C )
              <=> ( ( r1_orders_2 @ A @ B @ C )
                  & ( B != C ) ) ) ) ) ) )).

thf('75',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X9 ) )
      | ~ ( r2_orders_2 @ X9 @ X8 @ X10 )
      | ( X8 != X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) )
      | ~ ( l1_orders_2 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('76',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( l1_orders_2 @ X9 )
      | ~ ( r2_orders_2 @ X9 @ X10 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( r2_orders_2 @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['64','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_orders_2 @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('90',plain,(
    ! [X13: $i] :
      ( ( l1_struct_0 @ X13 )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('91',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['84','85','86','87','88','91'])).

thf('93',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X6: $i] :
      ( ( ( k2_struct_0 @ X6 )
        = ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('97',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 )
      | ( v2_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['95','99'])).

thf('101',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['89','90'])).

thf('102',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    $false ),
    inference(demod,[status(thm)],['0','102'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6sa9rV6PQL
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:04:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 5.34/5.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.34/5.52  % Solved by: fo/fo7.sh
% 5.34/5.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.34/5.52  % done 6542 iterations in 5.069s
% 5.34/5.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.34/5.52  % SZS output start Refutation
% 5.34/5.52  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 5.34/5.52  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 5.34/5.52  thf(sk_B_type, type, sk_B: $i > $i).
% 5.34/5.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 5.34/5.52  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 5.34/5.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.34/5.52  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 5.34/5.52  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 5.34/5.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 5.34/5.52  thf(sk_A_type, type, sk_A: $i).
% 5.34/5.52  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 5.34/5.52  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 5.34/5.52  thf(a_2_0_orders_2_type, type, a_2_0_orders_2: $i > $i > $i).
% 5.34/5.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.34/5.52  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 5.34/5.52  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 5.34/5.52  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 5.34/5.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 5.34/5.52  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 5.34/5.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 5.34/5.52  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 5.34/5.52  thf(t44_orders_2, conjecture,
% 5.34/5.52    (![A:$i]:
% 5.34/5.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 5.34/5.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 5.34/5.52       ( ( k1_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 5.34/5.52  thf(zf_stmt_0, negated_conjecture,
% 5.34/5.52    (~( ![A:$i]:
% 5.34/5.52        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 5.34/5.52            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 5.34/5.52          ( ( k1_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 5.34/5.52    inference('cnf.neg', [status(esa)], [t44_orders_2])).
% 5.34/5.52  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 5.34/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.34/5.52  thf(d3_struct_0, axiom,
% 5.34/5.52    (![A:$i]:
% 5.34/5.52     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 5.34/5.52  thf('1', plain,
% 5.34/5.52      (![X6 : $i]:
% 5.34/5.52         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 5.34/5.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.34/5.52  thf(t7_xboole_0, axiom,
% 5.34/5.52    (![A:$i]:
% 5.34/5.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 5.34/5.52          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 5.34/5.52  thf('2', plain,
% 5.34/5.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 5.34/5.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 5.34/5.52  thf('3', plain,
% 5.34/5.52      (![X6 : $i]:
% 5.34/5.52         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 5.34/5.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.34/5.52  thf('4', plain,
% 5.34/5.52      (![X6 : $i]:
% 5.34/5.52         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 5.34/5.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.34/5.52  thf(dt_k2_subset_1, axiom,
% 5.34/5.52    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 5.34/5.52  thf('5', plain,
% 5.34/5.52      (![X5 : $i]: (m1_subset_1 @ (k2_subset_1 @ X5) @ (k1_zfmisc_1 @ X5))),
% 5.34/5.52      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 5.34/5.52  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 5.34/5.52  thf('6', plain, (![X4 : $i]: ((k2_subset_1 @ X4) = (X4))),
% 5.34/5.52      inference('cnf', [status(esa)], [d4_subset_1])).
% 5.34/5.52  thf('7', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 5.34/5.52      inference('demod', [status(thm)], ['5', '6'])).
% 5.34/5.52  thf(d12_orders_2, axiom,
% 5.34/5.52    (![A:$i]:
% 5.34/5.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 5.34/5.52         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 5.34/5.52       ( ![B:$i]:
% 5.34/5.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 5.34/5.52           ( ( k1_orders_2 @ A @ B ) = ( a_2_0_orders_2 @ A @ B ) ) ) ) ))).
% 5.34/5.52  thf('8', plain,
% 5.34/5.52      (![X11 : $i, X12 : $i]:
% 5.34/5.52         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 5.34/5.52          | ((k1_orders_2 @ X12 @ X11) = (a_2_0_orders_2 @ X12 @ X11))
% 5.34/5.52          | ~ (l1_orders_2 @ X12)
% 5.34/5.52          | ~ (v5_orders_2 @ X12)
% 5.34/5.52          | ~ (v4_orders_2 @ X12)
% 5.34/5.52          | ~ (v3_orders_2 @ X12)
% 5.34/5.52          | (v2_struct_0 @ X12))),
% 5.34/5.52      inference('cnf', [status(esa)], [d12_orders_2])).
% 5.34/5.52  thf('9', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         ((v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 5.34/5.52              = (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 5.34/5.52      inference('sup-', [status(thm)], ['7', '8'])).
% 5.34/5.52  thf('10', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         (((k1_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 5.34/5.52            = (a_2_0_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0))),
% 5.34/5.52      inference('sup+', [status(thm)], ['4', '9'])).
% 5.34/5.52  thf('11', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         (((k1_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 5.34/5.52            = (a_2_0_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0))),
% 5.34/5.52      inference('sup+', [status(thm)], ['3', '10'])).
% 5.34/5.52  thf('12', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         (~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 5.34/5.52              = (a_2_0_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 5.34/5.52      inference('simplify', [status(thm)], ['11'])).
% 5.34/5.52  thf('13', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 5.34/5.52      inference('demod', [status(thm)], ['5', '6'])).
% 5.34/5.52  thf('14', plain,
% 5.34/5.52      (![X6 : $i]:
% 5.34/5.52         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 5.34/5.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.34/5.52  thf(fraenkel_a_2_0_orders_2, axiom,
% 5.34/5.52    (![A:$i,B:$i,C:$i]:
% 5.34/5.52     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 5.34/5.52         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 5.34/5.52         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 5.34/5.52       ( ( r2_hidden @ A @ ( a_2_0_orders_2 @ B @ C ) ) <=>
% 5.34/5.52         ( ?[D:$i]:
% 5.34/5.52           ( ( ![E:$i]:
% 5.34/5.52               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 5.34/5.52                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ E @ D ) ) ) ) & 
% 5.34/5.52             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 5.34/5.52  thf('15', plain,
% 5.34/5.52      (![X14 : $i, X15 : $i, X17 : $i]:
% 5.34/5.52         (~ (l1_orders_2 @ X14)
% 5.34/5.52          | ~ (v5_orders_2 @ X14)
% 5.34/5.52          | ~ (v4_orders_2 @ X14)
% 5.34/5.52          | ~ (v3_orders_2 @ X14)
% 5.34/5.52          | (v2_struct_0 @ X14)
% 5.34/5.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 5.34/5.52          | ((X17) = (sk_D @ X15 @ X14 @ X17))
% 5.34/5.52          | ~ (r2_hidden @ X17 @ (a_2_0_orders_2 @ X14 @ X15)))),
% 5.34/5.52      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 5.34/5.52  thf('16', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.34/5.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (r2_hidden @ X2 @ (a_2_0_orders_2 @ X0 @ X1))
% 5.34/5.52          | ((X2) = (sk_D @ X1 @ X0 @ X2))
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0))),
% 5.34/5.52      inference('sup-', [status(thm)], ['14', '15'])).
% 5.34/5.52  thf('17', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i]:
% 5.34/5.52         (~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 5.34/5.52          | ~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 5.34/5.52          | ~ (l1_struct_0 @ X0))),
% 5.34/5.52      inference('sup-', [status(thm)], ['13', '16'])).
% 5.34/5.52  thf('18', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i]:
% 5.34/5.52         (~ (r2_hidden @ X1 @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0))),
% 5.34/5.52      inference('sup-', [status(thm)], ['12', '17'])).
% 5.34/5.52  thf('19', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i]:
% 5.34/5.52         (((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (r2_hidden @ X1 @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 5.34/5.52      inference('simplify', [status(thm)], ['18'])).
% 5.34/5.52  thf('20', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         (((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ((sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 5.34/5.52              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 5.34/5.52                 (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 5.34/5.52      inference('sup-', [status(thm)], ['2', '19'])).
% 5.34/5.52  thf('21', plain,
% 5.34/5.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 5.34/5.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 5.34/5.52  thf('22', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         (~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 5.34/5.52              = (a_2_0_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 5.34/5.52      inference('simplify', [status(thm)], ['11'])).
% 5.34/5.52  thf('23', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 5.34/5.52      inference('demod', [status(thm)], ['5', '6'])).
% 5.34/5.52  thf('24', plain,
% 5.34/5.52      (![X6 : $i]:
% 5.34/5.52         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 5.34/5.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.34/5.52  thf('25', plain,
% 5.34/5.52      (![X14 : $i, X15 : $i, X17 : $i]:
% 5.34/5.52         (~ (l1_orders_2 @ X14)
% 5.34/5.52          | ~ (v5_orders_2 @ X14)
% 5.34/5.52          | ~ (v4_orders_2 @ X14)
% 5.34/5.52          | ~ (v3_orders_2 @ X14)
% 5.34/5.52          | (v2_struct_0 @ X14)
% 5.34/5.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 5.34/5.52          | (m1_subset_1 @ (sk_D @ X15 @ X14 @ X17) @ (u1_struct_0 @ X14))
% 5.34/5.52          | ~ (r2_hidden @ X17 @ (a_2_0_orders_2 @ X14 @ X15)))),
% 5.34/5.52      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 5.34/5.52  thf('26', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.34/5.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (r2_hidden @ X2 @ (a_2_0_orders_2 @ X0 @ X1))
% 5.34/5.52          | (m1_subset_1 @ (sk_D @ X1 @ X0 @ X2) @ (u1_struct_0 @ X0))
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0))),
% 5.34/5.52      inference('sup-', [status(thm)], ['24', '25'])).
% 5.34/5.52  thf('27', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i]:
% 5.34/5.52         (~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 5.34/5.52             (u1_struct_0 @ X0))
% 5.34/5.52          | ~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 5.34/5.52          | ~ (l1_struct_0 @ X0))),
% 5.34/5.52      inference('sup-', [status(thm)], ['23', '26'])).
% 5.34/5.52  thf('28', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i]:
% 5.34/5.52         (~ (r2_hidden @ X1 @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 5.34/5.52             (u1_struct_0 @ X0))
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0))),
% 5.34/5.52      inference('sup-', [status(thm)], ['22', '27'])).
% 5.34/5.52  thf('29', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i]:
% 5.34/5.52         ((m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 5.34/5.52           (u1_struct_0 @ X0))
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (r2_hidden @ X1 @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 5.34/5.52      inference('simplify', [status(thm)], ['28'])).
% 5.34/5.52  thf('30', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         (((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | (m1_subset_1 @ 
% 5.34/5.52             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 5.34/5.52              (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 5.34/5.52             (u1_struct_0 @ X0)))),
% 5.34/5.52      inference('sup-', [status(thm)], ['21', '29'])).
% 5.34/5.52  thf('31', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         ((m1_subset_1 @ (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 5.34/5.52           (u1_struct_0 @ X0))
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 5.34/5.52      inference('sup+', [status(thm)], ['20', '30'])).
% 5.34/5.52  thf('32', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         (((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | (m1_subset_1 @ (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 5.34/5.52             (u1_struct_0 @ X0)))),
% 5.34/5.52      inference('simplify', [status(thm)], ['31'])).
% 5.34/5.52  thf('33', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         ((m1_subset_1 @ (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 5.34/5.52           (k2_struct_0 @ X0))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 5.34/5.52      inference('sup+', [status(thm)], ['1', '32'])).
% 5.34/5.52  thf('34', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         (((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | (m1_subset_1 @ (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 5.34/5.52             (k2_struct_0 @ X0)))),
% 5.34/5.52      inference('simplify', [status(thm)], ['33'])).
% 5.34/5.52  thf(d2_subset_1, axiom,
% 5.34/5.52    (![A:$i,B:$i]:
% 5.34/5.52     ( ( ( v1_xboole_0 @ A ) =>
% 5.34/5.52         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 5.34/5.52       ( ( ~( v1_xboole_0 @ A ) ) =>
% 5.34/5.52         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 5.34/5.52  thf('35', plain,
% 5.34/5.52      (![X1 : $i, X2 : $i]:
% 5.34/5.52         (~ (m1_subset_1 @ X1 @ X2)
% 5.34/5.52          | (r2_hidden @ X1 @ X2)
% 5.34/5.52          | (v1_xboole_0 @ X2))),
% 5.34/5.52      inference('cnf', [status(esa)], [d2_subset_1])).
% 5.34/5.52  thf('36', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         (~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 5.34/5.52          | (r2_hidden @ (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 5.34/5.52             (k2_struct_0 @ X0)))),
% 5.34/5.52      inference('sup-', [status(thm)], ['34', '35'])).
% 5.34/5.52  thf('37', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         (((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | (m1_subset_1 @ (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 5.34/5.52             (u1_struct_0 @ X0)))),
% 5.34/5.52      inference('simplify', [status(thm)], ['31'])).
% 5.34/5.52  thf('38', plain,
% 5.34/5.52      (![X6 : $i]:
% 5.34/5.52         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 5.34/5.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.34/5.52  thf('39', plain,
% 5.34/5.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 5.34/5.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 5.34/5.52  thf('40', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         (~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 5.34/5.52              = (a_2_0_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 5.34/5.52      inference('simplify', [status(thm)], ['11'])).
% 5.34/5.52  thf('41', plain,
% 5.34/5.52      (![X6 : $i]:
% 5.34/5.52         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 5.34/5.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.34/5.52  thf('42', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 5.34/5.52      inference('demod', [status(thm)], ['5', '6'])).
% 5.34/5.52  thf('43', plain,
% 5.34/5.52      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 5.34/5.52         (~ (l1_orders_2 @ X14)
% 5.34/5.52          | ~ (v5_orders_2 @ X14)
% 5.34/5.52          | ~ (v4_orders_2 @ X14)
% 5.34/5.52          | ~ (v3_orders_2 @ X14)
% 5.34/5.52          | (v2_struct_0 @ X14)
% 5.34/5.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 5.34/5.52          | ~ (m1_subset_1 @ X16 @ (u1_struct_0 @ X14))
% 5.34/5.52          | (r2_orders_2 @ X14 @ X16 @ (sk_D @ X15 @ X14 @ X17))
% 5.34/5.52          | ~ (r2_hidden @ X16 @ X15)
% 5.34/5.52          | ~ (r2_hidden @ X17 @ (a_2_0_orders_2 @ X14 @ X15)))),
% 5.34/5.52      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 5.34/5.52  thf('44', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.34/5.52         (~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 5.34/5.52          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 5.34/5.52          | (r2_orders_2 @ X0 @ X2 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 5.34/5.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0))),
% 5.34/5.52      inference('sup-', [status(thm)], ['42', '43'])).
% 5.34/5.52  thf('45', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.34/5.52         (~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 5.34/5.52          | (r2_orders_2 @ X0 @ X2 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 5.34/5.52          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0)))),
% 5.34/5.52      inference('sup-', [status(thm)], ['41', '44'])).
% 5.34/5.52  thf('46', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.34/5.52         (~ (r2_hidden @ X1 @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 5.34/5.52          | (r2_orders_2 @ X0 @ X2 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 5.34/5.52          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0))),
% 5.34/5.52      inference('sup-', [status(thm)], ['40', '45'])).
% 5.34/5.52  thf('47', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.34/5.52         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 5.34/5.52          | (r2_orders_2 @ X0 @ X2 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 5.34/5.52          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (r2_hidden @ X1 @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 5.34/5.52      inference('simplify', [status(thm)], ['46'])).
% 5.34/5.52  thf('48', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i]:
% 5.34/5.52         (((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 5.34/5.52          | (r2_orders_2 @ X0 @ X1 @ 
% 5.34/5.52             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 5.34/5.52              (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 5.34/5.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0)))),
% 5.34/5.52      inference('sup-', [status(thm)], ['39', '47'])).
% 5.34/5.52  thf('49', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i]:
% 5.34/5.52         (~ (r2_hidden @ X1 @ (k2_struct_0 @ X0))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 5.34/5.52          | (r2_orders_2 @ X0 @ X1 @ 
% 5.34/5.52             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 5.34/5.52              (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 5.34/5.52      inference('sup-', [status(thm)], ['38', '48'])).
% 5.34/5.52  thf('50', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i]:
% 5.34/5.52         (((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | (r2_orders_2 @ X0 @ X1 @ 
% 5.34/5.52             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 5.34/5.52              (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 5.34/5.52          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0)))),
% 5.34/5.52      inference('simplify', [status(thm)], ['49'])).
% 5.34/5.52  thf('51', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         (~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | ~ (r2_hidden @ (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 5.34/5.52               (k2_struct_0 @ X0))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | (r2_orders_2 @ X0 @ 
% 5.34/5.52             (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 5.34/5.52             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 5.34/5.52              (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 5.34/5.52      inference('sup-', [status(thm)], ['37', '50'])).
% 5.34/5.52  thf('52', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         ((r2_orders_2 @ X0 @ 
% 5.34/5.52           (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 5.34/5.52           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 5.34/5.52            (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 5.34/5.52          | ~ (r2_hidden @ (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 5.34/5.52               (k2_struct_0 @ X0))
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0))),
% 5.34/5.52      inference('simplify', [status(thm)], ['51'])).
% 5.34/5.52  thf('53', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | (r2_orders_2 @ X0 @ 
% 5.34/5.52             (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 5.34/5.52             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 5.34/5.52              (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 5.34/5.52      inference('sup-', [status(thm)], ['36', '52'])).
% 5.34/5.52  thf('54', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         ((r2_orders_2 @ X0 @ 
% 5.34/5.52           (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 5.34/5.52           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 5.34/5.52            (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 5.34/5.52      inference('simplify', [status(thm)], ['53'])).
% 5.34/5.52  thf('55', plain,
% 5.34/5.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 5.34/5.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 5.34/5.52  thf('56', plain,
% 5.34/5.52      (![X6 : $i]:
% 5.34/5.52         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 5.34/5.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.34/5.52  thf('57', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         ((v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 5.34/5.52              = (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 5.34/5.52      inference('sup-', [status(thm)], ['7', '8'])).
% 5.34/5.52  thf('58', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 5.34/5.52      inference('demod', [status(thm)], ['5', '6'])).
% 5.34/5.52  thf('59', plain,
% 5.34/5.52      (![X14 : $i, X15 : $i, X17 : $i]:
% 5.34/5.52         (~ (l1_orders_2 @ X14)
% 5.34/5.52          | ~ (v5_orders_2 @ X14)
% 5.34/5.52          | ~ (v4_orders_2 @ X14)
% 5.34/5.52          | ~ (v3_orders_2 @ X14)
% 5.34/5.52          | (v2_struct_0 @ X14)
% 5.34/5.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 5.34/5.52          | ((X17) = (sk_D @ X15 @ X14 @ X17))
% 5.34/5.52          | ~ (r2_hidden @ X17 @ (a_2_0_orders_2 @ X14 @ X15)))),
% 5.34/5.52      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 5.34/5.52  thf('60', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i]:
% 5.34/5.52         (~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 5.34/5.52          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0))),
% 5.34/5.52      inference('sup-', [status(thm)], ['58', '59'])).
% 5.34/5.52  thf('61', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i]:
% 5.34/5.52         (~ (r2_hidden @ X1 @ (k1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1)))),
% 5.34/5.52      inference('sup-', [status(thm)], ['57', '60'])).
% 5.34/5.52  thf('62', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i]:
% 5.34/5.52         (((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (r2_hidden @ X1 @ (k1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 5.34/5.52      inference('simplify', [status(thm)], ['61'])).
% 5.34/5.52  thf('63', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i]:
% 5.34/5.52         (~ (r2_hidden @ X1 @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1)))),
% 5.34/5.52      inference('sup-', [status(thm)], ['56', '62'])).
% 5.34/5.52  thf('64', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         (((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | ((sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 5.34/5.52              = (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 5.34/5.52                 (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0))),
% 5.34/5.52      inference('sup-', [status(thm)], ['55', '63'])).
% 5.34/5.52  thf('65', plain,
% 5.34/5.52      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 5.34/5.52      inference('cnf', [status(esa)], [t7_xboole_0])).
% 5.34/5.52  thf('66', plain,
% 5.34/5.52      (![X6 : $i]:
% 5.34/5.52         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 5.34/5.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.34/5.52  thf('67', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         ((v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 5.34/5.52              = (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 5.34/5.52      inference('sup-', [status(thm)], ['7', '8'])).
% 5.34/5.52  thf('68', plain, (![X5 : $i]: (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X5))),
% 5.34/5.52      inference('demod', [status(thm)], ['5', '6'])).
% 5.34/5.52  thf('69', plain,
% 5.34/5.52      (![X14 : $i, X15 : $i, X17 : $i]:
% 5.34/5.52         (~ (l1_orders_2 @ X14)
% 5.34/5.52          | ~ (v5_orders_2 @ X14)
% 5.34/5.52          | ~ (v4_orders_2 @ X14)
% 5.34/5.52          | ~ (v3_orders_2 @ X14)
% 5.34/5.52          | (v2_struct_0 @ X14)
% 5.34/5.52          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 5.34/5.52          | (m1_subset_1 @ (sk_D @ X15 @ X14 @ X17) @ (u1_struct_0 @ X14))
% 5.34/5.52          | ~ (r2_hidden @ X17 @ (a_2_0_orders_2 @ X14 @ X15)))),
% 5.34/5.52      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 5.34/5.52  thf('70', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i]:
% 5.34/5.52         (~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 5.34/5.52          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 5.34/5.52             (u1_struct_0 @ X0))
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0))),
% 5.34/5.52      inference('sup-', [status(thm)], ['68', '69'])).
% 5.34/5.52  thf('71', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i]:
% 5.34/5.52         (~ (r2_hidden @ X1 @ (k1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 5.34/5.52             (u1_struct_0 @ X0)))),
% 5.34/5.52      inference('sup-', [status(thm)], ['67', '70'])).
% 5.34/5.52  thf('72', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i]:
% 5.34/5.52         ((m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 5.34/5.52           (u1_struct_0 @ X0))
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (r2_hidden @ X1 @ (k1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 5.34/5.52      inference('simplify', [status(thm)], ['71'])).
% 5.34/5.52  thf('73', plain,
% 5.34/5.52      (![X0 : $i, X1 : $i]:
% 5.34/5.52         (~ (r2_hidden @ X1 @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 5.34/5.52             (u1_struct_0 @ X0)))),
% 5.34/5.52      inference('sup-', [status(thm)], ['66', '72'])).
% 5.34/5.52  thf('74', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         (((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | (m1_subset_1 @ 
% 5.34/5.52             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 5.34/5.52              (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 5.34/5.52             (u1_struct_0 @ X0))
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0))),
% 5.34/5.52      inference('sup-', [status(thm)], ['65', '73'])).
% 5.34/5.52  thf(d10_orders_2, axiom,
% 5.34/5.52    (![A:$i]:
% 5.34/5.52     ( ( l1_orders_2 @ A ) =>
% 5.34/5.52       ( ![B:$i]:
% 5.34/5.52         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 5.34/5.52           ( ![C:$i]:
% 5.34/5.52             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 5.34/5.52               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 5.34/5.52                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 5.34/5.52  thf('75', plain,
% 5.34/5.52      (![X8 : $i, X9 : $i, X10 : $i]:
% 5.34/5.52         (~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X9))
% 5.34/5.52          | ~ (r2_orders_2 @ X9 @ X8 @ X10)
% 5.34/5.52          | ((X8) != (X10))
% 5.34/5.52          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9))
% 5.34/5.52          | ~ (l1_orders_2 @ X9))),
% 5.34/5.52      inference('cnf', [status(esa)], [d10_orders_2])).
% 5.34/5.52  thf('76', plain,
% 5.34/5.52      (![X9 : $i, X10 : $i]:
% 5.34/5.52         (~ (l1_orders_2 @ X9)
% 5.34/5.52          | ~ (r2_orders_2 @ X9 @ X10 @ X10)
% 5.34/5.52          | ~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X9)))),
% 5.34/5.52      inference('simplify', [status(thm)], ['75'])).
% 5.34/5.52  thf('77', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         (~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | ~ (r2_orders_2 @ X0 @ 
% 5.34/5.52               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 5.34/5.52                (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 5.34/5.52               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 5.34/5.52                (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 5.34/5.52          | ~ (l1_orders_2 @ X0))),
% 5.34/5.52      inference('sup-', [status(thm)], ['74', '76'])).
% 5.34/5.52  thf('78', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         (~ (r2_orders_2 @ X0 @ 
% 5.34/5.52             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 5.34/5.52              (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 5.34/5.52             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 5.34/5.52              (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0))),
% 5.34/5.52      inference('simplify', [status(thm)], ['77'])).
% 5.34/5.52  thf('79', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         (~ (r2_orders_2 @ X0 @ 
% 5.34/5.52             (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 5.34/5.52             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 5.34/5.52              (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 5.34/5.52      inference('sup-', [status(thm)], ['64', '78'])).
% 5.34/5.52  thf('80', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         (((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (r2_orders_2 @ X0 @ 
% 5.34/5.52               (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 5.34/5.52               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 5.34/5.52                (sk_B @ (k1_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 5.34/5.52      inference('simplify', [status(thm)], ['79'])).
% 5.34/5.52  thf('81', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 5.34/5.52      inference('sup-', [status(thm)], ['54', '80'])).
% 5.34/5.52  thf('82', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         (~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_orders_2 @ X0)
% 5.34/5.52          | ~ (v5_orders_2 @ X0)
% 5.34/5.52          | ~ (v4_orders_2 @ X0)
% 5.34/5.52          | ~ (v3_orders_2 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 5.34/5.52          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 5.34/5.52      inference('simplify', [status(thm)], ['81'])).
% 5.34/5.52  thf('83', plain,
% 5.34/5.52      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 5.34/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.34/5.52  thf('84', plain,
% 5.34/5.52      ((((k1_xboole_0) != (k1_xboole_0))
% 5.34/5.52        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 5.34/5.52        | (v2_struct_0 @ sk_A)
% 5.34/5.52        | ~ (v3_orders_2 @ sk_A)
% 5.34/5.52        | ~ (v4_orders_2 @ sk_A)
% 5.34/5.52        | ~ (v5_orders_2 @ sk_A)
% 5.34/5.52        | ~ (l1_orders_2 @ sk_A)
% 5.34/5.52        | ~ (l1_struct_0 @ sk_A))),
% 5.34/5.52      inference('sup-', [status(thm)], ['82', '83'])).
% 5.34/5.52  thf('85', plain, ((v3_orders_2 @ sk_A)),
% 5.34/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.34/5.52  thf('86', plain, ((v4_orders_2 @ sk_A)),
% 5.34/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.34/5.52  thf('87', plain, ((v5_orders_2 @ sk_A)),
% 5.34/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.34/5.52  thf('88', plain, ((l1_orders_2 @ sk_A)),
% 5.34/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.34/5.52  thf('89', plain, ((l1_orders_2 @ sk_A)),
% 5.34/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.34/5.52  thf(dt_l1_orders_2, axiom,
% 5.34/5.52    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 5.34/5.52  thf('90', plain,
% 5.34/5.52      (![X13 : $i]: ((l1_struct_0 @ X13) | ~ (l1_orders_2 @ X13))),
% 5.34/5.52      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 5.34/5.52  thf('91', plain, ((l1_struct_0 @ sk_A)),
% 5.34/5.52      inference('sup-', [status(thm)], ['89', '90'])).
% 5.34/5.52  thf('92', plain,
% 5.34/5.52      ((((k1_xboole_0) != (k1_xboole_0))
% 5.34/5.52        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 5.34/5.52        | (v2_struct_0 @ sk_A))),
% 5.34/5.52      inference('demod', [status(thm)], ['84', '85', '86', '87', '88', '91'])).
% 5.34/5.52  thf('93', plain,
% 5.34/5.52      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 5.34/5.52      inference('simplify', [status(thm)], ['92'])).
% 5.34/5.52  thf('94', plain, (~ (v2_struct_0 @ sk_A)),
% 5.34/5.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.34/5.52  thf('95', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 5.34/5.52      inference('clc', [status(thm)], ['93', '94'])).
% 5.34/5.52  thf('96', plain,
% 5.34/5.52      (![X6 : $i]:
% 5.34/5.52         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 5.34/5.52      inference('cnf', [status(esa)], [d3_struct_0])).
% 5.34/5.52  thf(fc2_struct_0, axiom,
% 5.34/5.52    (![A:$i]:
% 5.34/5.52     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 5.34/5.52       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 5.34/5.52  thf('97', plain,
% 5.34/5.52      (![X7 : $i]:
% 5.34/5.52         (~ (v1_xboole_0 @ (u1_struct_0 @ X7))
% 5.34/5.52          | ~ (l1_struct_0 @ X7)
% 5.34/5.52          | (v2_struct_0 @ X7))),
% 5.34/5.52      inference('cnf', [status(esa)], [fc2_struct_0])).
% 5.34/5.52  thf('98', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | (v2_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0))),
% 5.34/5.52      inference('sup-', [status(thm)], ['96', '97'])).
% 5.34/5.52  thf('99', plain,
% 5.34/5.52      (![X0 : $i]:
% 5.34/5.52         ((v2_struct_0 @ X0)
% 5.34/5.52          | ~ (l1_struct_0 @ X0)
% 5.34/5.52          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 5.34/5.52      inference('simplify', [status(thm)], ['98'])).
% 5.34/5.52  thf('100', plain, ((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 5.34/5.52      inference('sup-', [status(thm)], ['95', '99'])).
% 5.34/5.52  thf('101', plain, ((l1_struct_0 @ sk_A)),
% 5.34/5.52      inference('sup-', [status(thm)], ['89', '90'])).
% 5.34/5.52  thf('102', plain, ((v2_struct_0 @ sk_A)),
% 5.34/5.52      inference('demod', [status(thm)], ['100', '101'])).
% 5.34/5.52  thf('103', plain, ($false), inference('demod', [status(thm)], ['0', '102'])).
% 5.34/5.52  
% 5.34/5.52  % SZS output end Refutation
% 5.34/5.52  
% 5.34/5.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
