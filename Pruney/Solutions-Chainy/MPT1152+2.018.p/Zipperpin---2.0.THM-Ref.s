%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JuD9McD1tH

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:44 EST 2020

% Result     : Theorem 2.43s
% Output     : Refutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 298 expanded)
%              Number of leaves         :   32 ( 104 expanded)
%              Depth                    :   25
%              Number of atoms          : 2291 (4149 expanded)
%              Number of equality atoms :   82 ( 198 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(t46_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t46_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X2 ) @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('5',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('6',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

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

thf('8',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('13',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( X16
        = ( sk_D @ X14 @ X13 @ X16 ) )
      | ~ ( r2_hidden @ X16 @ ( a_2_1_orders_2 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( a_2_1_orders_2 @ X0 @ X1 ) )
      | ( X2
        = ( sk_D @ X1 @ X0 @ X2 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( X1
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
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
    inference('sup-',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','18'])).

thf('20',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('23',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('24',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('25',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X14 @ X13 @ X16 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_hidden @ X16 @ ( a_2_1_orders_2 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( a_2_1_orders_2 @ X0 @ X1 ) )
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
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
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
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['20','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('35',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','18'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','29'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('44',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('46',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X13 ) )
      | ( r2_orders_2 @ X13 @ ( sk_D @ X14 @ X13 @ X16 ) @ X15 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( r2_hidden @ X16 @ ( a_2_1_orders_2 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ X1 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['36','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('59',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('61',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('62',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( X16
        = ( sk_D @ X14 @ X13 @ X16 ) )
      | ~ ( r2_hidden @ X16 @ ( a_2_1_orders_2 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
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
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( X1
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('69',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('71',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('72',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X14 @ X13 @ X16 ) @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_hidden @ X16 @ ( a_2_1_orders_2 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
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
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['69','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','76'])).

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

thf('78',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r2_orders_2 @ X8 @ X7 @ X9 )
      | ( X7 != X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('79',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ~ ( r2_orders_2 @ X8 @ X9 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['67','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
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
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('89',plain,(
    ! [X12: $i] :
      ( ( l1_struct_0 @ X12 )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('90',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['87','90','91','92','93','94'])).

thf('96',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('100',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('101',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['98','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['88','89'])).

thf('105',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    $false ),
    inference(demod,[status(thm)],['0','105'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.JuD9McD1tH
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:20:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.43/2.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.43/2.60  % Solved by: fo/fo7.sh
% 2.43/2.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.43/2.60  % done 3124 iterations in 2.145s
% 2.43/2.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.43/2.60  % SZS output start Refutation
% 2.43/2.60  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 2.43/2.60  thf(sk_B_type, type, sk_B: $i > $i).
% 2.43/2.60  thf(sk_A_type, type, sk_A: $i).
% 2.43/2.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.43/2.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 2.43/2.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.43/2.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.43/2.60  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 2.43/2.60  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 2.43/2.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.43/2.60  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 2.43/2.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.43/2.60  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 2.43/2.60  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 2.43/2.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.43/2.60  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 2.43/2.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 2.43/2.60  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 2.43/2.60  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 2.43/2.60  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 2.43/2.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 2.43/2.60  thf(t46_orders_2, conjecture,
% 2.43/2.60    (![A:$i]:
% 2.43/2.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 2.43/2.60         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 2.43/2.60       ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 2.43/2.60  thf(zf_stmt_0, negated_conjecture,
% 2.43/2.60    (~( ![A:$i]:
% 2.43/2.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 2.43/2.60            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 2.43/2.60          ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 2.43/2.60    inference('cnf.neg', [status(esa)], [t46_orders_2])).
% 2.43/2.60  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 2.43/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.60  thf(t7_xboole_0, axiom,
% 2.43/2.60    (![A:$i]:
% 2.43/2.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 2.43/2.60          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 2.43/2.60  thf('1', plain,
% 2.43/2.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 2.43/2.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.43/2.60  thf(d3_struct_0, axiom,
% 2.43/2.60    (![A:$i]:
% 2.43/2.60     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 2.43/2.60  thf('2', plain,
% 2.43/2.60      (![X5 : $i]:
% 2.43/2.60         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 2.43/2.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.43/2.60  thf('3', plain,
% 2.43/2.60      (![X5 : $i]:
% 2.43/2.60         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 2.43/2.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.43/2.60  thf(dt_k2_subset_1, axiom,
% 2.43/2.60    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 2.43/2.60  thf('4', plain,
% 2.43/2.60      (![X2 : $i]: (m1_subset_1 @ (k2_subset_1 @ X2) @ (k1_zfmisc_1 @ X2))),
% 2.43/2.60      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 2.43/2.60  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 2.43/2.60  thf('5', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 2.43/2.60      inference('cnf', [status(esa)], [d4_subset_1])).
% 2.43/2.60  thf('6', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 2.43/2.60      inference('demod', [status(thm)], ['4', '5'])).
% 2.43/2.60  thf(d13_orders_2, axiom,
% 2.43/2.60    (![A:$i]:
% 2.43/2.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 2.43/2.60         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 2.43/2.60       ( ![B:$i]:
% 2.43/2.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 2.43/2.60           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 2.43/2.60  thf('7', plain,
% 2.43/2.60      (![X10 : $i, X11 : $i]:
% 2.43/2.60         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 2.43/2.60          | ((k2_orders_2 @ X11 @ X10) = (a_2_1_orders_2 @ X11 @ X10))
% 2.43/2.60          | ~ (l1_orders_2 @ X11)
% 2.43/2.60          | ~ (v5_orders_2 @ X11)
% 2.43/2.60          | ~ (v4_orders_2 @ X11)
% 2.43/2.60          | ~ (v3_orders_2 @ X11)
% 2.43/2.60          | (v2_struct_0 @ X11))),
% 2.43/2.60      inference('cnf', [status(esa)], [d13_orders_2])).
% 2.43/2.60  thf('8', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         ((v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 2.43/2.60              = (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 2.43/2.60      inference('sup-', [status(thm)], ['6', '7'])).
% 2.43/2.60  thf('9', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 2.43/2.60            = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0))),
% 2.43/2.60      inference('sup+', [status(thm)], ['3', '8'])).
% 2.43/2.60  thf('10', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 2.43/2.60            = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0))),
% 2.43/2.60      inference('sup+', [status(thm)], ['2', '9'])).
% 2.43/2.60  thf('11', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 2.43/2.60              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 2.43/2.60      inference('simplify', [status(thm)], ['10'])).
% 2.43/2.60  thf('12', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 2.43/2.60      inference('demod', [status(thm)], ['4', '5'])).
% 2.43/2.60  thf('13', plain,
% 2.43/2.60      (![X5 : $i]:
% 2.43/2.60         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 2.43/2.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.43/2.60  thf(fraenkel_a_2_1_orders_2, axiom,
% 2.43/2.60    (![A:$i,B:$i,C:$i]:
% 2.43/2.60     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 2.43/2.60         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 2.43/2.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 2.43/2.60       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 2.43/2.60         ( ?[D:$i]:
% 2.43/2.60           ( ( ![E:$i]:
% 2.43/2.60               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 2.43/2.60                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 2.43/2.60             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 2.43/2.60  thf('14', plain,
% 2.43/2.60      (![X13 : $i, X14 : $i, X16 : $i]:
% 2.43/2.60         (~ (l1_orders_2 @ X13)
% 2.43/2.60          | ~ (v5_orders_2 @ X13)
% 2.43/2.60          | ~ (v4_orders_2 @ X13)
% 2.43/2.60          | ~ (v3_orders_2 @ X13)
% 2.43/2.60          | (v2_struct_0 @ X13)
% 2.43/2.60          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 2.43/2.60          | ((X16) = (sk_D @ X14 @ X13 @ X16))
% 2.43/2.60          | ~ (r2_hidden @ X16 @ (a_2_1_orders_2 @ X13 @ X14)))),
% 2.43/2.60      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 2.43/2.60  thf('15', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.43/2.60         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ~ (r2_hidden @ X2 @ (a_2_1_orders_2 @ X0 @ X1))
% 2.43/2.60          | ((X2) = (sk_D @ X1 @ X0 @ X2))
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0))),
% 2.43/2.60      inference('sup-', [status(thm)], ['13', '14'])).
% 2.43/2.60  thf('16', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i]:
% 2.43/2.60         (~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 2.43/2.60          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 2.43/2.60          | ~ (l1_struct_0 @ X0))),
% 2.43/2.60      inference('sup-', [status(thm)], ['12', '15'])).
% 2.43/2.60  thf('17', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i]:
% 2.43/2.60         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0))),
% 2.43/2.60      inference('sup-', [status(thm)], ['11', '16'])).
% 2.43/2.60  thf('18', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i]:
% 2.43/2.60         (((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 2.43/2.60      inference('simplify', [status(thm)], ['17'])).
% 2.43/2.60  thf('19', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 2.43/2.60              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 2.43/2.60                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 2.43/2.60      inference('sup-', [status(thm)], ['1', '18'])).
% 2.43/2.60  thf('20', plain,
% 2.43/2.60      (![X5 : $i]:
% 2.43/2.60         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 2.43/2.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.43/2.60  thf('21', plain,
% 2.43/2.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 2.43/2.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.43/2.60  thf('22', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 2.43/2.60              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 2.43/2.60      inference('simplify', [status(thm)], ['10'])).
% 2.43/2.60  thf('23', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 2.43/2.60      inference('demod', [status(thm)], ['4', '5'])).
% 2.43/2.60  thf('24', plain,
% 2.43/2.60      (![X5 : $i]:
% 2.43/2.60         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 2.43/2.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.43/2.60  thf('25', plain,
% 2.43/2.60      (![X13 : $i, X14 : $i, X16 : $i]:
% 2.43/2.60         (~ (l1_orders_2 @ X13)
% 2.43/2.60          | ~ (v5_orders_2 @ X13)
% 2.43/2.60          | ~ (v4_orders_2 @ X13)
% 2.43/2.60          | ~ (v3_orders_2 @ X13)
% 2.43/2.60          | (v2_struct_0 @ X13)
% 2.43/2.60          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 2.43/2.60          | (m1_subset_1 @ (sk_D @ X14 @ X13 @ X16) @ (u1_struct_0 @ X13))
% 2.43/2.60          | ~ (r2_hidden @ X16 @ (a_2_1_orders_2 @ X13 @ X14)))),
% 2.43/2.60      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 2.43/2.60  thf('26', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.43/2.60         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ~ (r2_hidden @ X2 @ (a_2_1_orders_2 @ X0 @ X1))
% 2.43/2.60          | (m1_subset_1 @ (sk_D @ X1 @ X0 @ X2) @ (u1_struct_0 @ X0))
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0))),
% 2.43/2.60      inference('sup-', [status(thm)], ['24', '25'])).
% 2.43/2.60  thf('27', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i]:
% 2.43/2.60         (~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 2.43/2.60             (u1_struct_0 @ X0))
% 2.43/2.60          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 2.43/2.60          | ~ (l1_struct_0 @ X0))),
% 2.43/2.60      inference('sup-', [status(thm)], ['23', '26'])).
% 2.43/2.60  thf('28', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i]:
% 2.43/2.60         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 2.43/2.60             (u1_struct_0 @ X0))
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0))),
% 2.43/2.60      inference('sup-', [status(thm)], ['22', '27'])).
% 2.43/2.60  thf('29', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i]:
% 2.43/2.60         ((m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 2.43/2.60           (u1_struct_0 @ X0))
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 2.43/2.60      inference('simplify', [status(thm)], ['28'])).
% 2.43/2.60  thf('30', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | (m1_subset_1 @ 
% 2.43/2.60             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 2.43/2.60              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 2.43/2.60             (u1_struct_0 @ X0)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['21', '29'])).
% 2.43/2.60  thf('31', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         ((m1_subset_1 @ 
% 2.43/2.60           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 2.43/2.60            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 2.43/2.60           (k2_struct_0 @ X0))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 2.43/2.60      inference('sup+', [status(thm)], ['20', '30'])).
% 2.43/2.60  thf('32', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | (m1_subset_1 @ 
% 2.43/2.60             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 2.43/2.60              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 2.43/2.60             (k2_struct_0 @ X0)))),
% 2.43/2.60      inference('simplify', [status(thm)], ['31'])).
% 2.43/2.60  thf('33', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 2.43/2.60           (k2_struct_0 @ X0))
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 2.43/2.60      inference('sup+', [status(thm)], ['19', '32'])).
% 2.43/2.60  thf('34', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 2.43/2.60             (k2_struct_0 @ X0)))),
% 2.43/2.60      inference('simplify', [status(thm)], ['33'])).
% 2.43/2.60  thf(t2_subset, axiom,
% 2.43/2.60    (![A:$i,B:$i]:
% 2.43/2.60     ( ( m1_subset_1 @ A @ B ) =>
% 2.43/2.60       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 2.43/2.60  thf('35', plain,
% 2.43/2.60      (![X3 : $i, X4 : $i]:
% 2.43/2.60         ((r2_hidden @ X3 @ X4)
% 2.43/2.60          | (v1_xboole_0 @ X4)
% 2.43/2.60          | ~ (m1_subset_1 @ X3 @ X4))),
% 2.43/2.60      inference('cnf', [status(esa)], [t2_subset])).
% 2.43/2.60  thf('36', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 2.43/2.60          | (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 2.43/2.60             (k2_struct_0 @ X0)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['34', '35'])).
% 2.43/2.60  thf('37', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 2.43/2.60              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 2.43/2.60                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 2.43/2.60      inference('sup-', [status(thm)], ['1', '18'])).
% 2.43/2.60  thf('38', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | (m1_subset_1 @ 
% 2.43/2.60             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 2.43/2.60              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 2.43/2.60             (u1_struct_0 @ X0)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['21', '29'])).
% 2.43/2.60  thf('39', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 2.43/2.60           (u1_struct_0 @ X0))
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 2.43/2.60      inference('sup+', [status(thm)], ['37', '38'])).
% 2.43/2.60  thf('40', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 2.43/2.60             (u1_struct_0 @ X0)))),
% 2.43/2.60      inference('simplify', [status(thm)], ['39'])).
% 2.43/2.60  thf('41', plain,
% 2.43/2.60      (![X5 : $i]:
% 2.43/2.60         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 2.43/2.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.43/2.60  thf('42', plain,
% 2.43/2.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 2.43/2.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.43/2.60  thf('43', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 2.43/2.60              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 2.43/2.60      inference('simplify', [status(thm)], ['10'])).
% 2.43/2.60  thf('44', plain,
% 2.43/2.60      (![X5 : $i]:
% 2.43/2.60         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 2.43/2.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.43/2.60  thf('45', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 2.43/2.60      inference('demod', [status(thm)], ['4', '5'])).
% 2.43/2.60  thf('46', plain,
% 2.43/2.60      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 2.43/2.60         (~ (l1_orders_2 @ X13)
% 2.43/2.60          | ~ (v5_orders_2 @ X13)
% 2.43/2.60          | ~ (v4_orders_2 @ X13)
% 2.43/2.60          | ~ (v3_orders_2 @ X13)
% 2.43/2.60          | (v2_struct_0 @ X13)
% 2.43/2.60          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 2.43/2.60          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X13))
% 2.43/2.60          | (r2_orders_2 @ X13 @ (sk_D @ X14 @ X13 @ X16) @ X15)
% 2.43/2.60          | ~ (r2_hidden @ X15 @ X14)
% 2.43/2.60          | ~ (r2_hidden @ X16 @ (a_2_1_orders_2 @ X13 @ X14)))),
% 2.43/2.60      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 2.43/2.60  thf('47', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.43/2.60         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 2.43/2.60          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 2.43/2.60          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 2.43/2.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0))),
% 2.43/2.60      inference('sup-', [status(thm)], ['45', '46'])).
% 2.43/2.60  thf('48', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.43/2.60         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.43/2.60          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 2.43/2.60          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['44', '47'])).
% 2.43/2.60  thf('49', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.43/2.60         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 2.43/2.60          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 2.43/2.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0))),
% 2.43/2.60      inference('sup-', [status(thm)], ['43', '48'])).
% 2.43/2.60  thf('50', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.43/2.60         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 2.43/2.60          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 2.43/2.60          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 2.43/2.60      inference('simplify', [status(thm)], ['49'])).
% 2.43/2.60  thf('51', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i]:
% 2.43/2.60         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 2.43/2.60          | (r2_orders_2 @ X0 @ 
% 2.43/2.60             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 2.43/2.60              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 2.43/2.60             X1)
% 2.43/2.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['42', '50'])).
% 2.43/2.60  thf('52', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i]:
% 2.43/2.60         (~ (r2_hidden @ X1 @ (k2_struct_0 @ X0))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 2.43/2.60          | (r2_orders_2 @ X0 @ 
% 2.43/2.60             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 2.43/2.60              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 2.43/2.60             X1)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['41', '51'])).
% 2.43/2.60  thf('53', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i]:
% 2.43/2.60         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | (r2_orders_2 @ X0 @ 
% 2.43/2.60             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 2.43/2.60              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 2.43/2.60             X1)
% 2.43/2.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0)))),
% 2.43/2.60      inference('simplify', [status(thm)], ['52'])).
% 2.43/2.60  thf('54', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 2.43/2.60               (k2_struct_0 @ X0))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | (r2_orders_2 @ X0 @ 
% 2.43/2.60             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 2.43/2.60              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 2.43/2.60             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['40', '53'])).
% 2.43/2.60  thf('55', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         ((r2_orders_2 @ X0 @ 
% 2.43/2.60           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 2.43/2.60            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 2.43/2.60           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 2.43/2.60          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 2.43/2.60               (k2_struct_0 @ X0))
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0))),
% 2.43/2.60      inference('simplify', [status(thm)], ['54'])).
% 2.43/2.60  thf('56', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | (r2_orders_2 @ X0 @ 
% 2.43/2.60             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 2.43/2.60              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 2.43/2.60             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 2.43/2.60      inference('sup-', [status(thm)], ['36', '55'])).
% 2.43/2.60  thf('57', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         ((r2_orders_2 @ X0 @ 
% 2.43/2.60           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 2.43/2.60            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 2.43/2.60           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 2.43/2.60      inference('simplify', [status(thm)], ['56'])).
% 2.43/2.60  thf('58', plain,
% 2.43/2.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 2.43/2.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.43/2.60  thf('59', plain,
% 2.43/2.60      (![X5 : $i]:
% 2.43/2.60         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 2.43/2.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.43/2.60  thf('60', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         ((v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 2.43/2.60              = (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 2.43/2.60      inference('sup-', [status(thm)], ['6', '7'])).
% 2.43/2.60  thf('61', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 2.43/2.60      inference('demod', [status(thm)], ['4', '5'])).
% 2.43/2.60  thf('62', plain,
% 2.43/2.60      (![X13 : $i, X14 : $i, X16 : $i]:
% 2.43/2.60         (~ (l1_orders_2 @ X13)
% 2.43/2.60          | ~ (v5_orders_2 @ X13)
% 2.43/2.60          | ~ (v4_orders_2 @ X13)
% 2.43/2.60          | ~ (v3_orders_2 @ X13)
% 2.43/2.60          | (v2_struct_0 @ X13)
% 2.43/2.60          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 2.43/2.60          | ((X16) = (sk_D @ X14 @ X13 @ X16))
% 2.43/2.60          | ~ (r2_hidden @ X16 @ (a_2_1_orders_2 @ X13 @ X14)))),
% 2.43/2.60      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 2.43/2.60  thf('63', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i]:
% 2.43/2.60         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 2.43/2.60          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0))),
% 2.43/2.60      inference('sup-', [status(thm)], ['61', '62'])).
% 2.43/2.60  thf('64', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i]:
% 2.43/2.60         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['60', '63'])).
% 2.43/2.60  thf('65', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i]:
% 2.43/2.60         (((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 2.43/2.60      inference('simplify', [status(thm)], ['64'])).
% 2.43/2.60  thf('66', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i]:
% 2.43/2.60         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['59', '65'])).
% 2.43/2.60  thf('67', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 2.43/2.60              = (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 2.43/2.60                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0))),
% 2.43/2.60      inference('sup-', [status(thm)], ['58', '66'])).
% 2.43/2.60  thf('68', plain,
% 2.43/2.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 2.43/2.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 2.43/2.60  thf('69', plain,
% 2.43/2.60      (![X5 : $i]:
% 2.43/2.60         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 2.43/2.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.43/2.60  thf('70', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         ((v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 2.43/2.60              = (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 2.43/2.60      inference('sup-', [status(thm)], ['6', '7'])).
% 2.43/2.60  thf('71', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 2.43/2.60      inference('demod', [status(thm)], ['4', '5'])).
% 2.43/2.60  thf('72', plain,
% 2.43/2.60      (![X13 : $i, X14 : $i, X16 : $i]:
% 2.43/2.60         (~ (l1_orders_2 @ X13)
% 2.43/2.60          | ~ (v5_orders_2 @ X13)
% 2.43/2.60          | ~ (v4_orders_2 @ X13)
% 2.43/2.60          | ~ (v3_orders_2 @ X13)
% 2.43/2.60          | (v2_struct_0 @ X13)
% 2.43/2.60          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 2.43/2.60          | (m1_subset_1 @ (sk_D @ X14 @ X13 @ X16) @ (u1_struct_0 @ X13))
% 2.43/2.60          | ~ (r2_hidden @ X16 @ (a_2_1_orders_2 @ X13 @ X14)))),
% 2.43/2.60      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 2.43/2.60  thf('73', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i]:
% 2.43/2.60         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 2.43/2.60          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 2.43/2.60             (u1_struct_0 @ X0))
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0))),
% 2.43/2.60      inference('sup-', [status(thm)], ['71', '72'])).
% 2.43/2.60  thf('74', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i]:
% 2.43/2.60         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 2.43/2.60             (u1_struct_0 @ X0)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['70', '73'])).
% 2.43/2.60  thf('75', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i]:
% 2.43/2.60         ((m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 2.43/2.60           (u1_struct_0 @ X0))
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 2.43/2.60      inference('simplify', [status(thm)], ['74'])).
% 2.43/2.60  thf('76', plain,
% 2.43/2.60      (![X0 : $i, X1 : $i]:
% 2.43/2.60         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 2.43/2.60             (u1_struct_0 @ X0)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['69', '75'])).
% 2.43/2.60  thf('77', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | (m1_subset_1 @ 
% 2.43/2.60             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 2.43/2.60              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 2.43/2.60             (u1_struct_0 @ X0))
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0))),
% 2.43/2.60      inference('sup-', [status(thm)], ['68', '76'])).
% 2.43/2.60  thf(d10_orders_2, axiom,
% 2.43/2.60    (![A:$i]:
% 2.43/2.60     ( ( l1_orders_2 @ A ) =>
% 2.43/2.60       ( ![B:$i]:
% 2.43/2.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 2.43/2.60           ( ![C:$i]:
% 2.43/2.60             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 2.43/2.60               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 2.43/2.60                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 2.43/2.60  thf('78', plain,
% 2.43/2.60      (![X7 : $i, X8 : $i, X9 : $i]:
% 2.43/2.60         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 2.43/2.60          | ~ (r2_orders_2 @ X8 @ X7 @ X9)
% 2.43/2.60          | ((X7) != (X9))
% 2.43/2.60          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 2.43/2.60          | ~ (l1_orders_2 @ X8))),
% 2.43/2.60      inference('cnf', [status(esa)], [d10_orders_2])).
% 2.43/2.60  thf('79', plain,
% 2.43/2.60      (![X8 : $i, X9 : $i]:
% 2.43/2.60         (~ (l1_orders_2 @ X8)
% 2.43/2.60          | ~ (r2_orders_2 @ X8 @ X9 @ X9)
% 2.43/2.60          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8)))),
% 2.43/2.60      inference('simplify', [status(thm)], ['78'])).
% 2.43/2.60  thf('80', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (~ (l1_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | ~ (r2_orders_2 @ X0 @ 
% 2.43/2.60               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 2.43/2.60                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 2.43/2.60               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 2.43/2.60                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 2.43/2.60          | ~ (l1_orders_2 @ X0))),
% 2.43/2.60      inference('sup-', [status(thm)], ['77', '79'])).
% 2.43/2.60  thf('81', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (~ (r2_orders_2 @ X0 @ 
% 2.43/2.60             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 2.43/2.60              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 2.43/2.60             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 2.43/2.60              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0))),
% 2.43/2.60      inference('simplify', [status(thm)], ['80'])).
% 2.43/2.60  thf('82', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (~ (r2_orders_2 @ X0 @ 
% 2.43/2.60             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 2.43/2.60              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 2.43/2.60             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['67', '81'])).
% 2.43/2.60  thf('83', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ~ (r2_orders_2 @ X0 @ 
% 2.43/2.60               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 2.43/2.60                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 2.43/2.60               (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 2.43/2.60      inference('simplify', [status(thm)], ['82'])).
% 2.43/2.60  thf('84', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 2.43/2.60      inference('sup-', [status(thm)], ['57', '83'])).
% 2.43/2.60  thf('85', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (~ (l1_orders_2 @ X0)
% 2.43/2.60          | ~ (v5_orders_2 @ X0)
% 2.43/2.60          | ~ (v4_orders_2 @ X0)
% 2.43/2.60          | ~ (v3_orders_2 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 2.43/2.60          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 2.43/2.60      inference('simplify', [status(thm)], ['84'])).
% 2.43/2.60  thf('86', plain,
% 2.43/2.60      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 2.43/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.60  thf('87', plain,
% 2.43/2.60      ((((k1_xboole_0) != (k1_xboole_0))
% 2.43/2.60        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 2.43/2.60        | ~ (l1_struct_0 @ sk_A)
% 2.43/2.60        | (v2_struct_0 @ sk_A)
% 2.43/2.60        | ~ (v3_orders_2 @ sk_A)
% 2.43/2.60        | ~ (v4_orders_2 @ sk_A)
% 2.43/2.60        | ~ (v5_orders_2 @ sk_A)
% 2.43/2.60        | ~ (l1_orders_2 @ sk_A))),
% 2.43/2.60      inference('sup-', [status(thm)], ['85', '86'])).
% 2.43/2.60  thf('88', plain, ((l1_orders_2 @ sk_A)),
% 2.43/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.60  thf(dt_l1_orders_2, axiom,
% 2.43/2.60    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 2.43/2.60  thf('89', plain,
% 2.43/2.60      (![X12 : $i]: ((l1_struct_0 @ X12) | ~ (l1_orders_2 @ X12))),
% 2.43/2.60      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 2.43/2.60  thf('90', plain, ((l1_struct_0 @ sk_A)),
% 2.43/2.60      inference('sup-', [status(thm)], ['88', '89'])).
% 2.43/2.60  thf('91', plain, ((v3_orders_2 @ sk_A)),
% 2.43/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.60  thf('92', plain, ((v4_orders_2 @ sk_A)),
% 2.43/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.60  thf('93', plain, ((v5_orders_2 @ sk_A)),
% 2.43/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.60  thf('94', plain, ((l1_orders_2 @ sk_A)),
% 2.43/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.60  thf('95', plain,
% 2.43/2.60      ((((k1_xboole_0) != (k1_xboole_0))
% 2.43/2.60        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 2.43/2.60        | (v2_struct_0 @ sk_A))),
% 2.43/2.60      inference('demod', [status(thm)], ['87', '90', '91', '92', '93', '94'])).
% 2.43/2.60  thf('96', plain,
% 2.43/2.60      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 2.43/2.60      inference('simplify', [status(thm)], ['95'])).
% 2.43/2.60  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 2.43/2.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.43/2.60  thf('98', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 2.43/2.60      inference('clc', [status(thm)], ['96', '97'])).
% 2.43/2.60  thf('99', plain,
% 2.43/2.60      (![X5 : $i]:
% 2.43/2.60         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 2.43/2.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 2.43/2.60  thf(fc2_struct_0, axiom,
% 2.43/2.60    (![A:$i]:
% 2.43/2.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 2.43/2.60       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 2.43/2.60  thf('100', plain,
% 2.43/2.60      (![X6 : $i]:
% 2.43/2.60         (~ (v1_xboole_0 @ (u1_struct_0 @ X6))
% 2.43/2.60          | ~ (l1_struct_0 @ X6)
% 2.43/2.60          | (v2_struct_0 @ X6))),
% 2.43/2.60      inference('cnf', [status(esa)], [fc2_struct_0])).
% 2.43/2.60  thf('101', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | (v2_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0))),
% 2.43/2.60      inference('sup-', [status(thm)], ['99', '100'])).
% 2.43/2.60  thf('102', plain,
% 2.43/2.60      (![X0 : $i]:
% 2.43/2.60         ((v2_struct_0 @ X0)
% 2.43/2.60          | ~ (l1_struct_0 @ X0)
% 2.43/2.60          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 2.43/2.60      inference('simplify', [status(thm)], ['101'])).
% 2.43/2.60  thf('103', plain, ((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 2.43/2.60      inference('sup-', [status(thm)], ['98', '102'])).
% 2.43/2.60  thf('104', plain, ((l1_struct_0 @ sk_A)),
% 2.43/2.60      inference('sup-', [status(thm)], ['88', '89'])).
% 2.43/2.60  thf('105', plain, ((v2_struct_0 @ sk_A)),
% 2.43/2.60      inference('demod', [status(thm)], ['103', '104'])).
% 2.43/2.60  thf('106', plain, ($false), inference('demod', [status(thm)], ['0', '105'])).
% 2.43/2.60  
% 2.43/2.60  % SZS output end Refutation
% 2.43/2.60  
% 2.43/2.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
