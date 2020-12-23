%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3tZqCSQ9oy

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:43 EST 2020

% Result     : Theorem 0.82s
% Output     : Refutation 0.82s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 186 expanded)
%              Number of leaves         :   31 (  69 expanded)
%              Depth                    :   20
%              Number of atoms          : 1607 (3263 expanded)
%              Number of equality atoms :   55 ( 119 expanded)
%              Maximal formula depth    :   24 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

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

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

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

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( k2_orders_2 @ X13 @ X12 )
        = ( a_2_1_orders_2 @ X13 @ X12 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

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

thf('7',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( X18
        = ( sk_D @ X16 @ X15 @ X18 ) )
      | ~ ( r2_hidden @ X18 @ ( a_2_1_orders_2 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ( X1
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( X1
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('14',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('15',plain,(
    ! [X15: $i,X16: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X16 @ X15 @ X18 ) @ ( u1_struct_0 @ X15 ) )
      | ~ ( r2_hidden @ X18 @ ( a_2_1_orders_2 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['11','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('27',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('29',plain,(
    ! [X7: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X7 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X7 ) ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X17 @ ( u1_struct_0 @ X15 ) )
      | ( r2_orders_2 @ X15 @ ( sk_D @ X16 @ X15 @ X18 ) @ X17 )
      | ~ ( r2_hidden @ X17 @ X16 )
      | ~ ( r2_hidden @ X18 @ ( a_2_1_orders_2 @ X15 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X2 @ ( k2_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ X2 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ X1 )
      | ~ ( r2_hidden @ X1 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['25','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

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

thf('41',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r2_orders_2 @ X10 @ X9 @ X11 )
      | ( X9 != X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ~ ( r2_orders_2 @ X10 @ X11 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
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

thf('50',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('62',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('63',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57','58','59','60','63'])).

thf('65',plain,(
    v2_struct_0 @ sk_A ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['0','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3tZqCSQ9oy
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:38:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.82/0.99  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.82/0.99  % Solved by: fo/fo7.sh
% 0.82/0.99  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.82/0.99  % done 494 iterations in 0.532s
% 0.82/0.99  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.82/0.99  % SZS output start Refutation
% 0.82/0.99  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.82/0.99  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.82/0.99  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.82/0.99  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.82/0.99  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.82/0.99  thf(sk_B_type, type, sk_B: $i > $i).
% 0.82/0.99  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.82/0.99  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.82/0.99  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.82/0.99  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.82/0.99  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 0.82/0.99  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.82/0.99  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.82/0.99  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.82/0.99  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.82/0.99  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.82/0.99  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.82/0.99  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.82/0.99  thf(sk_A_type, type, sk_A: $i).
% 0.82/0.99  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.82/0.99  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.82/0.99  thf(t46_orders_2, conjecture,
% 0.82/0.99    (![A:$i]:
% 0.82/0.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.82/0.99         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.82/0.99       ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 0.82/0.99  thf(zf_stmt_0, negated_conjecture,
% 0.82/0.99    (~( ![A:$i]:
% 0.82/0.99        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.82/0.99            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.82/0.99          ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 0.82/0.99    inference('cnf.neg', [status(esa)], [t46_orders_2])).
% 0.82/0.99  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.82/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/0.99  thf(d3_struct_0, axiom,
% 0.82/0.99    (![A:$i]:
% 0.82/0.99     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.82/0.99  thf('1', plain,
% 0.82/0.99      (![X6 : $i]:
% 0.82/0.99         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.82/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.82/0.99  thf(t9_mcart_1, axiom,
% 0.82/0.99    (![A:$i]:
% 0.82/0.99     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.82/0.99          ( ![B:$i]:
% 0.82/0.99            ( ~( ( r2_hidden @ B @ A ) & 
% 0.82/0.99                 ( ![C:$i,D:$i]:
% 0.82/0.99                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.82/0.99                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.82/0.99  thf('2', plain,
% 0.82/0.99      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X3) @ X3))),
% 0.82/0.99      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.82/0.99  thf(dt_k2_struct_0, axiom,
% 0.82/0.99    (![A:$i]:
% 0.82/0.99     ( ( l1_struct_0 @ A ) =>
% 0.82/0.99       ( m1_subset_1 @
% 0.82/0.99         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.82/0.99  thf('3', plain,
% 0.82/0.99      (![X7 : $i]:
% 0.82/0.99         ((m1_subset_1 @ (k2_struct_0 @ X7) @ 
% 0.82/0.99           (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.82/0.99          | ~ (l1_struct_0 @ X7))),
% 0.82/0.99      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.82/0.99  thf(d13_orders_2, axiom,
% 0.82/0.99    (![A:$i]:
% 0.82/0.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.82/0.99         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.82/0.99       ( ![B:$i]:
% 0.82/0.99         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.82/0.99           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 0.82/0.99  thf('4', plain,
% 0.82/0.99      (![X12 : $i, X13 : $i]:
% 0.82/0.99         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.82/0.99          | ((k2_orders_2 @ X13 @ X12) = (a_2_1_orders_2 @ X13 @ X12))
% 0.82/0.99          | ~ (l1_orders_2 @ X13)
% 0.82/0.99          | ~ (v5_orders_2 @ X13)
% 0.82/0.99          | ~ (v4_orders_2 @ X13)
% 0.82/0.99          | ~ (v3_orders_2 @ X13)
% 0.82/0.99          | (v2_struct_0 @ X13))),
% 0.82/0.99      inference('cnf', [status(esa)], [d13_orders_2])).
% 0.82/0.99  thf('5', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 0.82/0.99              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.82/0.99      inference('sup-', [status(thm)], ['3', '4'])).
% 0.82/0.99  thf('6', plain,
% 0.82/0.99      (![X7 : $i]:
% 0.82/0.99         ((m1_subset_1 @ (k2_struct_0 @ X7) @ 
% 0.82/0.99           (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.82/0.99          | ~ (l1_struct_0 @ X7))),
% 0.82/0.99      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.82/0.99  thf(fraenkel_a_2_1_orders_2, axiom,
% 0.82/0.99    (![A:$i,B:$i,C:$i]:
% 0.82/0.99     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.82/0.99         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.82/0.99         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.82/0.99       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 0.82/0.99         ( ?[D:$i]:
% 0.82/0.99           ( ( ![E:$i]:
% 0.82/0.99               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.82/0.99                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 0.82/0.99             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.82/0.99  thf('7', plain,
% 0.82/0.99      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.82/0.99         (~ (l1_orders_2 @ X15)
% 0.82/0.99          | ~ (v5_orders_2 @ X15)
% 0.82/0.99          | ~ (v4_orders_2 @ X15)
% 0.82/0.99          | ~ (v3_orders_2 @ X15)
% 0.82/0.99          | (v2_struct_0 @ X15)
% 0.82/0.99          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.82/0.99          | ((X18) = (sk_D @ X16 @ X15 @ X18))
% 0.82/0.99          | ~ (r2_hidden @ X18 @ (a_2_1_orders_2 @ X15 @ X16)))),
% 0.82/0.99      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.82/0.99  thf('8', plain,
% 0.82/0.99      (![X0 : $i, X1 : $i]:
% 0.82/0.99         (~ (l1_struct_0 @ X0)
% 0.82/0.99          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.82/0.99          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0))),
% 0.82/0.99      inference('sup-', [status(thm)], ['6', '7'])).
% 0.82/0.99  thf('9', plain,
% 0.82/0.99      (![X0 : $i, X1 : $i]:
% 0.82/0.99         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 0.82/0.99          | ~ (l1_struct_0 @ X0))),
% 0.82/0.99      inference('sup-', [status(thm)], ['5', '8'])).
% 0.82/0.99  thf('10', plain,
% 0.82/0.99      (![X0 : $i, X1 : $i]:
% 0.82/0.99         (((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.82/0.99      inference('simplify', [status(thm)], ['9'])).
% 0.82/0.99  thf('11', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.82/0.99              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.82/0.99                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 0.82/0.99      inference('sup-', [status(thm)], ['2', '10'])).
% 0.82/0.99  thf('12', plain,
% 0.82/0.99      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X3) @ X3))),
% 0.82/0.99      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.82/0.99  thf('13', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 0.82/0.99              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.82/0.99      inference('sup-', [status(thm)], ['3', '4'])).
% 0.82/0.99  thf('14', plain,
% 0.82/0.99      (![X7 : $i]:
% 0.82/0.99         ((m1_subset_1 @ (k2_struct_0 @ X7) @ 
% 0.82/0.99           (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.82/0.99          | ~ (l1_struct_0 @ X7))),
% 0.82/0.99      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.82/0.99  thf('15', plain,
% 0.82/0.99      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.82/0.99         (~ (l1_orders_2 @ X15)
% 0.82/0.99          | ~ (v5_orders_2 @ X15)
% 0.82/0.99          | ~ (v4_orders_2 @ X15)
% 0.82/0.99          | ~ (v3_orders_2 @ X15)
% 0.82/0.99          | (v2_struct_0 @ X15)
% 0.82/0.99          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.82/0.99          | (m1_subset_1 @ (sk_D @ X16 @ X15 @ X18) @ (u1_struct_0 @ X15))
% 0.82/0.99          | ~ (r2_hidden @ X18 @ (a_2_1_orders_2 @ X15 @ X16)))),
% 0.82/0.99      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.82/0.99  thf('16', plain,
% 0.82/0.99      (![X0 : $i, X1 : $i]:
% 0.82/0.99         (~ (l1_struct_0 @ X0)
% 0.82/0.99          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.82/0.99          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 0.82/0.99             (u1_struct_0 @ X0))
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0))),
% 0.82/0.99      inference('sup-', [status(thm)], ['14', '15'])).
% 0.82/0.99  thf('17', plain,
% 0.82/0.99      (![X0 : $i, X1 : $i]:
% 0.82/0.99         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 0.82/0.99             (u1_struct_0 @ X0))
% 0.82/0.99          | ~ (l1_struct_0 @ X0))),
% 0.82/0.99      inference('sup-', [status(thm)], ['13', '16'])).
% 0.82/0.99  thf('18', plain,
% 0.82/0.99      (![X0 : $i, X1 : $i]:
% 0.82/0.99         ((m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 0.82/0.99           (u1_struct_0 @ X0))
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.82/0.99      inference('simplify', [status(thm)], ['17'])).
% 0.82/0.99  thf('19', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | (m1_subset_1 @ 
% 0.82/0.99             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.82/0.99              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.82/0.99             (u1_struct_0 @ X0)))),
% 0.82/0.99      inference('sup-', [status(thm)], ['12', '18'])).
% 0.82/0.99  thf('20', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.82/0.99           (u1_struct_0 @ X0))
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.82/0.99      inference('sup+', [status(thm)], ['11', '19'])).
% 0.82/0.99  thf('21', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.82/0.99             (u1_struct_0 @ X0)))),
% 0.82/0.99      inference('simplify', [status(thm)], ['20'])).
% 0.82/0.99  thf('22', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.82/0.99           (k2_struct_0 @ X0))
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.82/0.99      inference('sup+', [status(thm)], ['1', '21'])).
% 0.82/0.99  thf('23', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.82/0.99             (k2_struct_0 @ X0)))),
% 0.82/0.99      inference('simplify', [status(thm)], ['22'])).
% 0.82/0.99  thf(d2_subset_1, axiom,
% 0.82/0.99    (![A:$i,B:$i]:
% 0.82/0.99     ( ( ( v1_xboole_0 @ A ) =>
% 0.82/0.99         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.82/0.99       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.82/0.99         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.82/0.99  thf('24', plain,
% 0.82/0.99      (![X0 : $i, X1 : $i]:
% 0.82/0.99         (~ (m1_subset_1 @ X0 @ X1)
% 0.82/0.99          | (r2_hidden @ X0 @ X1)
% 0.82/0.99          | (v1_xboole_0 @ X1))),
% 0.82/0.99      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.82/0.99  thf('25', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.82/0.99          | (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.82/0.99             (k2_struct_0 @ X0)))),
% 0.82/0.99      inference('sup-', [status(thm)], ['23', '24'])).
% 0.82/0.99  thf('26', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.82/0.99             (u1_struct_0 @ X0)))),
% 0.82/0.99      inference('simplify', [status(thm)], ['20'])).
% 0.82/0.99  thf('27', plain,
% 0.82/0.99      (![X3 : $i]: (((X3) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X3) @ X3))),
% 0.82/0.99      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.82/0.99  thf('28', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 0.82/0.99              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.82/0.99      inference('sup-', [status(thm)], ['3', '4'])).
% 0.82/0.99  thf('29', plain,
% 0.82/0.99      (![X7 : $i]:
% 0.82/0.99         ((m1_subset_1 @ (k2_struct_0 @ X7) @ 
% 0.82/0.99           (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.82/0.99          | ~ (l1_struct_0 @ X7))),
% 0.82/0.99      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.82/0.99  thf('30', plain,
% 0.82/0.99      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.82/0.99         (~ (l1_orders_2 @ X15)
% 0.82/0.99          | ~ (v5_orders_2 @ X15)
% 0.82/0.99          | ~ (v4_orders_2 @ X15)
% 0.82/0.99          | ~ (v3_orders_2 @ X15)
% 0.82/0.99          | (v2_struct_0 @ X15)
% 0.82/0.99          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.82/0.99          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.82/0.99          | (r2_orders_2 @ X15 @ (sk_D @ X16 @ X15 @ X18) @ X17)
% 0.82/0.99          | ~ (r2_hidden @ X17 @ X16)
% 0.82/0.99          | ~ (r2_hidden @ X18 @ (a_2_1_orders_2 @ X15 @ X16)))),
% 0.82/0.99      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.82/0.99  thf('31', plain,
% 0.82/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/0.99         (~ (l1_struct_0 @ X0)
% 0.82/0.99          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.82/0.99          | ~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 0.82/0.99          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 0.82/0.99          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0))),
% 0.82/0.99      inference('sup-', [status(thm)], ['29', '30'])).
% 0.82/0.99  thf('32', plain,
% 0.82/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/0.99         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.82/0.99          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 0.82/0.99          | ~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 0.82/0.99          | ~ (l1_struct_0 @ X0))),
% 0.82/0.99      inference('sup-', [status(thm)], ['28', '31'])).
% 0.82/0.99  thf('33', plain,
% 0.82/0.99      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.82/0.99         (~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 0.82/0.99          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 0.82/0.99          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.82/0.99      inference('simplify', [status(thm)], ['32'])).
% 0.82/0.99  thf('34', plain,
% 0.82/0.99      (![X0 : $i, X1 : $i]:
% 0.82/0.99         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.82/0.99          | (r2_orders_2 @ X0 @ 
% 0.82/0.99             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.82/0.99              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.82/0.99             X1)
% 0.82/0.99          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0)))),
% 0.82/0.99      inference('sup-', [status(thm)], ['27', '33'])).
% 0.82/0.99  thf('35', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.82/0.99               (k2_struct_0 @ X0))
% 0.82/0.99          | (r2_orders_2 @ X0 @ 
% 0.82/0.99             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.82/0.99              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.82/0.99             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.82/0.99      inference('sup-', [status(thm)], ['26', '34'])).
% 0.82/0.99  thf('36', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         ((r2_orders_2 @ X0 @ 
% 0.82/0.99           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.82/0.99            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.82/0.99           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 0.82/0.99          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.82/0.99               (k2_struct_0 @ X0))
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0))),
% 0.82/0.99      inference('simplify', [status(thm)], ['35'])).
% 0.82/0.99  thf('37', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | (r2_orders_2 @ X0 @ 
% 0.82/0.99             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.82/0.99              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.82/0.99             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 0.82/0.99      inference('sup-', [status(thm)], ['25', '36'])).
% 0.82/0.99  thf('38', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         ((r2_orders_2 @ X0 @ 
% 0.82/0.99           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.82/0.99            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.82/0.99           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.82/0.99      inference('simplify', [status(thm)], ['37'])).
% 0.82/0.99  thf('39', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.82/0.99              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.82/0.99                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 0.82/0.99      inference('sup-', [status(thm)], ['2', '10'])).
% 0.82/0.99  thf('40', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | (m1_subset_1 @ 
% 0.82/0.99             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.82/0.99              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.82/0.99             (u1_struct_0 @ X0)))),
% 0.82/0.99      inference('sup-', [status(thm)], ['12', '18'])).
% 0.82/0.99  thf(d10_orders_2, axiom,
% 0.82/0.99    (![A:$i]:
% 0.82/0.99     ( ( l1_orders_2 @ A ) =>
% 0.82/0.99       ( ![B:$i]:
% 0.82/0.99         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.82/0.99           ( ![C:$i]:
% 0.82/0.99             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.82/0.99               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.82/0.99                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 0.82/0.99  thf('41', plain,
% 0.82/0.99      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.82/0.99         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.82/0.99          | ~ (r2_orders_2 @ X10 @ X9 @ X11)
% 0.82/0.99          | ((X9) != (X11))
% 0.82/0.99          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.82/0.99          | ~ (l1_orders_2 @ X10))),
% 0.82/0.99      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.82/0.99  thf('42', plain,
% 0.82/0.99      (![X10 : $i, X11 : $i]:
% 0.82/0.99         (~ (l1_orders_2 @ X10)
% 0.82/0.99          | ~ (r2_orders_2 @ X10 @ X11 @ X11)
% 0.82/0.99          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10)))),
% 0.82/0.99      inference('simplify', [status(thm)], ['41'])).
% 0.82/0.99  thf('43', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | ~ (r2_orders_2 @ X0 @ 
% 0.82/0.99               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.82/0.99                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.82/0.99               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.82/0.99                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 0.82/0.99          | ~ (l1_orders_2 @ X0))),
% 0.82/0.99      inference('sup-', [status(thm)], ['40', '42'])).
% 0.82/0.99  thf('44', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (~ (r2_orders_2 @ X0 @ 
% 0.82/0.99             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.82/0.99              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.82/0.99             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.82/0.99              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0))),
% 0.82/0.99      inference('simplify', [status(thm)], ['43'])).
% 0.82/0.99  thf('45', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (~ (r2_orders_2 @ X0 @ 
% 0.82/0.99             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.82/0.99              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.82/0.99             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.82/0.99      inference('sup-', [status(thm)], ['39', '44'])).
% 0.82/0.99  thf('46', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | ~ (r2_orders_2 @ X0 @ 
% 0.82/0.99               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.82/0.99                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.82/0.99               (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 0.82/0.99      inference('simplify', [status(thm)], ['45'])).
% 0.82/0.99  thf('47', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.82/0.99      inference('sup-', [status(thm)], ['38', '46'])).
% 0.82/0.99  thf('48', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.82/0.99      inference('simplify', [status(thm)], ['47'])).
% 0.82/0.99  thf('49', plain,
% 0.82/0.99      (![X6 : $i]:
% 0.82/0.99         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.82/0.99      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.82/0.99  thf(fc2_struct_0, axiom,
% 0.82/0.99    (![A:$i]:
% 0.82/0.99     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.82/0.99       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.82/0.99  thf('50', plain,
% 0.82/0.99      (![X8 : $i]:
% 0.82/0.99         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.82/0.99          | ~ (l1_struct_0 @ X8)
% 0.82/0.99          | (v2_struct_0 @ X8))),
% 0.82/0.99      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.82/0.99  thf('51', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0))),
% 0.82/0.99      inference('sup-', [status(thm)], ['49', '50'])).
% 0.82/0.99  thf('52', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         ((v2_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.82/0.99      inference('simplify', [status(thm)], ['51'])).
% 0.82/0.99  thf('53', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | ~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0))),
% 0.82/0.99      inference('sup-', [status(thm)], ['48', '52'])).
% 0.82/0.99  thf('54', plain,
% 0.82/0.99      (![X0 : $i]:
% 0.82/0.99         (~ (l1_struct_0 @ X0)
% 0.82/0.99          | (v2_struct_0 @ X0)
% 0.82/0.99          | ~ (v3_orders_2 @ X0)
% 0.82/0.99          | ~ (v4_orders_2 @ X0)
% 0.82/0.99          | ~ (v5_orders_2 @ X0)
% 0.82/0.99          | ~ (l1_orders_2 @ X0)
% 0.82/0.99          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.82/0.99      inference('simplify', [status(thm)], ['53'])).
% 0.82/0.99  thf('55', plain,
% 0.82/0.99      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 0.82/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/0.99  thf('56', plain,
% 0.82/0.99      ((((k1_xboole_0) != (k1_xboole_0))
% 0.82/0.99        | ~ (l1_orders_2 @ sk_A)
% 0.82/0.99        | ~ (v5_orders_2 @ sk_A)
% 0.82/0.99        | ~ (v4_orders_2 @ sk_A)
% 0.82/0.99        | ~ (v3_orders_2 @ sk_A)
% 0.82/0.99        | (v2_struct_0 @ sk_A)
% 0.82/0.99        | ~ (l1_struct_0 @ sk_A))),
% 0.82/0.99      inference('sup-', [status(thm)], ['54', '55'])).
% 0.82/0.99  thf('57', plain, ((l1_orders_2 @ sk_A)),
% 0.82/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/0.99  thf('58', plain, ((v5_orders_2 @ sk_A)),
% 0.82/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/0.99  thf('59', plain, ((v4_orders_2 @ sk_A)),
% 0.82/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/0.99  thf('60', plain, ((v3_orders_2 @ sk_A)),
% 0.82/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/0.99  thf('61', plain, ((l1_orders_2 @ sk_A)),
% 0.82/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.82/0.99  thf(dt_l1_orders_2, axiom,
% 0.82/0.99    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.82/0.99  thf('62', plain,
% 0.82/0.99      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_orders_2 @ X14))),
% 0.82/0.99      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.82/0.99  thf('63', plain, ((l1_struct_0 @ sk_A)),
% 0.82/0.99      inference('sup-', [status(thm)], ['61', '62'])).
% 0.82/0.99  thf('64', plain, ((((k1_xboole_0) != (k1_xboole_0)) | (v2_struct_0 @ sk_A))),
% 0.82/0.99      inference('demod', [status(thm)], ['56', '57', '58', '59', '60', '63'])).
% 0.82/0.99  thf('65', plain, ((v2_struct_0 @ sk_A)),
% 0.82/0.99      inference('simplify', [status(thm)], ['64'])).
% 0.82/0.99  thf('66', plain, ($false), inference('demod', [status(thm)], ['0', '65'])).
% 0.82/0.99  
% 0.82/0.99  % SZS output end Refutation
% 0.82/0.99  
% 0.82/1.00  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
