%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Cb0RYt4nCu

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:44 EST 2020

% Result     : Theorem 4.78s
% Output     : Refutation 4.78s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 299 expanded)
%              Number of leaves         :   33 ( 105 expanded)
%              Depth                    :   25
%              Number of atoms          : 2302 (4226 expanded)
%              Number of equality atoms :   83 ( 205 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

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

thf('1',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('6',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
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
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('13',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
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
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

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
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('24',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('25',plain,(
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
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
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
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('42',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

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
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('46',plain,(
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
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('59',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
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
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('62',plain,(
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
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('69',plain,(
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
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
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('72',plain,(
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
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r2_orders_2 @ X10 @ X9 @ X11 )
      | ( X9 != X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('79',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ~ ( r2_orders_2 @ X10 @ X11 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) ) ) ),
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
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
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
    ! [X7: $i] :
      ( ( ( k2_struct_0 @ X7 )
        = ( u1_struct_0 @ X7 ) )
      | ~ ( l1_struct_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('100',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
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
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Cb0RYt4nCu
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:47:48 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 4.78/5.03  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 4.78/5.03  % Solved by: fo/fo7.sh
% 4.78/5.03  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.78/5.03  % done 5591 iterations in 4.555s
% 4.78/5.03  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 4.78/5.03  % SZS output start Refutation
% 4.78/5.03  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 4.78/5.03  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.78/5.03  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.78/5.03  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 4.78/5.03  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.78/5.03  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 4.78/5.03  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.78/5.03  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 4.78/5.03  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 4.78/5.03  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 4.78/5.03  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 4.78/5.03  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 4.78/5.03  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.78/5.03  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.78/5.03  thf(sk_B_type, type, sk_B: $i > $i).
% 4.78/5.03  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 4.78/5.03  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 4.78/5.03  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 4.78/5.03  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 4.78/5.03  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 4.78/5.03  thf(sk_A_type, type, sk_A: $i).
% 4.78/5.03  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.78/5.03  thf(t46_orders_2, conjecture,
% 4.78/5.03    (![A:$i]:
% 4.78/5.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 4.78/5.03         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 4.78/5.03       ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 4.78/5.03  thf(zf_stmt_0, negated_conjecture,
% 4.78/5.03    (~( ![A:$i]:
% 4.78/5.03        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 4.78/5.03            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 4.78/5.03          ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 4.78/5.03    inference('cnf.neg', [status(esa)], [t46_orders_2])).
% 4.78/5.03  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf(t9_mcart_1, axiom,
% 4.78/5.03    (![A:$i]:
% 4.78/5.03     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 4.78/5.03          ( ![B:$i]:
% 4.78/5.03            ( ~( ( r2_hidden @ B @ A ) & 
% 4.78/5.03                 ( ![C:$i,D:$i]:
% 4.78/5.03                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 4.78/5.03                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 4.78/5.03  thf('1', plain,
% 4.78/5.03      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 4.78/5.03      inference('cnf', [status(esa)], [t9_mcart_1])).
% 4.78/5.03  thf(d3_struct_0, axiom,
% 4.78/5.03    (![A:$i]:
% 4.78/5.03     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 4.78/5.03  thf('2', plain,
% 4.78/5.03      (![X7 : $i]:
% 4.78/5.03         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.78/5.03  thf('3', plain,
% 4.78/5.03      (![X7 : $i]:
% 4.78/5.03         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.78/5.03  thf(dt_k2_subset_1, axiom,
% 4.78/5.03    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 4.78/5.03  thf('4', plain,
% 4.78/5.03      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 4.78/5.03      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 4.78/5.03  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 4.78/5.03  thf('5', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 4.78/5.03      inference('cnf', [status(esa)], [d4_subset_1])).
% 4.78/5.03  thf('6', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 4.78/5.03      inference('demod', [status(thm)], ['4', '5'])).
% 4.78/5.03  thf(d13_orders_2, axiom,
% 4.78/5.03    (![A:$i]:
% 4.78/5.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 4.78/5.03         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 4.78/5.03       ( ![B:$i]:
% 4.78/5.03         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.78/5.03           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 4.78/5.03  thf('7', plain,
% 4.78/5.03      (![X12 : $i, X13 : $i]:
% 4.78/5.03         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 4.78/5.03          | ((k2_orders_2 @ X13 @ X12) = (a_2_1_orders_2 @ X13 @ X12))
% 4.78/5.03          | ~ (l1_orders_2 @ X13)
% 4.78/5.03          | ~ (v5_orders_2 @ X13)
% 4.78/5.03          | ~ (v4_orders_2 @ X13)
% 4.78/5.03          | ~ (v3_orders_2 @ X13)
% 4.78/5.03          | (v2_struct_0 @ X13))),
% 4.78/5.03      inference('cnf', [status(esa)], [d13_orders_2])).
% 4.78/5.03  thf('8', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         ((v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 4.78/5.03              = (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['6', '7'])).
% 4.78/5.03  thf('9', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 4.78/5.03            = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0))),
% 4.78/5.03      inference('sup+', [status(thm)], ['3', '8'])).
% 4.78/5.03  thf('10', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 4.78/5.03            = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0))),
% 4.78/5.03      inference('sup+', [status(thm)], ['2', '9'])).
% 4.78/5.03  thf('11', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 4.78/5.03              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 4.78/5.03      inference('simplify', [status(thm)], ['10'])).
% 4.78/5.03  thf('12', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 4.78/5.03      inference('demod', [status(thm)], ['4', '5'])).
% 4.78/5.03  thf('13', plain,
% 4.78/5.03      (![X7 : $i]:
% 4.78/5.03         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.78/5.03  thf(fraenkel_a_2_1_orders_2, axiom,
% 4.78/5.03    (![A:$i,B:$i,C:$i]:
% 4.78/5.03     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 4.78/5.03         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 4.78/5.03         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 4.78/5.03       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 4.78/5.03         ( ?[D:$i]:
% 4.78/5.03           ( ( ![E:$i]:
% 4.78/5.03               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 4.78/5.03                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 4.78/5.03             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 4.78/5.03  thf('14', plain,
% 4.78/5.03      (![X15 : $i, X16 : $i, X18 : $i]:
% 4.78/5.03         (~ (l1_orders_2 @ X15)
% 4.78/5.03          | ~ (v5_orders_2 @ X15)
% 4.78/5.03          | ~ (v4_orders_2 @ X15)
% 4.78/5.03          | ~ (v3_orders_2 @ X15)
% 4.78/5.03          | (v2_struct_0 @ X15)
% 4.78/5.03          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 4.78/5.03          | ((X18) = (sk_D @ X16 @ X15 @ X18))
% 4.78/5.03          | ~ (r2_hidden @ X18 @ (a_2_1_orders_2 @ X15 @ X16)))),
% 4.78/5.03      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 4.78/5.03  thf('15', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ~ (r2_hidden @ X2 @ (a_2_1_orders_2 @ X0 @ X1))
% 4.78/5.03          | ((X2) = (sk_D @ X1 @ X0 @ X2))
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['13', '14'])).
% 4.78/5.03  thf('16', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 4.78/5.03          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.78/5.03          | ~ (l1_struct_0 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['12', '15'])).
% 4.78/5.03  thf('17', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['11', '16'])).
% 4.78/5.03  thf('18', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 4.78/5.03      inference('simplify', [status(thm)], ['17'])).
% 4.78/5.03  thf('19', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.78/5.03              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 4.78/5.03                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['1', '18'])).
% 4.78/5.03  thf('20', plain,
% 4.78/5.03      (![X7 : $i]:
% 4.78/5.03         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.78/5.03  thf('21', plain,
% 4.78/5.03      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 4.78/5.03      inference('cnf', [status(esa)], [t9_mcart_1])).
% 4.78/5.03  thf('22', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 4.78/5.03              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 4.78/5.03      inference('simplify', [status(thm)], ['10'])).
% 4.78/5.03  thf('23', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 4.78/5.03      inference('demod', [status(thm)], ['4', '5'])).
% 4.78/5.03  thf('24', plain,
% 4.78/5.03      (![X7 : $i]:
% 4.78/5.03         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.78/5.03  thf('25', plain,
% 4.78/5.03      (![X15 : $i, X16 : $i, X18 : $i]:
% 4.78/5.03         (~ (l1_orders_2 @ X15)
% 4.78/5.03          | ~ (v5_orders_2 @ X15)
% 4.78/5.03          | ~ (v4_orders_2 @ X15)
% 4.78/5.03          | ~ (v3_orders_2 @ X15)
% 4.78/5.03          | (v2_struct_0 @ X15)
% 4.78/5.03          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 4.78/5.03          | (m1_subset_1 @ (sk_D @ X16 @ X15 @ X18) @ (u1_struct_0 @ X15))
% 4.78/5.03          | ~ (r2_hidden @ X18 @ (a_2_1_orders_2 @ X15 @ X16)))),
% 4.78/5.03      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 4.78/5.03  thf('26', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ~ (r2_hidden @ X2 @ (a_2_1_orders_2 @ X0 @ X1))
% 4.78/5.03          | (m1_subset_1 @ (sk_D @ X1 @ X0 @ X2) @ (u1_struct_0 @ X0))
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['24', '25'])).
% 4.78/5.03  thf('27', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 4.78/5.03             (u1_struct_0 @ X0))
% 4.78/5.03          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.78/5.03          | ~ (l1_struct_0 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['23', '26'])).
% 4.78/5.03  thf('28', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 4.78/5.03             (u1_struct_0 @ X0))
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['22', '27'])).
% 4.78/5.03  thf('29', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         ((m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 4.78/5.03           (u1_struct_0 @ X0))
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 4.78/5.03      inference('simplify', [status(thm)], ['28'])).
% 4.78/5.03  thf('30', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | (m1_subset_1 @ 
% 4.78/5.03             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 4.78/5.03              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.78/5.03             (u1_struct_0 @ X0)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['21', '29'])).
% 4.78/5.03  thf('31', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         ((m1_subset_1 @ 
% 4.78/5.03           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 4.78/5.03            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.78/5.03           (k2_struct_0 @ X0))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 4.78/5.03      inference('sup+', [status(thm)], ['20', '30'])).
% 4.78/5.03  thf('32', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | (m1_subset_1 @ 
% 4.78/5.03             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 4.78/5.03              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.78/5.03             (k2_struct_0 @ X0)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['31'])).
% 4.78/5.03  thf('33', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 4.78/5.03           (k2_struct_0 @ X0))
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 4.78/5.03      inference('sup+', [status(thm)], ['19', '32'])).
% 4.78/5.03  thf('34', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 4.78/5.03             (k2_struct_0 @ X0)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['33'])).
% 4.78/5.03  thf(t2_subset, axiom,
% 4.78/5.03    (![A:$i,B:$i]:
% 4.78/5.03     ( ( m1_subset_1 @ A @ B ) =>
% 4.78/5.03       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 4.78/5.03  thf('35', plain,
% 4.78/5.03      (![X2 : $i, X3 : $i]:
% 4.78/5.03         ((r2_hidden @ X2 @ X3)
% 4.78/5.03          | (v1_xboole_0 @ X3)
% 4.78/5.03          | ~ (m1_subset_1 @ X2 @ X3))),
% 4.78/5.03      inference('cnf', [status(esa)], [t2_subset])).
% 4.78/5.03  thf('36', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 4.78/5.03          | (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 4.78/5.03             (k2_struct_0 @ X0)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['34', '35'])).
% 4.78/5.03  thf('37', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.78/5.03              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 4.78/5.03                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['1', '18'])).
% 4.78/5.03  thf('38', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | (m1_subset_1 @ 
% 4.78/5.03             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 4.78/5.03              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.78/5.03             (u1_struct_0 @ X0)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['21', '29'])).
% 4.78/5.03  thf('39', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 4.78/5.03           (u1_struct_0 @ X0))
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 4.78/5.03      inference('sup+', [status(thm)], ['37', '38'])).
% 4.78/5.03  thf('40', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 4.78/5.03             (u1_struct_0 @ X0)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['39'])).
% 4.78/5.03  thf('41', plain,
% 4.78/5.03      (![X7 : $i]:
% 4.78/5.03         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.78/5.03  thf('42', plain,
% 4.78/5.03      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 4.78/5.03      inference('cnf', [status(esa)], [t9_mcart_1])).
% 4.78/5.03  thf('43', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 4.78/5.03              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 4.78/5.03      inference('simplify', [status(thm)], ['10'])).
% 4.78/5.03  thf('44', plain,
% 4.78/5.03      (![X7 : $i]:
% 4.78/5.03         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.78/5.03  thf('45', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 4.78/5.03      inference('demod', [status(thm)], ['4', '5'])).
% 4.78/5.03  thf('46', plain,
% 4.78/5.03      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 4.78/5.03         (~ (l1_orders_2 @ X15)
% 4.78/5.03          | ~ (v5_orders_2 @ X15)
% 4.78/5.03          | ~ (v4_orders_2 @ X15)
% 4.78/5.03          | ~ (v3_orders_2 @ X15)
% 4.78/5.03          | (v2_struct_0 @ X15)
% 4.78/5.03          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 4.78/5.03          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 4.78/5.03          | (r2_orders_2 @ X15 @ (sk_D @ X16 @ X15 @ X18) @ X17)
% 4.78/5.03          | ~ (r2_hidden @ X17 @ X16)
% 4.78/5.03          | ~ (r2_hidden @ X18 @ (a_2_1_orders_2 @ X15 @ X16)))),
% 4.78/5.03      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 4.78/5.03  thf('47', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 4.78/5.03          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 4.78/5.03          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 4.78/5.03          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['45', '46'])).
% 4.78/5.03  thf('48', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.78/5.03          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 4.78/5.03          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['44', '47'])).
% 4.78/5.03  thf('49', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 4.78/5.03          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 4.78/5.03          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['43', '48'])).
% 4.78/5.03  thf('50', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.78/5.03         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.78/5.03          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 4.78/5.03          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 4.78/5.03      inference('simplify', [status(thm)], ['49'])).
% 4.78/5.03  thf('51', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 4.78/5.03          | (r2_orders_2 @ X0 @ 
% 4.78/5.03             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.78/5.03              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.78/5.03             X1)
% 4.78/5.03          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['42', '50'])).
% 4.78/5.03  thf('52', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X1 @ (k2_struct_0 @ X0))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 4.78/5.03          | (r2_orders_2 @ X0 @ 
% 4.78/5.03             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.78/5.03              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.78/5.03             X1)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['41', '51'])).
% 4.78/5.03  thf('53', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | (r2_orders_2 @ X0 @ 
% 4.78/5.03             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.78/5.03              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.78/5.03             X1)
% 4.78/5.03          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['52'])).
% 4.78/5.03  thf('54', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 4.78/5.03               (k2_struct_0 @ X0))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | (r2_orders_2 @ X0 @ 
% 4.78/5.03             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.78/5.03              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.78/5.03             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['40', '53'])).
% 4.78/5.03  thf('55', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         ((r2_orders_2 @ X0 @ 
% 4.78/5.03           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.78/5.03            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.78/5.03           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 4.78/5.03          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 4.78/5.03               (k2_struct_0 @ X0))
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0))),
% 4.78/5.03      inference('simplify', [status(thm)], ['54'])).
% 4.78/5.03  thf('56', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | (r2_orders_2 @ X0 @ 
% 4.78/5.03             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.78/5.03              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.78/5.03             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['36', '55'])).
% 4.78/5.03  thf('57', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         ((r2_orders_2 @ X0 @ 
% 4.78/5.03           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.78/5.03            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.78/5.03           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['56'])).
% 4.78/5.03  thf('58', plain,
% 4.78/5.03      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 4.78/5.03      inference('cnf', [status(esa)], [t9_mcart_1])).
% 4.78/5.03  thf('59', plain,
% 4.78/5.03      (![X7 : $i]:
% 4.78/5.03         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.78/5.03  thf('60', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         ((v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 4.78/5.03              = (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['6', '7'])).
% 4.78/5.03  thf('61', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 4.78/5.03      inference('demod', [status(thm)], ['4', '5'])).
% 4.78/5.03  thf('62', plain,
% 4.78/5.03      (![X15 : $i, X16 : $i, X18 : $i]:
% 4.78/5.03         (~ (l1_orders_2 @ X15)
% 4.78/5.03          | ~ (v5_orders_2 @ X15)
% 4.78/5.03          | ~ (v4_orders_2 @ X15)
% 4.78/5.03          | ~ (v3_orders_2 @ X15)
% 4.78/5.03          | (v2_struct_0 @ X15)
% 4.78/5.03          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 4.78/5.03          | ((X18) = (sk_D @ X16 @ X15 @ X18))
% 4.78/5.03          | ~ (r2_hidden @ X18 @ (a_2_1_orders_2 @ X15 @ X16)))),
% 4.78/5.03      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 4.78/5.03  thf('63', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 4.78/5.03          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['61', '62'])).
% 4.78/5.03  thf('64', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['60', '63'])).
% 4.78/5.03  thf('65', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 4.78/5.03      inference('simplify', [status(thm)], ['64'])).
% 4.78/5.03  thf('66', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['59', '65'])).
% 4.78/5.03  thf('67', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.78/5.03              = (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.78/5.03                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['58', '66'])).
% 4.78/5.03  thf('68', plain,
% 4.78/5.03      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 4.78/5.03      inference('cnf', [status(esa)], [t9_mcart_1])).
% 4.78/5.03  thf('69', plain,
% 4.78/5.03      (![X7 : $i]:
% 4.78/5.03         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.78/5.03  thf('70', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         ((v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 4.78/5.03              = (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 4.78/5.03      inference('sup-', [status(thm)], ['6', '7'])).
% 4.78/5.03  thf('71', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 4.78/5.03      inference('demod', [status(thm)], ['4', '5'])).
% 4.78/5.03  thf('72', plain,
% 4.78/5.03      (![X15 : $i, X16 : $i, X18 : $i]:
% 4.78/5.03         (~ (l1_orders_2 @ X15)
% 4.78/5.03          | ~ (v5_orders_2 @ X15)
% 4.78/5.03          | ~ (v4_orders_2 @ X15)
% 4.78/5.03          | ~ (v3_orders_2 @ X15)
% 4.78/5.03          | (v2_struct_0 @ X15)
% 4.78/5.03          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 4.78/5.03          | (m1_subset_1 @ (sk_D @ X16 @ X15 @ X18) @ (u1_struct_0 @ X15))
% 4.78/5.03          | ~ (r2_hidden @ X18 @ (a_2_1_orders_2 @ X15 @ X16)))),
% 4.78/5.03      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 4.78/5.03  thf('73', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 4.78/5.03          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 4.78/5.03             (u1_struct_0 @ X0))
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['71', '72'])).
% 4.78/5.03  thf('74', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 4.78/5.03             (u1_struct_0 @ X0)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['70', '73'])).
% 4.78/5.03  thf('75', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         ((m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 4.78/5.03           (u1_struct_0 @ X0))
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 4.78/5.03      inference('simplify', [status(thm)], ['74'])).
% 4.78/5.03  thf('76', plain,
% 4.78/5.03      (![X0 : $i, X1 : $i]:
% 4.78/5.03         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 4.78/5.03             (u1_struct_0 @ X0)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['69', '75'])).
% 4.78/5.03  thf('77', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | (m1_subset_1 @ 
% 4.78/5.03             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.78/5.03              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.78/5.03             (u1_struct_0 @ X0))
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['68', '76'])).
% 4.78/5.03  thf(d10_orders_2, axiom,
% 4.78/5.03    (![A:$i]:
% 4.78/5.03     ( ( l1_orders_2 @ A ) =>
% 4.78/5.03       ( ![B:$i]:
% 4.78/5.03         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 4.78/5.03           ( ![C:$i]:
% 4.78/5.03             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.78/5.03               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 4.78/5.03                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 4.78/5.03  thf('78', plain,
% 4.78/5.03      (![X9 : $i, X10 : $i, X11 : $i]:
% 4.78/5.03         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 4.78/5.03          | ~ (r2_orders_2 @ X10 @ X9 @ X11)
% 4.78/5.03          | ((X9) != (X11))
% 4.78/5.03          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 4.78/5.03          | ~ (l1_orders_2 @ X10))),
% 4.78/5.03      inference('cnf', [status(esa)], [d10_orders_2])).
% 4.78/5.03  thf('79', plain,
% 4.78/5.03      (![X10 : $i, X11 : $i]:
% 4.78/5.03         (~ (l1_orders_2 @ X10)
% 4.78/5.03          | ~ (r2_orders_2 @ X10 @ X11 @ X11)
% 4.78/5.03          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['78'])).
% 4.78/5.03  thf('80', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (~ (l1_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | ~ (r2_orders_2 @ X0 @ 
% 4.78/5.03               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.78/5.03                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.78/5.03               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.78/5.03                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 4.78/5.03          | ~ (l1_orders_2 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['77', '79'])).
% 4.78/5.03  thf('81', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (~ (r2_orders_2 @ X0 @ 
% 4.78/5.03             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.78/5.03              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.78/5.03             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.78/5.03              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0))),
% 4.78/5.03      inference('simplify', [status(thm)], ['80'])).
% 4.78/5.03  thf('82', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (~ (r2_orders_2 @ X0 @ 
% 4.78/5.03             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.78/5.03              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.78/5.03             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['67', '81'])).
% 4.78/5.03  thf('83', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ~ (r2_orders_2 @ X0 @ 
% 4.78/5.03               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.78/5.03                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.78/5.03               (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 4.78/5.03      inference('simplify', [status(thm)], ['82'])).
% 4.78/5.03  thf('84', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 4.78/5.03      inference('sup-', [status(thm)], ['57', '83'])).
% 4.78/5.03  thf('85', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (~ (l1_orders_2 @ X0)
% 4.78/5.03          | ~ (v5_orders_2 @ X0)
% 4.78/5.03          | ~ (v4_orders_2 @ X0)
% 4.78/5.03          | ~ (v3_orders_2 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.78/5.03          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['84'])).
% 4.78/5.03  thf('86', plain,
% 4.78/5.03      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('87', plain,
% 4.78/5.03      ((((k1_xboole_0) != (k1_xboole_0))
% 4.78/5.03        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 4.78/5.03        | ~ (l1_struct_0 @ sk_A)
% 4.78/5.03        | (v2_struct_0 @ sk_A)
% 4.78/5.03        | ~ (v3_orders_2 @ sk_A)
% 4.78/5.03        | ~ (v4_orders_2 @ sk_A)
% 4.78/5.03        | ~ (v5_orders_2 @ sk_A)
% 4.78/5.03        | ~ (l1_orders_2 @ sk_A))),
% 4.78/5.03      inference('sup-', [status(thm)], ['85', '86'])).
% 4.78/5.03  thf('88', plain, ((l1_orders_2 @ sk_A)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf(dt_l1_orders_2, axiom,
% 4.78/5.03    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 4.78/5.03  thf('89', plain,
% 4.78/5.03      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_orders_2 @ X14))),
% 4.78/5.03      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 4.78/5.03  thf('90', plain, ((l1_struct_0 @ sk_A)),
% 4.78/5.03      inference('sup-', [status(thm)], ['88', '89'])).
% 4.78/5.03  thf('91', plain, ((v3_orders_2 @ sk_A)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('92', plain, ((v4_orders_2 @ sk_A)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('93', plain, ((v5_orders_2 @ sk_A)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('94', plain, ((l1_orders_2 @ sk_A)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('95', plain,
% 4.78/5.03      ((((k1_xboole_0) != (k1_xboole_0))
% 4.78/5.03        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 4.78/5.03        | (v2_struct_0 @ sk_A))),
% 4.78/5.03      inference('demod', [status(thm)], ['87', '90', '91', '92', '93', '94'])).
% 4.78/5.03  thf('96', plain,
% 4.78/5.03      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['95'])).
% 4.78/5.03  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 4.78/5.03      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.78/5.03  thf('98', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 4.78/5.03      inference('clc', [status(thm)], ['96', '97'])).
% 4.78/5.03  thf('99', plain,
% 4.78/5.03      (![X7 : $i]:
% 4.78/5.03         (((k2_struct_0 @ X7) = (u1_struct_0 @ X7)) | ~ (l1_struct_0 @ X7))),
% 4.78/5.03      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.78/5.03  thf(fc2_struct_0, axiom,
% 4.78/5.03    (![A:$i]:
% 4.78/5.03     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 4.78/5.03       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 4.78/5.03  thf('100', plain,
% 4.78/5.03      (![X8 : $i]:
% 4.78/5.03         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 4.78/5.03          | ~ (l1_struct_0 @ X8)
% 4.78/5.03          | (v2_struct_0 @ X8))),
% 4.78/5.03      inference('cnf', [status(esa)], [fc2_struct_0])).
% 4.78/5.03  thf('101', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | (v2_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0))),
% 4.78/5.03      inference('sup-', [status(thm)], ['99', '100'])).
% 4.78/5.03  thf('102', plain,
% 4.78/5.03      (![X0 : $i]:
% 4.78/5.03         ((v2_struct_0 @ X0)
% 4.78/5.03          | ~ (l1_struct_0 @ X0)
% 4.78/5.03          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 4.78/5.03      inference('simplify', [status(thm)], ['101'])).
% 4.78/5.03  thf('103', plain, ((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 4.78/5.03      inference('sup-', [status(thm)], ['98', '102'])).
% 4.78/5.03  thf('104', plain, ((l1_struct_0 @ sk_A)),
% 4.78/5.03      inference('sup-', [status(thm)], ['88', '89'])).
% 4.78/5.03  thf('105', plain, ((v2_struct_0 @ sk_A)),
% 4.78/5.03      inference('demod', [status(thm)], ['103', '104'])).
% 4.78/5.03  thf('106', plain, ($false), inference('demod', [status(thm)], ['0', '105'])).
% 4.78/5.03  
% 4.78/5.03  % SZS output end Refutation
% 4.78/5.03  
% 4.78/5.04  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
