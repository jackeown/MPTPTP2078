%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xd8typVtBu

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:46 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 196 expanded)
%              Number of leaves         :   31 (  72 expanded)
%              Depth                    :   21
%              Number of atoms          : 1583 (3319 expanded)
%              Number of equality atoms :   53 ( 121 expanded)
%              Maximal formula depth    :   24 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

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
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

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

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

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
    ! [X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

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
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('56',plain,(
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('57',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51','52','53','54','57'])).

thf('59',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
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

thf('63',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','65'])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('68',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference(demod,[status(thm)],['0','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Xd8typVtBu
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:18:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.85  % Solved by: fo/fo7.sh
% 0.60/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.85  % done 234 iterations in 0.350s
% 0.60/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.85  % SZS output start Refutation
% 0.60/0.85  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.60/0.85  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.60/0.85  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.60/0.85  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.85  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.60/0.85  thf(sk_B_type, type, sk_B: $i > $i).
% 0.60/0.85  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.60/0.85  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.60/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.85  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.60/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.85  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.85  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.60/0.85  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.60/0.85  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 0.60/0.85  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.60/0.85  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.60/0.85  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.60/0.85  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.60/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.85  thf(t46_orders_2, conjecture,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.60/0.85         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.60/0.85       ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 0.60/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.85    (~( ![A:$i]:
% 0.60/0.85        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.60/0.85            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.60/0.85          ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 0.60/0.85    inference('cnf.neg', [status(esa)], [t46_orders_2])).
% 0.60/0.85  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(d3_struct_0, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.60/0.85  thf('1', plain,
% 0.60/0.85      (![X6 : $i]:
% 0.60/0.85         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.60/0.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.60/0.85  thf(t29_mcart_1, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.60/0.85          ( ![B:$i]:
% 0.60/0.85            ( ~( ( r2_hidden @ B @ A ) & 
% 0.60/0.85                 ( ![C:$i,D:$i,E:$i]:
% 0.60/0.85                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.60/0.85                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.85  thf('2', plain,
% 0.60/0.85      (![X2 : $i]: (((X2) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.60/0.85      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.60/0.85  thf(dt_k2_struct_0, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( l1_struct_0 @ A ) =>
% 0.60/0.85       ( m1_subset_1 @
% 0.60/0.85         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.60/0.85  thf('3', plain,
% 0.60/0.85      (![X7 : $i]:
% 0.60/0.85         ((m1_subset_1 @ (k2_struct_0 @ X7) @ 
% 0.60/0.85           (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.60/0.85          | ~ (l1_struct_0 @ X7))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.60/0.85  thf(d13_orders_2, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.60/0.85         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.60/0.85       ( ![B:$i]:
% 0.60/0.85         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.60/0.85           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 0.60/0.85  thf('4', plain,
% 0.60/0.85      (![X12 : $i, X13 : $i]:
% 0.60/0.85         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 0.60/0.85          | ((k2_orders_2 @ X13 @ X12) = (a_2_1_orders_2 @ X13 @ X12))
% 0.60/0.85          | ~ (l1_orders_2 @ X13)
% 0.60/0.85          | ~ (v5_orders_2 @ X13)
% 0.60/0.85          | ~ (v4_orders_2 @ X13)
% 0.60/0.85          | ~ (v3_orders_2 @ X13)
% 0.60/0.85          | (v2_struct_0 @ X13))),
% 0.60/0.85      inference('cnf', [status(esa)], [d13_orders_2])).
% 0.60/0.85  thf('5', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (l1_struct_0 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 0.60/0.85              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['3', '4'])).
% 0.60/0.85  thf('6', plain,
% 0.60/0.85      (![X7 : $i]:
% 0.60/0.85         ((m1_subset_1 @ (k2_struct_0 @ X7) @ 
% 0.60/0.85           (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.60/0.85          | ~ (l1_struct_0 @ X7))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.60/0.85  thf(fraenkel_a_2_1_orders_2, axiom,
% 0.60/0.85    (![A:$i,B:$i,C:$i]:
% 0.60/0.85     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.60/0.85         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.60/0.85         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.60/0.85       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 0.60/0.85         ( ?[D:$i]:
% 0.60/0.85           ( ( ![E:$i]:
% 0.60/0.85               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.60/0.85                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 0.60/0.85             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.60/0.85  thf('7', plain,
% 0.60/0.85      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.60/0.85         (~ (l1_orders_2 @ X15)
% 0.60/0.85          | ~ (v5_orders_2 @ X15)
% 0.60/0.85          | ~ (v4_orders_2 @ X15)
% 0.60/0.85          | ~ (v3_orders_2 @ X15)
% 0.60/0.85          | (v2_struct_0 @ X15)
% 0.60/0.85          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.60/0.85          | ((X18) = (sk_D @ X16 @ X15 @ X18))
% 0.60/0.85          | ~ (r2_hidden @ X18 @ (a_2_1_orders_2 @ X15 @ X16)))),
% 0.60/0.85      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.60/0.85  thf('8', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         (~ (l1_struct_0 @ X0)
% 0.60/0.85          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.60/0.85          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0))),
% 0.60/0.85      inference('sup-', [status(thm)], ['6', '7'])).
% 0.60/0.85  thf('9', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 0.60/0.85          | ~ (l1_struct_0 @ X0))),
% 0.60/0.85      inference('sup-', [status(thm)], ['5', '8'])).
% 0.60/0.85  thf('10', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         (((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.60/0.85      inference('simplify', [status(thm)], ['9'])).
% 0.60/0.85  thf('11', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.60/0.85              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.60/0.85                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['2', '10'])).
% 0.60/0.85  thf('12', plain,
% 0.60/0.85      (![X2 : $i]: (((X2) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.60/0.85      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.60/0.85  thf('13', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (l1_struct_0 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 0.60/0.85              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['3', '4'])).
% 0.60/0.85  thf('14', plain,
% 0.60/0.85      (![X7 : $i]:
% 0.60/0.85         ((m1_subset_1 @ (k2_struct_0 @ X7) @ 
% 0.60/0.85           (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.60/0.85          | ~ (l1_struct_0 @ X7))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.60/0.85  thf('15', plain,
% 0.60/0.85      (![X15 : $i, X16 : $i, X18 : $i]:
% 0.60/0.85         (~ (l1_orders_2 @ X15)
% 0.60/0.85          | ~ (v5_orders_2 @ X15)
% 0.60/0.85          | ~ (v4_orders_2 @ X15)
% 0.60/0.85          | ~ (v3_orders_2 @ X15)
% 0.60/0.85          | (v2_struct_0 @ X15)
% 0.60/0.85          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.60/0.85          | (m1_subset_1 @ (sk_D @ X16 @ X15 @ X18) @ (u1_struct_0 @ X15))
% 0.60/0.85          | ~ (r2_hidden @ X18 @ (a_2_1_orders_2 @ X15 @ X16)))),
% 0.60/0.85      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.60/0.85  thf('16', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         (~ (l1_struct_0 @ X0)
% 0.60/0.85          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.60/0.85          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 0.60/0.85             (u1_struct_0 @ X0))
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0))),
% 0.60/0.85      inference('sup-', [status(thm)], ['14', '15'])).
% 0.60/0.85  thf('17', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 0.60/0.85             (u1_struct_0 @ X0))
% 0.60/0.85          | ~ (l1_struct_0 @ X0))),
% 0.60/0.85      inference('sup-', [status(thm)], ['13', '16'])).
% 0.60/0.85  thf('18', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 0.60/0.85           (u1_struct_0 @ X0))
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.60/0.85      inference('simplify', [status(thm)], ['17'])).
% 0.60/0.85  thf('19', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | (m1_subset_1 @ 
% 0.60/0.85             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.60/0.85              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.60/0.85             (u1_struct_0 @ X0)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['12', '18'])).
% 0.60/0.85  thf('20', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.60/0.85           (u1_struct_0 @ X0))
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.60/0.85      inference('sup+', [status(thm)], ['11', '19'])).
% 0.60/0.85  thf('21', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.60/0.85             (u1_struct_0 @ X0)))),
% 0.60/0.85      inference('simplify', [status(thm)], ['20'])).
% 0.60/0.85  thf('22', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.60/0.85           (k2_struct_0 @ X0))
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.60/0.85      inference('sup+', [status(thm)], ['1', '21'])).
% 0.60/0.85  thf('23', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.60/0.85             (k2_struct_0 @ X0)))),
% 0.60/0.85      inference('simplify', [status(thm)], ['22'])).
% 0.60/0.85  thf(t2_subset, axiom,
% 0.60/0.85    (![A:$i,B:$i]:
% 0.60/0.85     ( ( m1_subset_1 @ A @ B ) =>
% 0.60/0.85       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.60/0.85  thf('24', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         ((r2_hidden @ X0 @ X1)
% 0.60/0.85          | (v1_xboole_0 @ X1)
% 0.60/0.85          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.60/0.85      inference('cnf', [status(esa)], [t2_subset])).
% 0.60/0.85  thf('25', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (l1_struct_0 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.60/0.85          | (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.60/0.85             (k2_struct_0 @ X0)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['23', '24'])).
% 0.60/0.85  thf('26', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.60/0.85             (u1_struct_0 @ X0)))),
% 0.60/0.85      inference('simplify', [status(thm)], ['20'])).
% 0.60/0.85  thf('27', plain,
% 0.60/0.85      (![X2 : $i]: (((X2) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.60/0.85      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.60/0.85  thf('28', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (l1_struct_0 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 0.60/0.85              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['3', '4'])).
% 0.60/0.85  thf('29', plain,
% 0.60/0.85      (![X7 : $i]:
% 0.60/0.85         ((m1_subset_1 @ (k2_struct_0 @ X7) @ 
% 0.60/0.85           (k1_zfmisc_1 @ (u1_struct_0 @ X7)))
% 0.60/0.85          | ~ (l1_struct_0 @ X7))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.60/0.85  thf('30', plain,
% 0.60/0.85      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.60/0.85         (~ (l1_orders_2 @ X15)
% 0.60/0.85          | ~ (v5_orders_2 @ X15)
% 0.60/0.85          | ~ (v4_orders_2 @ X15)
% 0.60/0.85          | ~ (v3_orders_2 @ X15)
% 0.60/0.85          | (v2_struct_0 @ X15)
% 0.60/0.85          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.60/0.85          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 0.60/0.85          | (r2_orders_2 @ X15 @ (sk_D @ X16 @ X15 @ X18) @ X17)
% 0.60/0.85          | ~ (r2_hidden @ X17 @ X16)
% 0.60/0.85          | ~ (r2_hidden @ X18 @ (a_2_1_orders_2 @ X15 @ X16)))),
% 0.60/0.85      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.60/0.85  thf('31', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.85         (~ (l1_struct_0 @ X0)
% 0.60/0.85          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.60/0.85          | ~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 0.60/0.85          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 0.60/0.85          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0))),
% 0.60/0.85      inference('sup-', [status(thm)], ['29', '30'])).
% 0.60/0.85  thf('32', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.85         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.60/0.85          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 0.60/0.85          | ~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 0.60/0.85          | ~ (l1_struct_0 @ X0))),
% 0.60/0.85      inference('sup-', [status(thm)], ['28', '31'])).
% 0.60/0.85  thf('33', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.85         (~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 0.60/0.85          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 0.60/0.85          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.60/0.85      inference('simplify', [status(thm)], ['32'])).
% 0.60/0.85  thf('34', plain,
% 0.60/0.85      (![X0 : $i, X1 : $i]:
% 0.60/0.85         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.60/0.85          | (r2_orders_2 @ X0 @ 
% 0.60/0.85             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.60/0.85              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.60/0.85             X1)
% 0.60/0.85          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['27', '33'])).
% 0.60/0.85  thf('35', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (l1_struct_0 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.60/0.85               (k2_struct_0 @ X0))
% 0.60/0.85          | (r2_orders_2 @ X0 @ 
% 0.60/0.85             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.60/0.85              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.60/0.85             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['26', '34'])).
% 0.60/0.85  thf('36', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((r2_orders_2 @ X0 @ 
% 0.60/0.85           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.60/0.85            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.60/0.85           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 0.60/0.85          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.60/0.85               (k2_struct_0 @ X0))
% 0.60/0.85          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0))),
% 0.60/0.85      inference('simplify', [status(thm)], ['35'])).
% 0.60/0.85  thf('37', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.60/0.85          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | (r2_orders_2 @ X0 @ 
% 0.60/0.85             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.60/0.85              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.60/0.85             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['25', '36'])).
% 0.60/0.85  thf('38', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((r2_orders_2 @ X0 @ 
% 0.60/0.85           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.60/0.85            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.60/0.85           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.60/0.85      inference('simplify', [status(thm)], ['37'])).
% 0.60/0.85  thf('39', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.60/0.85              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.60/0.85                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 0.60/0.85      inference('sup-', [status(thm)], ['2', '10'])).
% 0.60/0.85  thf('40', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | (m1_subset_1 @ 
% 0.60/0.85             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.60/0.85              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.60/0.85             (u1_struct_0 @ X0)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['12', '18'])).
% 0.60/0.85  thf(d10_orders_2, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( l1_orders_2 @ A ) =>
% 0.60/0.85       ( ![B:$i]:
% 0.60/0.85         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.60/0.85           ( ![C:$i]:
% 0.60/0.85             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.60/0.85               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.60/0.85                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 0.60/0.85  thf('41', plain,
% 0.60/0.85      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.85         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 0.60/0.85          | ~ (r2_orders_2 @ X10 @ X9 @ X11)
% 0.60/0.85          | ((X9) != (X11))
% 0.60/0.85          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 0.60/0.85          | ~ (l1_orders_2 @ X10))),
% 0.60/0.85      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.60/0.85  thf('42', plain,
% 0.60/0.85      (![X10 : $i, X11 : $i]:
% 0.60/0.85         (~ (l1_orders_2 @ X10)
% 0.60/0.85          | ~ (r2_orders_2 @ X10 @ X11 @ X11)
% 0.60/0.85          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10)))),
% 0.60/0.85      inference('simplify', [status(thm)], ['41'])).
% 0.60/0.85  thf('43', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (l1_struct_0 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | ~ (r2_orders_2 @ X0 @ 
% 0.60/0.85               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.60/0.85                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.60/0.85               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.60/0.85                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 0.60/0.85          | ~ (l1_orders_2 @ X0))),
% 0.60/0.85      inference('sup-', [status(thm)], ['40', '42'])).
% 0.60/0.85  thf('44', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (r2_orders_2 @ X0 @ 
% 0.60/0.85             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.60/0.85              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.60/0.85             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.60/0.85              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 0.60/0.85          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0))),
% 0.60/0.85      inference('simplify', [status(thm)], ['43'])).
% 0.60/0.85  thf('45', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (r2_orders_2 @ X0 @ 
% 0.60/0.85             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.60/0.85              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.60/0.85             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['39', '44'])).
% 0.60/0.85  thf('46', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | ~ (r2_orders_2 @ X0 @ 
% 0.60/0.85               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.60/0.85                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.60/0.85               (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 0.60/0.85      inference('simplify', [status(thm)], ['45'])).
% 0.60/0.85  thf('47', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.60/0.85          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.60/0.85      inference('sup-', [status(thm)], ['38', '46'])).
% 0.60/0.85  thf('48', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (l1_struct_0 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (v3_orders_2 @ X0)
% 0.60/0.85          | ~ (v4_orders_2 @ X0)
% 0.60/0.85          | ~ (v5_orders_2 @ X0)
% 0.60/0.85          | ~ (l1_orders_2 @ X0)
% 0.60/0.85          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.60/0.85          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.60/0.85      inference('simplify', [status(thm)], ['47'])).
% 0.60/0.85  thf('49', plain,
% 0.60/0.85      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('50', plain,
% 0.60/0.85      ((((k1_xboole_0) != (k1_xboole_0))
% 0.60/0.85        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.60/0.85        | ~ (l1_orders_2 @ sk_A)
% 0.60/0.85        | ~ (v5_orders_2 @ sk_A)
% 0.60/0.85        | ~ (v4_orders_2 @ sk_A)
% 0.60/0.85        | ~ (v3_orders_2 @ sk_A)
% 0.60/0.85        | (v2_struct_0 @ sk_A)
% 0.60/0.85        | ~ (l1_struct_0 @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['48', '49'])).
% 0.60/0.85  thf('51', plain, ((l1_orders_2 @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('52', plain, ((v5_orders_2 @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('53', plain, ((v4_orders_2 @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('54', plain, ((v3_orders_2 @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('55', plain, ((l1_orders_2 @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf(dt_l1_orders_2, axiom,
% 0.60/0.85    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.60/0.85  thf('56', plain,
% 0.60/0.85      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_orders_2 @ X14))),
% 0.60/0.85      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.60/0.85  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.60/0.85      inference('sup-', [status(thm)], ['55', '56'])).
% 0.60/0.85  thf('58', plain,
% 0.60/0.85      ((((k1_xboole_0) != (k1_xboole_0))
% 0.60/0.85        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.60/0.85        | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('demod', [status(thm)], ['50', '51', '52', '53', '54', '57'])).
% 0.60/0.85  thf('59', plain,
% 0.60/0.85      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.60/0.85      inference('simplify', [status(thm)], ['58'])).
% 0.60/0.85  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.60/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.85  thf('61', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.60/0.85      inference('clc', [status(thm)], ['59', '60'])).
% 0.60/0.85  thf('62', plain,
% 0.60/0.85      (![X6 : $i]:
% 0.60/0.85         (((k2_struct_0 @ X6) = (u1_struct_0 @ X6)) | ~ (l1_struct_0 @ X6))),
% 0.60/0.85      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.60/0.85  thf(fc2_struct_0, axiom,
% 0.60/0.85    (![A:$i]:
% 0.60/0.85     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.60/0.85       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.60/0.85  thf('63', plain,
% 0.60/0.85      (![X8 : $i]:
% 0.60/0.85         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 0.60/0.85          | ~ (l1_struct_0 @ X8)
% 0.60/0.85          | (v2_struct_0 @ X8))),
% 0.60/0.85      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.60/0.85  thf('64', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | (v2_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0))),
% 0.60/0.85      inference('sup-', [status(thm)], ['62', '63'])).
% 0.60/0.85  thf('65', plain,
% 0.60/0.85      (![X0 : $i]:
% 0.60/0.85         ((v2_struct_0 @ X0)
% 0.60/0.85          | ~ (l1_struct_0 @ X0)
% 0.60/0.85          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.60/0.85      inference('simplify', [status(thm)], ['64'])).
% 0.60/0.85  thf('66', plain, ((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.60/0.85      inference('sup-', [status(thm)], ['61', '65'])).
% 0.60/0.85  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.60/0.85      inference('sup-', [status(thm)], ['55', '56'])).
% 0.60/0.85  thf('68', plain, ((v2_struct_0 @ sk_A)),
% 0.60/0.85      inference('demod', [status(thm)], ['66', '67'])).
% 0.60/0.85  thf('69', plain, ($false), inference('demod', [status(thm)], ['0', '68'])).
% 0.60/0.85  
% 0.60/0.85  % SZS output end Refutation
% 0.60/0.85  
% 0.60/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
