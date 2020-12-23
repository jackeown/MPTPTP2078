%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4gKzX4PoqA

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:46 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 221 expanded)
%              Number of leaves         :   32 (  80 expanded)
%              Depth                    :   22
%              Number of atoms          : 1771 (3686 expanded)
%              Number of equality atoms :   60 ( 140 expanded)
%              Maximal formula depth    :   24 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

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
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
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
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( ( k2_orders_2 @ X14 @ X13 )
        = ( a_2_1_orders_2 @ X14 @ X13 ) )
      | ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 ) ) ),
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
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
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
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( X21
        = ( sk_D @ X19 @ X18 @ X21 ) )
      | ~ ( r2_hidden @ X21 @ ( a_2_1_orders_2 @ X18 @ X19 ) ) ) ),
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
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
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
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('15',plain,(
    ! [X18: $i,X19: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X19 @ X18 @ X21 ) @ ( u1_struct_0 @ X18 ) )
      | ~ ( r2_hidden @ X21 @ ( a_2_1_orders_2 @ X18 @ X19 ) ) ) ),
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
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
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
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('30',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X18 ) )
      | ( r2_orders_2 @ X18 @ ( sk_D @ X19 @ X18 @ X21 ) @ X20 )
      | ~ ( r2_hidden @ X20 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( a_2_1_orders_2 @ X18 @ X19 ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( u1_struct_0 @ X11 ) )
      | ~ ( r2_orders_2 @ X11 @ X10 @ X12 )
      | ( X10 != X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) )
      | ~ ( l1_orders_2 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( l1_orders_2 @ X11 )
      | ~ ( r2_orders_2 @ X11 @ X12 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X11 ) ) ) ),
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
    ! [X17: $i] :
      ( ( l1_struct_0 @ X17 )
      | ~ ( l1_orders_2 @ X17 ) ) ),
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
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('63',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf('64',plain,(
    ! [X9: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X9 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X9 ) ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(dt_k2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('65',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( m1_subset_1 @ ( k2_orders_2 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_orders_2])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('67',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

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

thf('78',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73','74','75','76','77'])).

thf('79',plain,(
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['78','79'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['0','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4gKzX4PoqA
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.74/0.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.74/0.98  % Solved by: fo/fo7.sh
% 0.74/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.74/0.98  % done 521 iterations in 0.528s
% 0.74/0.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.74/0.98  % SZS output start Refutation
% 0.74/0.98  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.74/0.98  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.74/0.98  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.74/0.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.74/0.98  thf(sk_B_type, type, sk_B: $i > $i).
% 0.74/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.74/0.98  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.74/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.74/0.98  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.74/0.98  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.74/0.98  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.74/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.74/0.98  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.74/0.98  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.74/0.98  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 0.74/0.98  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.74/0.98  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.74/0.98  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.74/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.74/0.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.74/0.98  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.74/0.98  thf(t46_orders_2, conjecture,
% 0.74/0.98    (![A:$i]:
% 0.74/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.74/0.98         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.74/0.98       ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 0.74/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.74/0.98    (~( ![A:$i]:
% 0.74/0.98        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.74/0.98            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.74/0.98          ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 0.74/0.98    inference('cnf.neg', [status(esa)], [t46_orders_2])).
% 0.74/0.98  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.74/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.98  thf(d3_struct_0, axiom,
% 0.74/0.98    (![A:$i]:
% 0.74/0.98     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.74/0.98  thf('1', plain,
% 0.74/0.98      (![X8 : $i]:
% 0.74/0.98         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.74/0.98      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.74/0.98  thf(t9_mcart_1, axiom,
% 0.74/0.98    (![A:$i]:
% 0.74/0.98     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.74/0.98          ( ![B:$i]:
% 0.74/0.98            ( ~( ( r2_hidden @ B @ A ) & 
% 0.74/0.98                 ( ![C:$i,D:$i]:
% 0.74/0.98                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.74/0.98                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.74/0.98  thf('2', plain,
% 0.74/0.98      (![X5 : $i]: (((X5) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X5) @ X5))),
% 0.74/0.98      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.74/0.98  thf(dt_k2_struct_0, axiom,
% 0.74/0.98    (![A:$i]:
% 0.74/0.98     ( ( l1_struct_0 @ A ) =>
% 0.74/0.98       ( m1_subset_1 @
% 0.74/0.98         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.74/0.98  thf('3', plain,
% 0.74/0.98      (![X9 : $i]:
% 0.74/0.98         ((m1_subset_1 @ (k2_struct_0 @ X9) @ 
% 0.74/0.98           (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.74/0.98          | ~ (l1_struct_0 @ X9))),
% 0.74/0.98      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.74/0.98  thf(d13_orders_2, axiom,
% 0.74/0.98    (![A:$i]:
% 0.74/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.74/0.98         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.74/0.98       ( ![B:$i]:
% 0.74/0.98         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.74/0.98           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 0.74/0.98  thf('4', plain,
% 0.74/0.98      (![X13 : $i, X14 : $i]:
% 0.74/0.98         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 0.74/0.98          | ((k2_orders_2 @ X14 @ X13) = (a_2_1_orders_2 @ X14 @ X13))
% 0.74/0.98          | ~ (l1_orders_2 @ X14)
% 0.74/0.98          | ~ (v5_orders_2 @ X14)
% 0.74/0.98          | ~ (v4_orders_2 @ X14)
% 0.74/0.98          | ~ (v3_orders_2 @ X14)
% 0.74/0.98          | (v2_struct_0 @ X14))),
% 0.74/0.98      inference('cnf', [status(esa)], [d13_orders_2])).
% 0.74/0.98  thf('5', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (~ (l1_struct_0 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 0.74/0.98              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.74/0.98      inference('sup-', [status(thm)], ['3', '4'])).
% 0.74/0.98  thf('6', plain,
% 0.74/0.98      (![X9 : $i]:
% 0.74/0.98         ((m1_subset_1 @ (k2_struct_0 @ X9) @ 
% 0.74/0.98           (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.74/0.98          | ~ (l1_struct_0 @ X9))),
% 0.74/0.98      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.74/0.98  thf(fraenkel_a_2_1_orders_2, axiom,
% 0.74/0.98    (![A:$i,B:$i,C:$i]:
% 0.74/0.98     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.74/0.98         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.74/0.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.74/0.98       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 0.74/0.98         ( ?[D:$i]:
% 0.74/0.98           ( ( ![E:$i]:
% 0.74/0.98               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.74/0.98                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 0.74/0.98             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.74/0.98  thf('7', plain,
% 0.74/0.98      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.74/0.98         (~ (l1_orders_2 @ X18)
% 0.74/0.98          | ~ (v5_orders_2 @ X18)
% 0.74/0.98          | ~ (v4_orders_2 @ X18)
% 0.74/0.98          | ~ (v3_orders_2 @ X18)
% 0.74/0.98          | (v2_struct_0 @ X18)
% 0.74/0.98          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.74/0.98          | ((X21) = (sk_D @ X19 @ X18 @ X21))
% 0.74/0.98          | ~ (r2_hidden @ X21 @ (a_2_1_orders_2 @ X18 @ X19)))),
% 0.74/0.98      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.74/0.98  thf('8', plain,
% 0.74/0.98      (![X0 : $i, X1 : $i]:
% 0.74/0.98         (~ (l1_struct_0 @ X0)
% 0.74/0.98          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.74/0.98          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0))),
% 0.74/0.98      inference('sup-', [status(thm)], ['6', '7'])).
% 0.74/0.98  thf('9', plain,
% 0.74/0.98      (![X0 : $i, X1 : $i]:
% 0.74/0.98         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 0.74/0.98          | ~ (l1_struct_0 @ X0))),
% 0.74/0.98      inference('sup-', [status(thm)], ['5', '8'])).
% 0.74/0.98  thf('10', plain,
% 0.74/0.98      (![X0 : $i, X1 : $i]:
% 0.74/0.98         (((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.74/0.98      inference('simplify', [status(thm)], ['9'])).
% 0.74/0.98  thf('11', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.74/0.98              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.74/0.98                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 0.74/0.98      inference('sup-', [status(thm)], ['2', '10'])).
% 0.74/0.98  thf('12', plain,
% 0.74/0.98      (![X5 : $i]: (((X5) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X5) @ X5))),
% 0.74/0.98      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.74/0.98  thf('13', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (~ (l1_struct_0 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 0.74/0.98              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.74/0.98      inference('sup-', [status(thm)], ['3', '4'])).
% 0.74/0.98  thf('14', plain,
% 0.74/0.98      (![X9 : $i]:
% 0.74/0.98         ((m1_subset_1 @ (k2_struct_0 @ X9) @ 
% 0.74/0.98           (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.74/0.98          | ~ (l1_struct_0 @ X9))),
% 0.74/0.98      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.74/0.98  thf('15', plain,
% 0.74/0.98      (![X18 : $i, X19 : $i, X21 : $i]:
% 0.74/0.98         (~ (l1_orders_2 @ X18)
% 0.74/0.98          | ~ (v5_orders_2 @ X18)
% 0.74/0.98          | ~ (v4_orders_2 @ X18)
% 0.74/0.98          | ~ (v3_orders_2 @ X18)
% 0.74/0.98          | (v2_struct_0 @ X18)
% 0.74/0.98          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.74/0.98          | (m1_subset_1 @ (sk_D @ X19 @ X18 @ X21) @ (u1_struct_0 @ X18))
% 0.74/0.98          | ~ (r2_hidden @ X21 @ (a_2_1_orders_2 @ X18 @ X19)))),
% 0.74/0.98      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.74/0.98  thf('16', plain,
% 0.74/0.98      (![X0 : $i, X1 : $i]:
% 0.74/0.98         (~ (l1_struct_0 @ X0)
% 0.74/0.98          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.74/0.98          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 0.74/0.98             (u1_struct_0 @ X0))
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0))),
% 0.74/0.98      inference('sup-', [status(thm)], ['14', '15'])).
% 0.74/0.98  thf('17', plain,
% 0.74/0.98      (![X0 : $i, X1 : $i]:
% 0.74/0.98         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 0.74/0.98             (u1_struct_0 @ X0))
% 0.74/0.98          | ~ (l1_struct_0 @ X0))),
% 0.74/0.98      inference('sup-', [status(thm)], ['13', '16'])).
% 0.74/0.98  thf('18', plain,
% 0.74/0.98      (![X0 : $i, X1 : $i]:
% 0.74/0.98         ((m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 0.74/0.98           (u1_struct_0 @ X0))
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.74/0.98      inference('simplify', [status(thm)], ['17'])).
% 0.74/0.98  thf('19', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | (m1_subset_1 @ 
% 0.74/0.98             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.74/0.98              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.74/0.98             (u1_struct_0 @ X0)))),
% 0.74/0.98      inference('sup-', [status(thm)], ['12', '18'])).
% 0.74/0.98  thf('20', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.74/0.98           (u1_struct_0 @ X0))
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.74/0.98      inference('sup+', [status(thm)], ['11', '19'])).
% 0.74/0.98  thf('21', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.74/0.98             (u1_struct_0 @ X0)))),
% 0.74/0.98      inference('simplify', [status(thm)], ['20'])).
% 0.74/0.98  thf('22', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.74/0.98           (k2_struct_0 @ X0))
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.74/0.98      inference('sup+', [status(thm)], ['1', '21'])).
% 0.74/0.98  thf('23', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.74/0.98             (k2_struct_0 @ X0)))),
% 0.74/0.98      inference('simplify', [status(thm)], ['22'])).
% 0.74/0.98  thf(t2_subset, axiom,
% 0.74/0.98    (![A:$i,B:$i]:
% 0.74/0.98     ( ( m1_subset_1 @ A @ B ) =>
% 0.74/0.98       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.74/0.98  thf('24', plain,
% 0.74/0.98      (![X0 : $i, X1 : $i]:
% 0.74/0.98         ((r2_hidden @ X0 @ X1)
% 0.74/0.98          | (v1_xboole_0 @ X1)
% 0.74/0.98          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.74/0.98      inference('cnf', [status(esa)], [t2_subset])).
% 0.74/0.98  thf('25', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (~ (l1_struct_0 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.74/0.98          | (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.74/0.98             (k2_struct_0 @ X0)))),
% 0.74/0.98      inference('sup-', [status(thm)], ['23', '24'])).
% 0.74/0.98  thf('26', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.74/0.98             (u1_struct_0 @ X0)))),
% 0.74/0.98      inference('simplify', [status(thm)], ['20'])).
% 0.74/0.98  thf('27', plain,
% 0.74/0.98      (![X5 : $i]: (((X5) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X5) @ X5))),
% 0.74/0.98      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.74/0.98  thf('28', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (~ (l1_struct_0 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 0.74/0.98              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.74/0.98      inference('sup-', [status(thm)], ['3', '4'])).
% 0.74/0.98  thf('29', plain,
% 0.74/0.98      (![X9 : $i]:
% 0.74/0.98         ((m1_subset_1 @ (k2_struct_0 @ X9) @ 
% 0.74/0.98           (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.74/0.98          | ~ (l1_struct_0 @ X9))),
% 0.74/0.98      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.74/0.98  thf('30', plain,
% 0.74/0.98      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.74/0.98         (~ (l1_orders_2 @ X18)
% 0.74/0.98          | ~ (v5_orders_2 @ X18)
% 0.74/0.98          | ~ (v4_orders_2 @ X18)
% 0.74/0.98          | ~ (v3_orders_2 @ X18)
% 0.74/0.98          | (v2_struct_0 @ X18)
% 0.74/0.98          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.74/0.98          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X18))
% 0.74/0.98          | (r2_orders_2 @ X18 @ (sk_D @ X19 @ X18 @ X21) @ X20)
% 0.74/0.98          | ~ (r2_hidden @ X20 @ X19)
% 0.74/0.98          | ~ (r2_hidden @ X21 @ (a_2_1_orders_2 @ X18 @ X19)))),
% 0.74/0.98      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.74/0.98  thf('31', plain,
% 0.74/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.98         (~ (l1_struct_0 @ X0)
% 0.74/0.98          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.74/0.98          | ~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 0.74/0.98          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 0.74/0.98          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0))),
% 0.74/0.98      inference('sup-', [status(thm)], ['29', '30'])).
% 0.74/0.98  thf('32', plain,
% 0.74/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.98         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.74/0.98          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 0.74/0.98          | ~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 0.74/0.98          | ~ (l1_struct_0 @ X0))),
% 0.74/0.98      inference('sup-', [status(thm)], ['28', '31'])).
% 0.74/0.98  thf('33', plain,
% 0.74/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.74/0.98         (~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 0.74/0.98          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 0.74/0.98          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.74/0.98      inference('simplify', [status(thm)], ['32'])).
% 0.74/0.98  thf('34', plain,
% 0.74/0.98      (![X0 : $i, X1 : $i]:
% 0.74/0.98         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.74/0.98          | (r2_orders_2 @ X0 @ 
% 0.74/0.98             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.74/0.98              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.74/0.98             X1)
% 0.74/0.98          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0)))),
% 0.74/0.98      inference('sup-', [status(thm)], ['27', '33'])).
% 0.74/0.98  thf('35', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (~ (l1_struct_0 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.74/0.98               (k2_struct_0 @ X0))
% 0.74/0.98          | (r2_orders_2 @ X0 @ 
% 0.74/0.98             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.74/0.98              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.74/0.98             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.74/0.98      inference('sup-', [status(thm)], ['26', '34'])).
% 0.74/0.98  thf('36', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         ((r2_orders_2 @ X0 @ 
% 0.74/0.98           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.74/0.98            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.74/0.98           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 0.74/0.98          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.74/0.98               (k2_struct_0 @ X0))
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0))),
% 0.74/0.98      inference('simplify', [status(thm)], ['35'])).
% 0.74/0.98  thf('37', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | (r2_orders_2 @ X0 @ 
% 0.74/0.98             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.74/0.98              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.74/0.98             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 0.74/0.98      inference('sup-', [status(thm)], ['25', '36'])).
% 0.74/0.98  thf('38', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         ((r2_orders_2 @ X0 @ 
% 0.74/0.98           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.74/0.98            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.74/0.98           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.74/0.98      inference('simplify', [status(thm)], ['37'])).
% 0.74/0.98  thf('39', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.74/0.98              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.74/0.98                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 0.74/0.98      inference('sup-', [status(thm)], ['2', '10'])).
% 0.74/0.98  thf('40', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | (m1_subset_1 @ 
% 0.74/0.98             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.74/0.98              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.74/0.98             (u1_struct_0 @ X0)))),
% 0.74/0.98      inference('sup-', [status(thm)], ['12', '18'])).
% 0.74/0.98  thf(d10_orders_2, axiom,
% 0.74/0.98    (![A:$i]:
% 0.74/0.98     ( ( l1_orders_2 @ A ) =>
% 0.74/0.98       ( ![B:$i]:
% 0.74/0.98         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.74/0.98           ( ![C:$i]:
% 0.74/0.98             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.74/0.98               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.74/0.98                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 0.74/0.98  thf('41', plain,
% 0.74/0.98      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.74/0.98         (~ (m1_subset_1 @ X10 @ (u1_struct_0 @ X11))
% 0.74/0.98          | ~ (r2_orders_2 @ X11 @ X10 @ X12)
% 0.74/0.98          | ((X10) != (X12))
% 0.74/0.98          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11))
% 0.74/0.98          | ~ (l1_orders_2 @ X11))),
% 0.74/0.98      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.74/0.98  thf('42', plain,
% 0.74/0.98      (![X11 : $i, X12 : $i]:
% 0.74/0.98         (~ (l1_orders_2 @ X11)
% 0.74/0.98          | ~ (r2_orders_2 @ X11 @ X12 @ X12)
% 0.74/0.98          | ~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X11)))),
% 0.74/0.98      inference('simplify', [status(thm)], ['41'])).
% 0.74/0.98  thf('43', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (~ (l1_struct_0 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | ~ (r2_orders_2 @ X0 @ 
% 0.74/0.98               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.74/0.98                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.74/0.98               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.74/0.98                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 0.74/0.98          | ~ (l1_orders_2 @ X0))),
% 0.74/0.98      inference('sup-', [status(thm)], ['40', '42'])).
% 0.74/0.98  thf('44', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (~ (r2_orders_2 @ X0 @ 
% 0.74/0.98             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.74/0.98              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.74/0.98             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.74/0.98              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0))),
% 0.74/0.98      inference('simplify', [status(thm)], ['43'])).
% 0.74/0.98  thf('45', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (~ (r2_orders_2 @ X0 @ 
% 0.74/0.98             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.74/0.98              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.74/0.98             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.74/0.98      inference('sup-', [status(thm)], ['39', '44'])).
% 0.74/0.98  thf('46', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | ~ (r2_orders_2 @ X0 @ 
% 0.74/0.98               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.74/0.98                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.74/0.98               (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 0.74/0.98      inference('simplify', [status(thm)], ['45'])).
% 0.74/0.98  thf('47', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.74/0.98      inference('sup-', [status(thm)], ['38', '46'])).
% 0.74/0.98  thf('48', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (~ (l1_struct_0 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.74/0.98      inference('simplify', [status(thm)], ['47'])).
% 0.74/0.98  thf('49', plain,
% 0.74/0.98      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 0.74/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.98  thf('50', plain,
% 0.74/0.98      ((((k1_xboole_0) != (k1_xboole_0))
% 0.74/0.98        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.74/0.98        | ~ (l1_orders_2 @ sk_A)
% 0.74/0.98        | ~ (v5_orders_2 @ sk_A)
% 0.74/0.98        | ~ (v4_orders_2 @ sk_A)
% 0.74/0.98        | ~ (v3_orders_2 @ sk_A)
% 0.74/0.98        | (v2_struct_0 @ sk_A)
% 0.74/0.98        | ~ (l1_struct_0 @ sk_A))),
% 0.74/0.98      inference('sup-', [status(thm)], ['48', '49'])).
% 0.74/0.98  thf('51', plain, ((l1_orders_2 @ sk_A)),
% 0.74/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.98  thf('52', plain, ((v5_orders_2 @ sk_A)),
% 0.74/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.98  thf('53', plain, ((v4_orders_2 @ sk_A)),
% 0.74/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.98  thf('54', plain, ((v3_orders_2 @ sk_A)),
% 0.74/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.98  thf('55', plain, ((l1_orders_2 @ sk_A)),
% 0.74/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.98  thf(dt_l1_orders_2, axiom,
% 0.74/0.98    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.74/0.98  thf('56', plain,
% 0.74/0.98      (![X17 : $i]: ((l1_struct_0 @ X17) | ~ (l1_orders_2 @ X17))),
% 0.74/0.98      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.74/0.98  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.74/0.98      inference('sup-', [status(thm)], ['55', '56'])).
% 0.74/0.98  thf('58', plain,
% 0.74/0.98      ((((k1_xboole_0) != (k1_xboole_0))
% 0.74/0.98        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.74/0.98        | (v2_struct_0 @ sk_A))),
% 0.74/0.98      inference('demod', [status(thm)], ['50', '51', '52', '53', '54', '57'])).
% 0.74/0.98  thf('59', plain,
% 0.74/0.98      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.74/0.98      inference('simplify', [status(thm)], ['58'])).
% 0.74/0.98  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.74/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.98  thf('61', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.74/0.98      inference('clc', [status(thm)], ['59', '60'])).
% 0.74/0.98  thf('62', plain,
% 0.74/0.98      (![X8 : $i]:
% 0.74/0.98         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 0.74/0.98      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.74/0.98  thf('63', plain,
% 0.74/0.98      (![X5 : $i]: (((X5) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X5) @ X5))),
% 0.74/0.98      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.74/0.98  thf('64', plain,
% 0.74/0.98      (![X9 : $i]:
% 0.74/0.98         ((m1_subset_1 @ (k2_struct_0 @ X9) @ 
% 0.74/0.98           (k1_zfmisc_1 @ (u1_struct_0 @ X9)))
% 0.74/0.98          | ~ (l1_struct_0 @ X9))),
% 0.74/0.98      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.74/0.98  thf(dt_k2_orders_2, axiom,
% 0.74/0.98    (![A:$i,B:$i]:
% 0.74/0.98     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.74/0.98         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.74/0.98         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.74/0.98       ( m1_subset_1 @
% 0.74/0.98         ( k2_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.74/0.98  thf('65', plain,
% 0.74/0.98      (![X15 : $i, X16 : $i]:
% 0.74/0.98         (~ (l1_orders_2 @ X15)
% 0.74/0.98          | ~ (v5_orders_2 @ X15)
% 0.74/0.98          | ~ (v4_orders_2 @ X15)
% 0.74/0.98          | ~ (v3_orders_2 @ X15)
% 0.74/0.98          | (v2_struct_0 @ X15)
% 0.74/0.98          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 0.74/0.98          | (m1_subset_1 @ (k2_orders_2 @ X15 @ X16) @ 
% 0.74/0.98             (k1_zfmisc_1 @ (u1_struct_0 @ X15))))),
% 0.74/0.98      inference('cnf', [status(esa)], [dt_k2_orders_2])).
% 0.74/0.98  thf('66', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (~ (l1_struct_0 @ X0)
% 0.74/0.98          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.74/0.98             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0))),
% 0.74/0.98      inference('sup-', [status(thm)], ['64', '65'])).
% 0.74/0.98  thf(t5_subset, axiom,
% 0.74/0.98    (![A:$i,B:$i,C:$i]:
% 0.74/0.98     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.74/0.98          ( v1_xboole_0 @ C ) ) ))).
% 0.74/0.98  thf('67', plain,
% 0.74/0.98      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.74/0.98         (~ (r2_hidden @ X2 @ X3)
% 0.74/0.98          | ~ (v1_xboole_0 @ X4)
% 0.74/0.98          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 0.74/0.98      inference('cnf', [status(esa)], [t5_subset])).
% 0.74/0.98  thf('68', plain,
% 0.74/0.98      (![X0 : $i, X1 : $i]:
% 0.74/0.98         (~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.74/0.98          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.74/0.98      inference('sup-', [status(thm)], ['66', '67'])).
% 0.74/0.98  thf('69', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0))),
% 0.74/0.98      inference('sup-', [status(thm)], ['63', '68'])).
% 0.74/0.98  thf('70', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.74/0.98      inference('sup-', [status(thm)], ['62', '69'])).
% 0.74/0.98  thf('71', plain,
% 0.74/0.98      (![X0 : $i]:
% 0.74/0.98         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.74/0.98          | (v2_struct_0 @ X0)
% 0.74/0.98          | ~ (v3_orders_2 @ X0)
% 0.74/0.98          | ~ (v4_orders_2 @ X0)
% 0.74/0.98          | ~ (v5_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_orders_2 @ X0)
% 0.74/0.98          | ~ (l1_struct_0 @ X0)
% 0.74/0.98          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.74/0.98      inference('simplify', [status(thm)], ['70'])).
% 0.74/0.98  thf('72', plain,
% 0.74/0.98      ((~ (l1_struct_0 @ sk_A)
% 0.74/0.98        | ~ (l1_orders_2 @ sk_A)
% 0.74/0.98        | ~ (v5_orders_2 @ sk_A)
% 0.74/0.98        | ~ (v4_orders_2 @ sk_A)
% 0.74/0.98        | ~ (v3_orders_2 @ sk_A)
% 0.74/0.98        | (v2_struct_0 @ sk_A)
% 0.74/0.98        | ((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0)))),
% 0.74/0.98      inference('sup-', [status(thm)], ['61', '71'])).
% 0.74/0.98  thf('73', plain, ((l1_struct_0 @ sk_A)),
% 0.74/0.98      inference('sup-', [status(thm)], ['55', '56'])).
% 0.74/0.98  thf('74', plain, ((l1_orders_2 @ sk_A)),
% 0.74/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.98  thf('75', plain, ((v5_orders_2 @ sk_A)),
% 0.74/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.98  thf('76', plain, ((v4_orders_2 @ sk_A)),
% 0.74/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.98  thf('77', plain, ((v3_orders_2 @ sk_A)),
% 0.74/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.98  thf('78', plain,
% 0.74/0.98      (((v2_struct_0 @ sk_A)
% 0.74/0.98        | ((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0)))),
% 0.74/0.98      inference('demod', [status(thm)], ['72', '73', '74', '75', '76', '77'])).
% 0.74/0.98  thf('79', plain,
% 0.74/0.98      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 0.74/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.74/0.99  thf('80', plain, ((v2_struct_0 @ sk_A)),
% 0.74/0.99      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 0.74/0.99  thf('81', plain, ($false), inference('demod', [status(thm)], ['0', '80'])).
% 0.74/0.99  
% 0.74/0.99  % SZS output end Refutation
% 0.74/0.99  
% 0.74/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
