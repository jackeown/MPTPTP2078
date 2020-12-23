%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6x65NdRTEA

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:40 EST 2020

% Result     : Theorem 54.41s
% Output     : Refutation 54.41s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 205 expanded)
%              Number of leaves         :   31 (  75 expanded)
%              Depth                    :   23
%              Number of atoms          : 1503 (2576 expanded)
%              Number of equality atoms :   58 (  87 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_orders_2_type,type,(
    k1_orders_2: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(a_2_0_orders_2_type,type,(
    a_2_0_orders_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('3',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
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

thf('8',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X13 ) ) )
      | ( ( k1_orders_2 @ X13 @ X12 )
        = ( a_2_0_orders_2 @ X13 @ X12 ) )
      | ~ ( l1_orders_2 @ X13 )
      | ~ ( v5_orders_2 @ X13 )
      | ~ ( v4_orders_2 @ X13 )
      | ~ ( v3_orders_2 @ X13 )
      | ( v2_struct_0 @ X13 ) ) ),
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

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(dt_k1_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('12',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k1_orders_2 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_orders_2])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_tarski @ ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('20',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

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

thf('22',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( X20
        = ( sk_D @ X18 @ X17 @ X20 ) )
      | ~ ( r2_hidden @ X20 @ ( a_2_0_orders_2 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('27',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X18 @ X17 @ X20 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( r2_hidden @ X20 @ ( a_2_0_orders_2 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['19','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('36',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( r2_orders_2 @ X17 @ X19 @ ( sk_D @ X18 @ X17 @ X20 ) )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( a_2_0_orders_2 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_0_orders_2])).

thf('37',plain,(
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
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ X1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( r2_orders_2 @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['18','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

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

thf('46',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r2_orders_2 @ X10 @ X9 @ X11 )
      | ( X9 != X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ~ ( r2_orders_2 @ X10 @ X11 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_orders_2 @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( r2_orders_2 @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( r2_orders_2 @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_orders_2 @ X0 @ ( sk_B @ ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( a_2_0_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','57'])).

thf('59',plain,(
    ( k1_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
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
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('66',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62','63','64','67'])).

thf('69',plain,(
    v2_struct_0 @ sk_A ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['0','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6x65NdRTEA
% 0.17/0.39  % Computer   : n008.cluster.edu
% 0.17/0.39  % Model      : x86_64 x86_64
% 0.17/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.39  % Memory     : 8042.1875MB
% 0.17/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.39  % CPULimit   : 60
% 0.17/0.39  % DateTime   : Tue Dec  1 12:14:30 EST 2020
% 0.17/0.39  % CPUTime    : 
% 0.17/0.39  % Running portfolio for 600 s
% 0.17/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.39  % Number of cores: 8
% 0.17/0.40  % Python version: Python 3.6.8
% 0.17/0.40  % Running in FO mode
% 54.41/54.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 54.41/54.60  % Solved by: fo/fo7.sh
% 54.41/54.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 54.41/54.60  % done 36328 iterations in 54.098s
% 54.41/54.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 54.41/54.60  % SZS output start Refutation
% 54.41/54.60  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 54.41/54.60  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 54.41/54.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 54.41/54.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 54.41/54.60  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 54.41/54.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 54.41/54.60  thf(k1_orders_2_type, type, k1_orders_2: $i > $i > $i).
% 54.41/54.60  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 54.41/54.60  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 54.41/54.60  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 54.41/54.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 54.41/54.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 54.41/54.60  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 54.41/54.60  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 54.41/54.60  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 54.41/54.60  thf(a_2_0_orders_2_type, type, a_2_0_orders_2: $i > $i > $i).
% 54.41/54.60  thf(sk_B_type, type, sk_B: $i > $i).
% 54.41/54.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 54.41/54.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 54.41/54.60  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 54.41/54.60  thf(sk_A_type, type, sk_A: $i).
% 54.41/54.60  thf(t44_orders_2, conjecture,
% 54.41/54.60    (![A:$i]:
% 54.41/54.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 54.41/54.60         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 54.41/54.60       ( ( k1_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 54.41/54.60  thf(zf_stmt_0, negated_conjecture,
% 54.41/54.60    (~( ![A:$i]:
% 54.41/54.60        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 54.41/54.60            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 54.41/54.60          ( ( k1_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 54.41/54.60    inference('cnf.neg', [status(esa)], [t44_orders_2])).
% 54.41/54.60  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 54.41/54.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.41/54.60  thf(d3_struct_0, axiom,
% 54.41/54.60    (![A:$i]:
% 54.41/54.60     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 54.41/54.60  thf('1', plain,
% 54.41/54.60      (![X8 : $i]:
% 54.41/54.60         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 54.41/54.60      inference('cnf', [status(esa)], [d3_struct_0])).
% 54.41/54.60  thf(d3_tarski, axiom,
% 54.41/54.60    (![A:$i,B:$i]:
% 54.41/54.60     ( ( r1_tarski @ A @ B ) <=>
% 54.41/54.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 54.41/54.60  thf('2', plain,
% 54.41/54.60      (![X1 : $i, X3 : $i]:
% 54.41/54.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 54.41/54.60      inference('cnf', [status(esa)], [d3_tarski])).
% 54.41/54.60  thf('3', plain,
% 54.41/54.60      (![X1 : $i, X3 : $i]:
% 54.41/54.60         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 54.41/54.60      inference('cnf', [status(esa)], [d3_tarski])).
% 54.41/54.60  thf('4', plain,
% 54.41/54.60      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 54.41/54.60      inference('sup-', [status(thm)], ['2', '3'])).
% 54.41/54.60  thf('5', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 54.41/54.60      inference('simplify', [status(thm)], ['4'])).
% 54.41/54.60  thf(t3_subset, axiom,
% 54.41/54.60    (![A:$i,B:$i]:
% 54.41/54.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 54.41/54.60  thf('6', plain,
% 54.41/54.60      (![X5 : $i, X7 : $i]:
% 54.41/54.60         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 54.41/54.60      inference('cnf', [status(esa)], [t3_subset])).
% 54.41/54.60  thf('7', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 54.41/54.60      inference('sup-', [status(thm)], ['5', '6'])).
% 54.41/54.60  thf(d12_orders_2, axiom,
% 54.41/54.60    (![A:$i]:
% 54.41/54.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 54.41/54.60         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 54.41/54.60       ( ![B:$i]:
% 54.41/54.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 54.41/54.60           ( ( k1_orders_2 @ A @ B ) = ( a_2_0_orders_2 @ A @ B ) ) ) ) ))).
% 54.41/54.60  thf('8', plain,
% 54.41/54.60      (![X12 : $i, X13 : $i]:
% 54.41/54.60         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 54.41/54.60          | ((k1_orders_2 @ X13 @ X12) = (a_2_0_orders_2 @ X13 @ X12))
% 54.41/54.60          | ~ (l1_orders_2 @ X13)
% 54.41/54.60          | ~ (v5_orders_2 @ X13)
% 54.41/54.60          | ~ (v4_orders_2 @ X13)
% 54.41/54.60          | ~ (v3_orders_2 @ X13)
% 54.41/54.60          | (v2_struct_0 @ X13))),
% 54.41/54.60      inference('cnf', [status(esa)], [d12_orders_2])).
% 54.41/54.60  thf('9', plain,
% 54.41/54.60      (![X0 : $i]:
% 54.41/54.60         ((v2_struct_0 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | ((k1_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 54.41/54.60              = (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 54.41/54.60      inference('sup-', [status(thm)], ['7', '8'])).
% 54.41/54.60  thf(t7_xboole_0, axiom,
% 54.41/54.60    (![A:$i]:
% 54.41/54.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 54.41/54.60          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 54.41/54.60  thf('10', plain,
% 54.41/54.60      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 54.41/54.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 54.41/54.60  thf('11', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 54.41/54.60      inference('sup-', [status(thm)], ['5', '6'])).
% 54.41/54.60  thf(dt_k1_orders_2, axiom,
% 54.41/54.60    (![A:$i,B:$i]:
% 54.41/54.60     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 54.41/54.60         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 54.41/54.60         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 54.41/54.60       ( m1_subset_1 @
% 54.41/54.60         ( k1_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 54.41/54.60  thf('12', plain,
% 54.41/54.60      (![X14 : $i, X15 : $i]:
% 54.41/54.60         (~ (l1_orders_2 @ X14)
% 54.41/54.60          | ~ (v5_orders_2 @ X14)
% 54.41/54.60          | ~ (v4_orders_2 @ X14)
% 54.41/54.60          | ~ (v3_orders_2 @ X14)
% 54.41/54.60          | (v2_struct_0 @ X14)
% 54.41/54.60          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 54.41/54.60          | (m1_subset_1 @ (k1_orders_2 @ X14 @ X15) @ 
% 54.41/54.60             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 54.41/54.60      inference('cnf', [status(esa)], [dt_k1_orders_2])).
% 54.41/54.60  thf('13', plain,
% 54.41/54.60      (![X0 : $i]:
% 54.41/54.60         ((m1_subset_1 @ (k1_orders_2 @ X0 @ (u1_struct_0 @ X0)) @ 
% 54.41/54.60           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 54.41/54.60          | (v2_struct_0 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (l1_orders_2 @ X0))),
% 54.41/54.60      inference('sup-', [status(thm)], ['11', '12'])).
% 54.41/54.60  thf('14', plain,
% 54.41/54.60      (![X5 : $i, X6 : $i]:
% 54.41/54.60         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 54.41/54.60      inference('cnf', [status(esa)], [t3_subset])).
% 54.41/54.60  thf('15', plain,
% 54.41/54.60      (![X0 : $i]:
% 54.41/54.60         (~ (l1_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | (v2_struct_0 @ X0)
% 54.41/54.60          | (r1_tarski @ (k1_orders_2 @ X0 @ (u1_struct_0 @ X0)) @ 
% 54.41/54.60             (u1_struct_0 @ X0)))),
% 54.41/54.60      inference('sup-', [status(thm)], ['13', '14'])).
% 54.41/54.60  thf('16', plain,
% 54.41/54.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.41/54.60         (~ (r2_hidden @ X0 @ X1)
% 54.41/54.60          | (r2_hidden @ X0 @ X2)
% 54.41/54.60          | ~ (r1_tarski @ X1 @ X2))),
% 54.41/54.60      inference('cnf', [status(esa)], [d3_tarski])).
% 54.41/54.60  thf('17', plain,
% 54.41/54.60      (![X0 : $i, X1 : $i]:
% 54.41/54.60         ((v2_struct_0 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 54.41/54.60          | ~ (r2_hidden @ X1 @ (k1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 54.41/54.60      inference('sup-', [status(thm)], ['15', '16'])).
% 54.41/54.60  thf('18', plain,
% 54.41/54.60      (![X0 : $i]:
% 54.41/54.60         (((k1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.60          | (r2_hidden @ (sk_B @ (k1_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 54.41/54.60             (u1_struct_0 @ X0))
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | (v2_struct_0 @ X0))),
% 54.41/54.60      inference('sup-', [status(thm)], ['10', '17'])).
% 54.41/54.60  thf('19', plain,
% 54.41/54.60      (![X0 : $i]:
% 54.41/54.60         ((v2_struct_0 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | ((k1_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 54.41/54.60              = (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 54.41/54.60      inference('sup-', [status(thm)], ['7', '8'])).
% 54.41/54.60  thf('20', plain,
% 54.41/54.60      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 54.41/54.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 54.41/54.60  thf('21', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 54.41/54.60      inference('sup-', [status(thm)], ['5', '6'])).
% 54.41/54.60  thf(fraenkel_a_2_0_orders_2, axiom,
% 54.41/54.60    (![A:$i,B:$i,C:$i]:
% 54.41/54.60     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 54.41/54.60         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 54.41/54.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 54.41/54.60       ( ( r2_hidden @ A @ ( a_2_0_orders_2 @ B @ C ) ) <=>
% 54.41/54.60         ( ?[D:$i]:
% 54.41/54.60           ( ( ![E:$i]:
% 54.41/54.60               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 54.41/54.60                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ E @ D ) ) ) ) & 
% 54.41/54.60             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 54.41/54.60  thf('22', plain,
% 54.41/54.60      (![X17 : $i, X18 : $i, X20 : $i]:
% 54.41/54.60         (~ (l1_orders_2 @ X17)
% 54.41/54.60          | ~ (v5_orders_2 @ X17)
% 54.41/54.60          | ~ (v4_orders_2 @ X17)
% 54.41/54.60          | ~ (v3_orders_2 @ X17)
% 54.41/54.60          | (v2_struct_0 @ X17)
% 54.41/54.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 54.41/54.60          | ((X20) = (sk_D @ X18 @ X17 @ X20))
% 54.41/54.60          | ~ (r2_hidden @ X20 @ (a_2_0_orders_2 @ X17 @ X18)))),
% 54.41/54.60      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 54.41/54.60  thf('23', plain,
% 54.41/54.60      (![X0 : $i, X1 : $i]:
% 54.41/54.60         (~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 54.41/54.60          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 54.41/54.60          | (v2_struct_0 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (l1_orders_2 @ X0))),
% 54.41/54.60      inference('sup-', [status(thm)], ['21', '22'])).
% 54.41/54.60  thf('24', plain,
% 54.41/54.60      (![X0 : $i]:
% 54.41/54.60         (((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | (v2_struct_0 @ X0)
% 54.41/54.60          | ((sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 54.41/54.60              = (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 54.41/54.60                 (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0))))))),
% 54.41/54.60      inference('sup-', [status(thm)], ['20', '23'])).
% 54.41/54.60  thf('25', plain,
% 54.41/54.60      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 54.41/54.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 54.41/54.60  thf('26', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 54.41/54.60      inference('sup-', [status(thm)], ['5', '6'])).
% 54.41/54.60  thf('27', plain,
% 54.41/54.60      (![X17 : $i, X18 : $i, X20 : $i]:
% 54.41/54.60         (~ (l1_orders_2 @ X17)
% 54.41/54.60          | ~ (v5_orders_2 @ X17)
% 54.41/54.60          | ~ (v4_orders_2 @ X17)
% 54.41/54.60          | ~ (v3_orders_2 @ X17)
% 54.41/54.60          | (v2_struct_0 @ X17)
% 54.41/54.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 54.41/54.60          | (m1_subset_1 @ (sk_D @ X18 @ X17 @ X20) @ (u1_struct_0 @ X17))
% 54.41/54.60          | ~ (r2_hidden @ X20 @ (a_2_0_orders_2 @ X17 @ X18)))),
% 54.41/54.60      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 54.41/54.60  thf('28', plain,
% 54.41/54.60      (![X0 : $i, X1 : $i]:
% 54.41/54.60         (~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 54.41/54.60          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 54.41/54.60             (u1_struct_0 @ X0))
% 54.41/54.60          | (v2_struct_0 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (l1_orders_2 @ X0))),
% 54.41/54.60      inference('sup-', [status(thm)], ['26', '27'])).
% 54.41/54.60  thf('29', plain,
% 54.41/54.60      (![X0 : $i]:
% 54.41/54.60         (((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | (v2_struct_0 @ X0)
% 54.41/54.60          | (m1_subset_1 @ 
% 54.41/54.60             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 54.41/54.60              (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))) @ 
% 54.41/54.60             (u1_struct_0 @ X0)))),
% 54.41/54.60      inference('sup-', [status(thm)], ['25', '28'])).
% 54.41/54.60  thf('30', plain,
% 54.41/54.60      (![X0 : $i]:
% 54.41/54.60         ((m1_subset_1 @ (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 54.41/54.60           (u1_struct_0 @ X0))
% 54.41/54.60          | (v2_struct_0 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | ((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.60          | (v2_struct_0 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | ((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0)))),
% 54.41/54.60      inference('sup+', [status(thm)], ['24', '29'])).
% 54.41/54.60  thf('31', plain,
% 54.41/54.60      (![X0 : $i]:
% 54.41/54.60         (((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | (v2_struct_0 @ X0)
% 54.41/54.60          | (m1_subset_1 @ 
% 54.41/54.60             (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 54.41/54.60             (u1_struct_0 @ X0)))),
% 54.41/54.60      inference('simplify', [status(thm)], ['30'])).
% 54.41/54.60  thf('32', plain,
% 54.41/54.60      (![X0 : $i]:
% 54.41/54.60         ((m1_subset_1 @ (sk_B @ (k1_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 54.41/54.60           (u1_struct_0 @ X0))
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | (v2_struct_0 @ X0)
% 54.41/54.60          | (v2_struct_0 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | ((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0)))),
% 54.41/54.60      inference('sup+', [status(thm)], ['19', '31'])).
% 54.41/54.60  thf('33', plain,
% 54.41/54.60      (![X0 : $i]:
% 54.41/54.60         (((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.60          | (v2_struct_0 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | (m1_subset_1 @ (sk_B @ (k1_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 54.41/54.60             (u1_struct_0 @ X0)))),
% 54.41/54.60      inference('simplify', [status(thm)], ['32'])).
% 54.41/54.60  thf('34', plain,
% 54.41/54.60      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 54.41/54.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 54.41/54.60  thf('35', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 54.41/54.60      inference('sup-', [status(thm)], ['5', '6'])).
% 54.41/54.60  thf('36', plain,
% 54.41/54.60      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 54.41/54.60         (~ (l1_orders_2 @ X17)
% 54.41/54.60          | ~ (v5_orders_2 @ X17)
% 54.41/54.60          | ~ (v4_orders_2 @ X17)
% 54.41/54.60          | ~ (v3_orders_2 @ X17)
% 54.41/54.60          | (v2_struct_0 @ X17)
% 54.41/54.60          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 54.41/54.60          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 54.41/54.60          | (r2_orders_2 @ X17 @ X19 @ (sk_D @ X18 @ X17 @ X20))
% 54.41/54.60          | ~ (r2_hidden @ X19 @ X18)
% 54.41/54.60          | ~ (r2_hidden @ X20 @ (a_2_0_orders_2 @ X17 @ X18)))),
% 54.41/54.60      inference('cnf', [status(esa)], [fraenkel_a_2_0_orders_2])).
% 54.41/54.60  thf('37', plain,
% 54.41/54.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 54.41/54.60         (~ (r2_hidden @ X1 @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 54.41/54.60          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 54.41/54.60          | (r2_orders_2 @ X0 @ X2 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 54.41/54.60          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 54.41/54.60          | (v2_struct_0 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (l1_orders_2 @ X0))),
% 54.41/54.60      inference('sup-', [status(thm)], ['35', '36'])).
% 54.41/54.60  thf('38', plain,
% 54.41/54.60      (![X0 : $i, X1 : $i]:
% 54.41/54.60         (((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | (v2_struct_0 @ X0)
% 54.41/54.60          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 54.41/54.60          | (r2_orders_2 @ X0 @ X1 @ 
% 54.41/54.60             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 54.41/54.60              (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))))
% 54.41/54.60          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0)))),
% 54.41/54.60      inference('sup-', [status(thm)], ['34', '37'])).
% 54.41/54.60  thf('39', plain,
% 54.41/54.60      (![X0 : $i]:
% 54.41/54.60         (~ (l1_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | (v2_struct_0 @ X0)
% 54.41/54.60          | ((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.60          | ~ (r2_hidden @ (sk_B @ (k1_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 54.41/54.60               (u1_struct_0 @ X0))
% 54.41/54.60          | (r2_orders_2 @ X0 @ 
% 54.41/54.60             (sk_B @ (k1_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 54.41/54.60             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 54.41/54.60              (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))))
% 54.41/54.60          | (v2_struct_0 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | ((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0)))),
% 54.41/54.60      inference('sup-', [status(thm)], ['33', '38'])).
% 54.41/54.60  thf('40', plain,
% 54.41/54.60      (![X0 : $i]:
% 54.41/54.60         ((r2_orders_2 @ X0 @ 
% 54.41/54.60           (sk_B @ (k1_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 54.41/54.60           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 54.41/54.60            (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))))
% 54.41/54.60          | ~ (r2_hidden @ (sk_B @ (k1_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 54.41/54.60               (u1_struct_0 @ X0))
% 54.41/54.60          | ((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.60          | (v2_struct_0 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (l1_orders_2 @ X0))),
% 54.41/54.60      inference('simplify', [status(thm)], ['39'])).
% 54.41/54.60  thf('41', plain,
% 54.41/54.60      (![X0 : $i]:
% 54.41/54.60         ((v2_struct_0 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | ((k1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | (v2_struct_0 @ X0)
% 54.41/54.60          | ((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.60          | (r2_orders_2 @ X0 @ 
% 54.41/54.60             (sk_B @ (k1_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 54.41/54.60             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 54.41/54.60              (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0))))))),
% 54.41/54.60      inference('sup-', [status(thm)], ['18', '40'])).
% 54.41/54.60  thf('42', plain,
% 54.41/54.60      (![X0 : $i]:
% 54.41/54.60         ((r2_orders_2 @ X0 @ 
% 54.41/54.60           (sk_B @ (k1_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 54.41/54.60           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 54.41/54.60            (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))))
% 54.41/54.60          | ((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.60          | ((k1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | (v2_struct_0 @ X0))),
% 54.41/54.60      inference('simplify', [status(thm)], ['41'])).
% 54.41/54.60  thf('43', plain,
% 54.41/54.60      (![X0 : $i]:
% 54.41/54.60         ((v2_struct_0 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | ((k1_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 54.41/54.60              = (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 54.41/54.60      inference('sup-', [status(thm)], ['7', '8'])).
% 54.41/54.60  thf('44', plain,
% 54.41/54.60      (![X0 : $i]:
% 54.41/54.60         (((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | (v2_struct_0 @ X0)
% 54.41/54.60          | ((sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 54.41/54.60              = (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 54.41/54.60                 (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0))))))),
% 54.41/54.60      inference('sup-', [status(thm)], ['20', '23'])).
% 54.41/54.60  thf('45', plain,
% 54.41/54.60      (![X0 : $i]:
% 54.41/54.60         (((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | (v2_struct_0 @ X0)
% 54.41/54.60          | (m1_subset_1 @ 
% 54.41/54.60             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 54.41/54.60              (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))) @ 
% 54.41/54.60             (u1_struct_0 @ X0)))),
% 54.41/54.60      inference('sup-', [status(thm)], ['25', '28'])).
% 54.41/54.60  thf(d10_orders_2, axiom,
% 54.41/54.60    (![A:$i]:
% 54.41/54.60     ( ( l1_orders_2 @ A ) =>
% 54.41/54.60       ( ![B:$i]:
% 54.41/54.60         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 54.41/54.60           ( ![C:$i]:
% 54.41/54.60             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 54.41/54.60               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 54.41/54.60                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 54.41/54.60  thf('46', plain,
% 54.41/54.60      (![X9 : $i, X10 : $i, X11 : $i]:
% 54.41/54.60         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 54.41/54.60          | ~ (r2_orders_2 @ X10 @ X9 @ X11)
% 54.41/54.60          | ((X9) != (X11))
% 54.41/54.60          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 54.41/54.60          | ~ (l1_orders_2 @ X10))),
% 54.41/54.60      inference('cnf', [status(esa)], [d10_orders_2])).
% 54.41/54.60  thf('47', plain,
% 54.41/54.60      (![X10 : $i, X11 : $i]:
% 54.41/54.60         (~ (l1_orders_2 @ X10)
% 54.41/54.60          | ~ (r2_orders_2 @ X10 @ X11 @ X11)
% 54.41/54.60          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10)))),
% 54.41/54.60      inference('simplify', [status(thm)], ['46'])).
% 54.41/54.60  thf('48', plain,
% 54.41/54.60      (![X0 : $i]:
% 54.41/54.60         ((v2_struct_0 @ X0)
% 54.41/54.60          | ~ (v3_orders_2 @ X0)
% 54.41/54.60          | ~ (v4_orders_2 @ X0)
% 54.41/54.60          | ~ (v5_orders_2 @ X0)
% 54.41/54.60          | ~ (l1_orders_2 @ X0)
% 54.41/54.60          | ((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.60          | ~ (r2_orders_2 @ X0 @ 
% 54.41/54.60               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 54.41/54.60                (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))) @ 
% 54.41/54.60               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 54.41/54.60                (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))))
% 54.41/54.60          | ~ (l1_orders_2 @ X0))),
% 54.41/54.60      inference('sup-', [status(thm)], ['45', '47'])).
% 54.41/54.60  thf('49', plain,
% 54.41/54.60      (![X0 : $i]:
% 54.41/54.60         (~ (r2_orders_2 @ X0 @ 
% 54.41/54.60             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 54.41/54.60              (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))) @ 
% 54.41/54.61             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 54.41/54.61              (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))))
% 54.41/54.61          | ((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.61          | ~ (l1_orders_2 @ X0)
% 54.41/54.61          | ~ (v5_orders_2 @ X0)
% 54.41/54.61          | ~ (v4_orders_2 @ X0)
% 54.41/54.61          | ~ (v3_orders_2 @ X0)
% 54.41/54.61          | (v2_struct_0 @ X0))),
% 54.41/54.61      inference('simplify', [status(thm)], ['48'])).
% 54.41/54.61  thf('50', plain,
% 54.41/54.61      (![X0 : $i]:
% 54.41/54.61         (~ (r2_orders_2 @ X0 @ 
% 54.41/54.61             (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 54.41/54.61             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 54.41/54.61              (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))))
% 54.41/54.61          | (v2_struct_0 @ X0)
% 54.41/54.61          | ~ (v3_orders_2 @ X0)
% 54.41/54.61          | ~ (v4_orders_2 @ X0)
% 54.41/54.61          | ~ (v5_orders_2 @ X0)
% 54.41/54.61          | ~ (l1_orders_2 @ X0)
% 54.41/54.61          | ((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.61          | (v2_struct_0 @ X0)
% 54.41/54.61          | ~ (v3_orders_2 @ X0)
% 54.41/54.61          | ~ (v4_orders_2 @ X0)
% 54.41/54.61          | ~ (v5_orders_2 @ X0)
% 54.41/54.61          | ~ (l1_orders_2 @ X0)
% 54.41/54.61          | ((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0)))),
% 54.41/54.61      inference('sup-', [status(thm)], ['44', '49'])).
% 54.41/54.61  thf('51', plain,
% 54.41/54.61      (![X0 : $i]:
% 54.41/54.61         (((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.61          | ~ (l1_orders_2 @ X0)
% 54.41/54.61          | ~ (v5_orders_2 @ X0)
% 54.41/54.61          | ~ (v4_orders_2 @ X0)
% 54.41/54.61          | ~ (v3_orders_2 @ X0)
% 54.41/54.61          | (v2_struct_0 @ X0)
% 54.41/54.61          | ~ (r2_orders_2 @ X0 @ 
% 54.41/54.61               (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 54.41/54.61               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 54.41/54.61                (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0))))))),
% 54.41/54.61      inference('simplify', [status(thm)], ['50'])).
% 54.41/54.61  thf('52', plain,
% 54.41/54.61      (![X0 : $i]:
% 54.41/54.61         (~ (r2_orders_2 @ X0 @ 
% 54.41/54.61             (sk_B @ (k1_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 54.41/54.61             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 54.41/54.61              (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)))))
% 54.41/54.61          | ~ (l1_orders_2 @ X0)
% 54.41/54.61          | ~ (v5_orders_2 @ X0)
% 54.41/54.61          | ~ (v4_orders_2 @ X0)
% 54.41/54.61          | ~ (v3_orders_2 @ X0)
% 54.41/54.61          | (v2_struct_0 @ X0)
% 54.41/54.61          | (v2_struct_0 @ X0)
% 54.41/54.61          | ~ (v3_orders_2 @ X0)
% 54.41/54.61          | ~ (v4_orders_2 @ X0)
% 54.41/54.61          | ~ (v5_orders_2 @ X0)
% 54.41/54.61          | ~ (l1_orders_2 @ X0)
% 54.41/54.61          | ((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0)))),
% 54.41/54.61      inference('sup-', [status(thm)], ['43', '51'])).
% 54.41/54.61  thf('53', plain,
% 54.41/54.61      (![X0 : $i]:
% 54.41/54.61         (((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.61          | (v2_struct_0 @ X0)
% 54.41/54.61          | ~ (v3_orders_2 @ X0)
% 54.41/54.61          | ~ (v4_orders_2 @ X0)
% 54.41/54.61          | ~ (v5_orders_2 @ X0)
% 54.41/54.61          | ~ (l1_orders_2 @ X0)
% 54.41/54.61          | ~ (r2_orders_2 @ X0 @ 
% 54.41/54.61               (sk_B @ (k1_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 54.41/54.61               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 54.41/54.61                (sk_B @ (a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0))))))),
% 54.41/54.61      inference('simplify', [status(thm)], ['52'])).
% 54.41/54.61  thf('54', plain,
% 54.41/54.61      (![X0 : $i]:
% 54.41/54.61         ((v2_struct_0 @ X0)
% 54.41/54.61          | ~ (v3_orders_2 @ X0)
% 54.41/54.61          | ~ (v4_orders_2 @ X0)
% 54.41/54.61          | ~ (v5_orders_2 @ X0)
% 54.41/54.61          | ~ (l1_orders_2 @ X0)
% 54.41/54.61          | ((k1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.61          | ((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.61          | ~ (l1_orders_2 @ X0)
% 54.41/54.61          | ~ (v5_orders_2 @ X0)
% 54.41/54.61          | ~ (v4_orders_2 @ X0)
% 54.41/54.61          | ~ (v3_orders_2 @ X0)
% 54.41/54.61          | (v2_struct_0 @ X0)
% 54.41/54.61          | ((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0)))),
% 54.41/54.61      inference('sup-', [status(thm)], ['42', '53'])).
% 54.41/54.61  thf('55', plain,
% 54.41/54.61      (![X0 : $i]:
% 54.41/54.61         (((a_2_0_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.61          | ((k1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.61          | ~ (l1_orders_2 @ X0)
% 54.41/54.61          | ~ (v5_orders_2 @ X0)
% 54.41/54.61          | ~ (v4_orders_2 @ X0)
% 54.41/54.61          | ~ (v3_orders_2 @ X0)
% 54.41/54.61          | (v2_struct_0 @ X0))),
% 54.41/54.61      inference('simplify', [status(thm)], ['54'])).
% 54.41/54.61  thf('56', plain,
% 54.41/54.61      (![X0 : $i]:
% 54.41/54.61         (((k1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.61          | ~ (l1_orders_2 @ X0)
% 54.41/54.61          | ~ (v5_orders_2 @ X0)
% 54.41/54.61          | ~ (v4_orders_2 @ X0)
% 54.41/54.61          | ~ (v3_orders_2 @ X0)
% 54.41/54.61          | (v2_struct_0 @ X0)
% 54.41/54.61          | (v2_struct_0 @ X0)
% 54.41/54.61          | ~ (v3_orders_2 @ X0)
% 54.41/54.61          | ~ (v4_orders_2 @ X0)
% 54.41/54.61          | ~ (v5_orders_2 @ X0)
% 54.41/54.61          | ~ (l1_orders_2 @ X0)
% 54.41/54.61          | ((k1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0)))),
% 54.41/54.61      inference('sup+', [status(thm)], ['9', '55'])).
% 54.41/54.61  thf('57', plain,
% 54.41/54.61      (![X0 : $i]:
% 54.41/54.61         ((v2_struct_0 @ X0)
% 54.41/54.61          | ~ (v3_orders_2 @ X0)
% 54.41/54.61          | ~ (v4_orders_2 @ X0)
% 54.41/54.61          | ~ (v5_orders_2 @ X0)
% 54.41/54.61          | ~ (l1_orders_2 @ X0)
% 54.41/54.61          | ((k1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0)))),
% 54.41/54.61      inference('simplify', [status(thm)], ['56'])).
% 54.41/54.61  thf('58', plain,
% 54.41/54.61      (![X0 : $i]:
% 54.41/54.61         (((k1_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 54.41/54.61          | ~ (l1_struct_0 @ X0)
% 54.41/54.61          | ~ (l1_orders_2 @ X0)
% 54.41/54.61          | ~ (v5_orders_2 @ X0)
% 54.41/54.61          | ~ (v4_orders_2 @ X0)
% 54.41/54.61          | ~ (v3_orders_2 @ X0)
% 54.41/54.61          | (v2_struct_0 @ X0))),
% 54.41/54.61      inference('sup+', [status(thm)], ['1', '57'])).
% 54.41/54.61  thf('59', plain,
% 54.41/54.61      (((k1_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 54.41/54.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.41/54.61  thf('60', plain,
% 54.41/54.61      ((((k1_xboole_0) != (k1_xboole_0))
% 54.41/54.61        | (v2_struct_0 @ sk_A)
% 54.41/54.61        | ~ (v3_orders_2 @ sk_A)
% 54.41/54.61        | ~ (v4_orders_2 @ sk_A)
% 54.41/54.61        | ~ (v5_orders_2 @ sk_A)
% 54.41/54.61        | ~ (l1_orders_2 @ sk_A)
% 54.41/54.61        | ~ (l1_struct_0 @ sk_A))),
% 54.41/54.61      inference('sup-', [status(thm)], ['58', '59'])).
% 54.41/54.61  thf('61', plain, ((v3_orders_2 @ sk_A)),
% 54.41/54.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.41/54.61  thf('62', plain, ((v4_orders_2 @ sk_A)),
% 54.41/54.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.41/54.61  thf('63', plain, ((v5_orders_2 @ sk_A)),
% 54.41/54.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.41/54.61  thf('64', plain, ((l1_orders_2 @ sk_A)),
% 54.41/54.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.41/54.61  thf('65', plain, ((l1_orders_2 @ sk_A)),
% 54.41/54.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 54.41/54.61  thf(dt_l1_orders_2, axiom,
% 54.41/54.61    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 54.41/54.61  thf('66', plain,
% 54.41/54.61      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_orders_2 @ X16))),
% 54.41/54.61      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 54.41/54.61  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 54.41/54.61      inference('sup-', [status(thm)], ['65', '66'])).
% 54.41/54.61  thf('68', plain, ((((k1_xboole_0) != (k1_xboole_0)) | (v2_struct_0 @ sk_A))),
% 54.41/54.61      inference('demod', [status(thm)], ['60', '61', '62', '63', '64', '67'])).
% 54.41/54.61  thf('69', plain, ((v2_struct_0 @ sk_A)),
% 54.41/54.61      inference('simplify', [status(thm)], ['68'])).
% 54.41/54.61  thf('70', plain, ($false), inference('demod', [status(thm)], ['0', '69'])).
% 54.41/54.61  
% 54.41/54.61  % SZS output end Refutation
% 54.41/54.61  
% 54.41/54.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
