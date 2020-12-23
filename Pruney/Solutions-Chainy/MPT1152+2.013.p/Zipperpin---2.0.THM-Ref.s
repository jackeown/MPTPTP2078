%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YqaYTxLyV1

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:43 EST 2020

% Result     : Theorem 38.02s
% Output     : Refutation 38.02s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 234 expanded)
%              Number of leaves         :   33 (  86 expanded)
%              Depth                    :   25
%              Number of atoms          : 1604 (3069 expanded)
%              Number of equality atoms :   62 ( 146 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

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
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X2 ) @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('3',plain,(
    ! [X1: $i] :
      ( ( k2_subset_1 @ X1 )
      = X1 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('4',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('5',plain,(
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

thf('6',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('9',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('10',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( X20
        = ( sk_D @ X18 @ X17 @ X20 ) )
      | ~ ( r2_hidden @ X20 @ ( a_2_1_orders_2 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( X1
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('14',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('15',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X18 @ X17 @ X20 ) @ ( u1_struct_0 @ X17 ) )
      | ~ ( r2_hidden @ X20 @ ( a_2_1_orders_2 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
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
      | ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('26',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('27',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( u1_struct_0 @ X17 ) )
      | ( r2_orders_2 @ X17 @ ( sk_D @ X18 @ X17 @ X20 ) @ X19 )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( a_2_1_orders_2 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('28',plain,(
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
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) @ X1 )
      | ~ ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
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
      | ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['23','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

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

thf('37',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r2_orders_2 @ X10 @ X9 @ X11 )
      | ( X9 != X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('38',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ~ ( r2_orders_2 @ X10 @ X11 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) )
      | ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) )
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
      | ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
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
      | ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','48'])).

thf('50',plain,(
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('57',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['51','52','53','54','55','58'])).

thf('60',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('64',plain,(
    ! [X8: $i] :
      ( ( ( k2_struct_0 @ X8 )
        = ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('65',plain,(
    ! [X2: $i] :
      ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(dt_k2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('66',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_orders_2 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_orders_2])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('68',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','70'])).

thf('72',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','71'])).

thf('73',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('74',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    l1_orders_2 @ sk_A ),
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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.YqaYTxLyV1
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:43:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 38.02/38.27  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 38.02/38.27  % Solved by: fo/fo7.sh
% 38.02/38.27  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 38.02/38.27  % done 27574 iterations in 37.809s
% 38.02/38.27  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 38.02/38.27  % SZS output start Refutation
% 38.02/38.27  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 38.02/38.27  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 38.02/38.27  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 38.02/38.27  thf(sk_B_type, type, sk_B: $i > $i).
% 38.02/38.27  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 38.02/38.27  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 38.02/38.27  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 38.02/38.27  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 38.02/38.27  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 38.02/38.27  thf(sk_A_type, type, sk_A: $i).
% 38.02/38.27  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 38.02/38.27  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 38.02/38.27  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 38.02/38.27  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 38.02/38.27  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 38.02/38.27  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 38.02/38.27  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 38.02/38.27  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 38.02/38.27  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 38.02/38.27  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 38.02/38.27  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 38.02/38.27  thf(t46_orders_2, conjecture,
% 38.02/38.27    (![A:$i]:
% 38.02/38.27     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 38.02/38.27         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 38.02/38.27       ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 38.02/38.27  thf(zf_stmt_0, negated_conjecture,
% 38.02/38.27    (~( ![A:$i]:
% 38.02/38.27        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 38.02/38.27            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 38.02/38.27          ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 38.02/38.27    inference('cnf.neg', [status(esa)], [t46_orders_2])).
% 38.02/38.27  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 38.02/38.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.02/38.27  thf(d3_struct_0, axiom,
% 38.02/38.27    (![A:$i]:
% 38.02/38.27     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 38.02/38.27  thf('1', plain,
% 38.02/38.27      (![X8 : $i]:
% 38.02/38.27         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 38.02/38.27      inference('cnf', [status(esa)], [d3_struct_0])).
% 38.02/38.27  thf(dt_k2_subset_1, axiom,
% 38.02/38.27    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 38.02/38.27  thf('2', plain,
% 38.02/38.27      (![X2 : $i]: (m1_subset_1 @ (k2_subset_1 @ X2) @ (k1_zfmisc_1 @ X2))),
% 38.02/38.27      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 38.02/38.27  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 38.02/38.27  thf('3', plain, (![X1 : $i]: ((k2_subset_1 @ X1) = (X1))),
% 38.02/38.27      inference('cnf', [status(esa)], [d4_subset_1])).
% 38.02/38.27  thf('4', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 38.02/38.27      inference('demod', [status(thm)], ['2', '3'])).
% 38.02/38.27  thf(d13_orders_2, axiom,
% 38.02/38.27    (![A:$i]:
% 38.02/38.27     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 38.02/38.27         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 38.02/38.27       ( ![B:$i]:
% 38.02/38.27         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 38.02/38.27           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 38.02/38.27  thf('5', plain,
% 38.02/38.27      (![X12 : $i, X13 : $i]:
% 38.02/38.27         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 38.02/38.27          | ((k2_orders_2 @ X13 @ X12) = (a_2_1_orders_2 @ X13 @ X12))
% 38.02/38.27          | ~ (l1_orders_2 @ X13)
% 38.02/38.27          | ~ (v5_orders_2 @ X13)
% 38.02/38.27          | ~ (v4_orders_2 @ X13)
% 38.02/38.27          | ~ (v3_orders_2 @ X13)
% 38.02/38.27          | (v2_struct_0 @ X13))),
% 38.02/38.27      inference('cnf', [status(esa)], [d13_orders_2])).
% 38.02/38.27  thf('6', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         ((v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 38.02/38.27              = (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 38.02/38.27      inference('sup-', [status(thm)], ['4', '5'])).
% 38.02/38.27  thf('7', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         ((v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 38.02/38.27              = (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 38.02/38.27      inference('sup-', [status(thm)], ['4', '5'])).
% 38.02/38.27  thf(t7_xboole_0, axiom,
% 38.02/38.27    (![A:$i]:
% 38.02/38.27     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 38.02/38.27          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 38.02/38.27  thf('8', plain,
% 38.02/38.27      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 38.02/38.27      inference('cnf', [status(esa)], [t7_xboole_0])).
% 38.02/38.27  thf('9', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 38.02/38.27      inference('demod', [status(thm)], ['2', '3'])).
% 38.02/38.27  thf(fraenkel_a_2_1_orders_2, axiom,
% 38.02/38.27    (![A:$i,B:$i,C:$i]:
% 38.02/38.27     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 38.02/38.27         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 38.02/38.27         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 38.02/38.27       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 38.02/38.27         ( ?[D:$i]:
% 38.02/38.27           ( ( ![E:$i]:
% 38.02/38.27               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 38.02/38.27                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 38.02/38.27             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 38.02/38.27  thf('10', plain,
% 38.02/38.27      (![X17 : $i, X18 : $i, X20 : $i]:
% 38.02/38.27         (~ (l1_orders_2 @ X17)
% 38.02/38.27          | ~ (v5_orders_2 @ X17)
% 38.02/38.27          | ~ (v4_orders_2 @ X17)
% 38.02/38.27          | ~ (v3_orders_2 @ X17)
% 38.02/38.27          | (v2_struct_0 @ X17)
% 38.02/38.27          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 38.02/38.27          | ((X20) = (sk_D @ X18 @ X17 @ X20))
% 38.02/38.27          | ~ (r2_hidden @ X20 @ (a_2_1_orders_2 @ X17 @ X18)))),
% 38.02/38.27      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 38.02/38.27  thf('11', plain,
% 38.02/38.27      (![X0 : $i, X1 : $i]:
% 38.02/38.27         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 38.02/38.27          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0))),
% 38.02/38.27      inference('sup-', [status(thm)], ['9', '10'])).
% 38.02/38.27  thf('12', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         (((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ((sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 38.02/38.27              = (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 38.02/38.27                 (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))))),
% 38.02/38.27      inference('sup-', [status(thm)], ['8', '11'])).
% 38.02/38.27  thf('13', plain,
% 38.02/38.27      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 38.02/38.27      inference('cnf', [status(esa)], [t7_xboole_0])).
% 38.02/38.27  thf('14', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 38.02/38.27      inference('demod', [status(thm)], ['2', '3'])).
% 38.02/38.27  thf('15', plain,
% 38.02/38.27      (![X17 : $i, X18 : $i, X20 : $i]:
% 38.02/38.27         (~ (l1_orders_2 @ X17)
% 38.02/38.27          | ~ (v5_orders_2 @ X17)
% 38.02/38.27          | ~ (v4_orders_2 @ X17)
% 38.02/38.27          | ~ (v3_orders_2 @ X17)
% 38.02/38.27          | (v2_struct_0 @ X17)
% 38.02/38.27          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 38.02/38.27          | (m1_subset_1 @ (sk_D @ X18 @ X17 @ X20) @ (u1_struct_0 @ X17))
% 38.02/38.27          | ~ (r2_hidden @ X20 @ (a_2_1_orders_2 @ X17 @ X18)))),
% 38.02/38.27      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 38.02/38.27  thf('16', plain,
% 38.02/38.27      (![X0 : $i, X1 : $i]:
% 38.02/38.27         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 38.02/38.27          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 38.02/38.27             (u1_struct_0 @ X0))
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0))),
% 38.02/38.27      inference('sup-', [status(thm)], ['14', '15'])).
% 38.02/38.27  thf('17', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         (((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | (m1_subset_1 @ 
% 38.02/38.27             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 38.02/38.27              (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))) @ 
% 38.02/38.27             (u1_struct_0 @ X0)))),
% 38.02/38.27      inference('sup-', [status(thm)], ['13', '16'])).
% 38.02/38.27  thf('18', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         ((m1_subset_1 @ (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 38.02/38.27           (u1_struct_0 @ X0))
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0)))),
% 38.02/38.27      inference('sup+', [status(thm)], ['12', '17'])).
% 38.02/38.27  thf('19', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         (((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | (m1_subset_1 @ 
% 38.02/38.27             (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 38.02/38.27             (u1_struct_0 @ X0)))),
% 38.02/38.27      inference('simplify', [status(thm)], ['18'])).
% 38.02/38.27  thf('20', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 38.02/38.27           (u1_struct_0 @ X0))
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0)))),
% 38.02/38.27      inference('sup+', [status(thm)], ['7', '19'])).
% 38.02/38.27  thf('21', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         (((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 38.02/38.27             (u1_struct_0 @ X0)))),
% 38.02/38.27      inference('simplify', [status(thm)], ['20'])).
% 38.02/38.27  thf(t2_subset, axiom,
% 38.02/38.27    (![A:$i,B:$i]:
% 38.02/38.27     ( ( m1_subset_1 @ A @ B ) =>
% 38.02/38.27       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 38.02/38.27  thf('22', plain,
% 38.02/38.27      (![X3 : $i, X4 : $i]:
% 38.02/38.27         ((r2_hidden @ X3 @ X4)
% 38.02/38.27          | (v1_xboole_0 @ X4)
% 38.02/38.27          | ~ (m1_subset_1 @ X3 @ X4))),
% 38.02/38.27      inference('cnf', [status(esa)], [t2_subset])).
% 38.02/38.27  thf('23', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         (~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 38.02/38.27          | (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 38.02/38.27             (u1_struct_0 @ X0)))),
% 38.02/38.27      inference('sup-', [status(thm)], ['21', '22'])).
% 38.02/38.27  thf('24', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         (((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 38.02/38.27             (u1_struct_0 @ X0)))),
% 38.02/38.27      inference('simplify', [status(thm)], ['20'])).
% 38.02/38.27  thf('25', plain,
% 38.02/38.27      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 38.02/38.27      inference('cnf', [status(esa)], [t7_xboole_0])).
% 38.02/38.27  thf('26', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 38.02/38.27      inference('demod', [status(thm)], ['2', '3'])).
% 38.02/38.27  thf('27', plain,
% 38.02/38.27      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 38.02/38.27         (~ (l1_orders_2 @ X17)
% 38.02/38.27          | ~ (v5_orders_2 @ X17)
% 38.02/38.27          | ~ (v4_orders_2 @ X17)
% 38.02/38.27          | ~ (v3_orders_2 @ X17)
% 38.02/38.27          | (v2_struct_0 @ X17)
% 38.02/38.27          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 38.02/38.27          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 38.02/38.27          | (r2_orders_2 @ X17 @ (sk_D @ X18 @ X17 @ X20) @ X19)
% 38.02/38.27          | ~ (r2_hidden @ X19 @ X18)
% 38.02/38.27          | ~ (r2_hidden @ X20 @ (a_2_1_orders_2 @ X17 @ X18)))),
% 38.02/38.27      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 38.02/38.27  thf('28', plain,
% 38.02/38.27      (![X0 : $i, X1 : $i, X2 : $i]:
% 38.02/38.27         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 38.02/38.27          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 38.02/38.27          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 38.02/38.27          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0))),
% 38.02/38.27      inference('sup-', [status(thm)], ['26', '27'])).
% 38.02/38.27  thf('29', plain,
% 38.02/38.27      (![X0 : $i, X1 : $i]:
% 38.02/38.27         (((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 38.02/38.27          | (r2_orders_2 @ X0 @ 
% 38.02/38.27             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 38.02/38.27              (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))) @ 
% 38.02/38.27             X1)
% 38.02/38.27          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0)))),
% 38.02/38.27      inference('sup-', [status(thm)], ['25', '28'])).
% 38.02/38.27  thf('30', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         (~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 38.02/38.27               (u1_struct_0 @ X0))
% 38.02/38.27          | (r2_orders_2 @ X0 @ 
% 38.02/38.27             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 38.02/38.27              (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))) @ 
% 38.02/38.27             (sk_B @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))))
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0)))),
% 38.02/38.27      inference('sup-', [status(thm)], ['24', '29'])).
% 38.02/38.27  thf('31', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         ((r2_orders_2 @ X0 @ 
% 38.02/38.27           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 38.02/38.27            (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))) @ 
% 38.02/38.27           (sk_B @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))))
% 38.02/38.27          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))) @ 
% 38.02/38.27               (u1_struct_0 @ X0))
% 38.02/38.27          | ((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0))),
% 38.02/38.27      inference('simplify', [status(thm)], ['30'])).
% 38.02/38.27  thf('32', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 38.02/38.27          | ((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | (r2_orders_2 @ X0 @ 
% 38.02/38.27             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 38.02/38.27              (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))) @ 
% 38.02/38.27             (sk_B @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0)))))),
% 38.02/38.27      inference('sup-', [status(thm)], ['23', '31'])).
% 38.02/38.27  thf('33', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         ((r2_orders_2 @ X0 @ 
% 38.02/38.27           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 38.02/38.27            (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))) @ 
% 38.02/38.27           (sk_B @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))))
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 38.02/38.27      inference('simplify', [status(thm)], ['32'])).
% 38.02/38.27  thf('34', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         ((v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 38.02/38.27              = (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 38.02/38.27      inference('sup-', [status(thm)], ['4', '5'])).
% 38.02/38.27  thf('35', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         (((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ((sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 38.02/38.27              = (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 38.02/38.27                 (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))))),
% 38.02/38.27      inference('sup-', [status(thm)], ['8', '11'])).
% 38.02/38.27  thf('36', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         (((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | (m1_subset_1 @ 
% 38.02/38.27             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 38.02/38.27              (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))) @ 
% 38.02/38.27             (u1_struct_0 @ X0)))),
% 38.02/38.27      inference('sup-', [status(thm)], ['13', '16'])).
% 38.02/38.27  thf(d10_orders_2, axiom,
% 38.02/38.27    (![A:$i]:
% 38.02/38.27     ( ( l1_orders_2 @ A ) =>
% 38.02/38.27       ( ![B:$i]:
% 38.02/38.27         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 38.02/38.27           ( ![C:$i]:
% 38.02/38.27             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 38.02/38.27               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 38.02/38.27                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 38.02/38.27  thf('37', plain,
% 38.02/38.27      (![X9 : $i, X10 : $i, X11 : $i]:
% 38.02/38.27         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 38.02/38.27          | ~ (r2_orders_2 @ X10 @ X9 @ X11)
% 38.02/38.27          | ((X9) != (X11))
% 38.02/38.27          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 38.02/38.27          | ~ (l1_orders_2 @ X10))),
% 38.02/38.27      inference('cnf', [status(esa)], [d10_orders_2])).
% 38.02/38.27  thf('38', plain,
% 38.02/38.27      (![X10 : $i, X11 : $i]:
% 38.02/38.27         (~ (l1_orders_2 @ X10)
% 38.02/38.27          | ~ (r2_orders_2 @ X10 @ X11 @ X11)
% 38.02/38.27          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10)))),
% 38.02/38.27      inference('simplify', [status(thm)], ['37'])).
% 38.02/38.27  thf('39', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         ((v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | ~ (r2_orders_2 @ X0 @ 
% 38.02/38.27               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 38.02/38.27                (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))) @ 
% 38.02/38.27               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 38.02/38.27                (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))))
% 38.02/38.27          | ~ (l1_orders_2 @ X0))),
% 38.02/38.27      inference('sup-', [status(thm)], ['36', '38'])).
% 38.02/38.27  thf('40', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         (~ (r2_orders_2 @ X0 @ 
% 38.02/38.27             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 38.02/38.27              (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))) @ 
% 38.02/38.27             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 38.02/38.27              (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))))
% 38.02/38.27          | ((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0))),
% 38.02/38.27      inference('simplify', [status(thm)], ['39'])).
% 38.02/38.27  thf('41', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         (~ (r2_orders_2 @ X0 @ 
% 38.02/38.27             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 38.02/38.27              (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))) @ 
% 38.02/38.27             (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0)))),
% 38.02/38.27      inference('sup-', [status(thm)], ['35', '40'])).
% 38.02/38.27  thf('42', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         (((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (r2_orders_2 @ X0 @ 
% 38.02/38.27               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 38.02/38.27                (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))) @ 
% 38.02/38.27               (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))))),
% 38.02/38.27      inference('simplify', [status(thm)], ['41'])).
% 38.02/38.27  thf('43', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         (~ (r2_orders_2 @ X0 @ 
% 38.02/38.27             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 38.02/38.27              (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))) @ 
% 38.02/38.27             (sk_B @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))))
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0)))),
% 38.02/38.27      inference('sup-', [status(thm)], ['34', '42'])).
% 38.02/38.27  thf('44', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         (((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (r2_orders_2 @ X0 @ 
% 38.02/38.27               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 38.02/38.27                (sk_B @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))) @ 
% 38.02/38.27               (sk_B @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0)))))),
% 38.02/38.27      inference('simplify', [status(thm)], ['43'])).
% 38.02/38.27  thf('45', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 38.02/38.27          | ((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0)))),
% 38.02/38.27      inference('sup-', [status(thm)], ['33', '44'])).
% 38.02/38.27  thf('46', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         (~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ((a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 38.02/38.27      inference('simplify', [status(thm)], ['45'])).
% 38.02/38.27  thf('47', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         (((k2_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | (v1_xboole_0 @ (u1_struct_0 @ X0))
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0))),
% 38.02/38.27      inference('sup+', [status(thm)], ['6', '46'])).
% 38.02/38.27  thf('48', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         ((v1_xboole_0 @ (u1_struct_0 @ X0))
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ((k2_orders_2 @ X0 @ (u1_struct_0 @ X0)) = (k1_xboole_0)))),
% 38.02/38.27      inference('simplify', [status(thm)], ['47'])).
% 38.02/38.27  thf('49', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | ~ (l1_struct_0 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | (v1_xboole_0 @ (u1_struct_0 @ X0)))),
% 38.02/38.27      inference('sup+', [status(thm)], ['1', '48'])).
% 38.02/38.27  thf('50', plain,
% 38.02/38.27      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 38.02/38.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.02/38.27  thf('51', plain,
% 38.02/38.27      ((((k1_xboole_0) != (k1_xboole_0))
% 38.02/38.27        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 38.02/38.27        | (v2_struct_0 @ sk_A)
% 38.02/38.27        | ~ (v3_orders_2 @ sk_A)
% 38.02/38.27        | ~ (v4_orders_2 @ sk_A)
% 38.02/38.27        | ~ (v5_orders_2 @ sk_A)
% 38.02/38.27        | ~ (l1_orders_2 @ sk_A)
% 38.02/38.27        | ~ (l1_struct_0 @ sk_A))),
% 38.02/38.27      inference('sup-', [status(thm)], ['49', '50'])).
% 38.02/38.27  thf('52', plain, ((v3_orders_2 @ sk_A)),
% 38.02/38.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.02/38.27  thf('53', plain, ((v4_orders_2 @ sk_A)),
% 38.02/38.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.02/38.27  thf('54', plain, ((v5_orders_2 @ sk_A)),
% 38.02/38.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.02/38.27  thf('55', plain, ((l1_orders_2 @ sk_A)),
% 38.02/38.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.02/38.27  thf('56', plain, ((l1_orders_2 @ sk_A)),
% 38.02/38.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.02/38.27  thf(dt_l1_orders_2, axiom,
% 38.02/38.27    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 38.02/38.27  thf('57', plain,
% 38.02/38.27      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_orders_2 @ X16))),
% 38.02/38.27      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 38.02/38.27  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 38.02/38.27      inference('sup-', [status(thm)], ['56', '57'])).
% 38.02/38.27  thf('59', plain,
% 38.02/38.27      ((((k1_xboole_0) != (k1_xboole_0))
% 38.02/38.27        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 38.02/38.27        | (v2_struct_0 @ sk_A))),
% 38.02/38.27      inference('demod', [status(thm)], ['51', '52', '53', '54', '55', '58'])).
% 38.02/38.27  thf('60', plain,
% 38.02/38.27      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 38.02/38.27      inference('simplify', [status(thm)], ['59'])).
% 38.02/38.27  thf('61', plain, (~ (v2_struct_0 @ sk_A)),
% 38.02/38.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.02/38.27  thf('62', plain, ((v1_xboole_0 @ (u1_struct_0 @ sk_A))),
% 38.02/38.27      inference('clc', [status(thm)], ['60', '61'])).
% 38.02/38.27  thf('63', plain,
% 38.02/38.27      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 38.02/38.27      inference('cnf', [status(esa)], [t7_xboole_0])).
% 38.02/38.27  thf('64', plain,
% 38.02/38.27      (![X8 : $i]:
% 38.02/38.27         (((k2_struct_0 @ X8) = (u1_struct_0 @ X8)) | ~ (l1_struct_0 @ X8))),
% 38.02/38.27      inference('cnf', [status(esa)], [d3_struct_0])).
% 38.02/38.27  thf('65', plain, (![X2 : $i]: (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X2))),
% 38.02/38.27      inference('demod', [status(thm)], ['2', '3'])).
% 38.02/38.27  thf(dt_k2_orders_2, axiom,
% 38.02/38.27    (![A:$i,B:$i]:
% 38.02/38.27     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 38.02/38.27         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 38.02/38.27         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 38.02/38.27       ( m1_subset_1 @
% 38.02/38.27         ( k2_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 38.02/38.27  thf('66', plain,
% 38.02/38.27      (![X14 : $i, X15 : $i]:
% 38.02/38.27         (~ (l1_orders_2 @ X14)
% 38.02/38.27          | ~ (v5_orders_2 @ X14)
% 38.02/38.27          | ~ (v4_orders_2 @ X14)
% 38.02/38.27          | ~ (v3_orders_2 @ X14)
% 38.02/38.27          | (v2_struct_0 @ X14)
% 38.02/38.27          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 38.02/38.27          | (m1_subset_1 @ (k2_orders_2 @ X14 @ X15) @ 
% 38.02/38.27             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 38.02/38.27      inference('cnf', [status(esa)], [dt_k2_orders_2])).
% 38.02/38.27  thf('67', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         ((m1_subset_1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0)) @ 
% 38.02/38.27           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0))),
% 38.02/38.27      inference('sup-', [status(thm)], ['65', '66'])).
% 38.02/38.27  thf(t5_subset, axiom,
% 38.02/38.27    (![A:$i,B:$i,C:$i]:
% 38.02/38.27     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 38.02/38.27          ( v1_xboole_0 @ C ) ) ))).
% 38.02/38.27  thf('68', plain,
% 38.02/38.27      (![X5 : $i, X6 : $i, X7 : $i]:
% 38.02/38.27         (~ (r2_hidden @ X5 @ X6)
% 38.02/38.27          | ~ (v1_xboole_0 @ X7)
% 38.02/38.27          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 38.02/38.27      inference('cnf', [status(esa)], [t5_subset])).
% 38.02/38.27  thf('69', plain,
% 38.02/38.27      (![X0 : $i, X1 : $i]:
% 38.02/38.27         (~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 38.02/38.27          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 38.02/38.27      inference('sup-', [status(thm)], ['67', '68'])).
% 38.02/38.27  thf('70', plain,
% 38.02/38.27      (![X0 : $i, X1 : $i]:
% 38.02/38.27         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 38.02/38.27          | ~ (l1_struct_0 @ X0)
% 38.02/38.27          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (l1_orders_2 @ X0))),
% 38.02/38.27      inference('sup-', [status(thm)], ['64', '69'])).
% 38.02/38.27  thf('71', plain,
% 38.02/38.27      (![X0 : $i]:
% 38.02/38.27         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 38.02/38.27          | ~ (l1_orders_2 @ X0)
% 38.02/38.27          | ~ (v5_orders_2 @ X0)
% 38.02/38.27          | ~ (v4_orders_2 @ X0)
% 38.02/38.27          | ~ (v3_orders_2 @ X0)
% 38.02/38.27          | (v2_struct_0 @ X0)
% 38.02/38.27          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 38.02/38.27          | ~ (l1_struct_0 @ X0))),
% 38.02/38.27      inference('sup-', [status(thm)], ['63', '70'])).
% 38.02/38.27  thf('72', plain,
% 38.02/38.27      ((~ (l1_struct_0 @ sk_A)
% 38.02/38.27        | (v2_struct_0 @ sk_A)
% 38.02/38.27        | ~ (v3_orders_2 @ sk_A)
% 38.02/38.27        | ~ (v4_orders_2 @ sk_A)
% 38.02/38.27        | ~ (v5_orders_2 @ sk_A)
% 38.02/38.27        | ~ (l1_orders_2 @ sk_A)
% 38.02/38.27        | ((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0)))),
% 38.02/38.27      inference('sup-', [status(thm)], ['62', '71'])).
% 38.02/38.27  thf('73', plain, ((l1_struct_0 @ sk_A)),
% 38.02/38.27      inference('sup-', [status(thm)], ['56', '57'])).
% 38.02/38.27  thf('74', plain, ((v3_orders_2 @ sk_A)),
% 38.02/38.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.02/38.27  thf('75', plain, ((v4_orders_2 @ sk_A)),
% 38.02/38.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.02/38.27  thf('76', plain, ((v5_orders_2 @ sk_A)),
% 38.02/38.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.02/38.27  thf('77', plain, ((l1_orders_2 @ sk_A)),
% 38.02/38.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.02/38.27  thf('78', plain,
% 38.02/38.27      (((v2_struct_0 @ sk_A)
% 38.02/38.27        | ((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0)))),
% 38.02/38.27      inference('demod', [status(thm)], ['72', '73', '74', '75', '76', '77'])).
% 38.02/38.27  thf('79', plain,
% 38.02/38.27      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 38.02/38.27      inference('cnf', [status(esa)], [zf_stmt_0])).
% 38.02/38.27  thf('80', plain, ((v2_struct_0 @ sk_A)),
% 38.02/38.27      inference('simplify_reflect-', [status(thm)], ['78', '79'])).
% 38.02/38.27  thf('81', plain, ($false), inference('demod', [status(thm)], ['0', '80'])).
% 38.02/38.27  
% 38.02/38.27  % SZS output end Refutation
% 38.02/38.27  
% 38.10/38.28  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
