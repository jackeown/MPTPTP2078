%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KBsjYyYpJH

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:46 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 195 expanded)
%              Number of leaves         :   30 (  71 expanded)
%              Depth                    :   21
%              Number of atoms          : 1571 (3235 expanded)
%              Number of equality atoms :   52 ( 114 expanded)
%              Maximal formula depth    :   24 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

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

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
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

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X10 ) ) )
      | ( ( k2_orders_2 @ X10 @ X9 )
        = ( a_2_1_orders_2 @ X10 @ X9 ) )
      | ~ ( l1_orders_2 @ X10 )
      | ~ ( v5_orders_2 @ X10 )
      | ~ ( v4_orders_2 @ X10 )
      | ~ ( v3_orders_2 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
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
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
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
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( X15
        = ( sk_D @ X13 @ X12 @ X15 ) )
      | ~ ( r2_hidden @ X15 @ ( a_2_1_orders_2 @ X12 @ X13 ) ) ) ),
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
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('15',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X13 @ X12 @ X15 ) @ ( u1_struct_0 @ X12 ) )
      | ~ ( r2_hidden @ X15 @ ( a_2_1_orders_2 @ X12 @ X13 ) ) ) ),
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
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
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
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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
    ! [X4: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X4 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X4 ) ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('30',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X12 ) )
      | ( r2_orders_2 @ X12 @ ( sk_D @ X13 @ X12 @ X15 ) @ X14 )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( r2_hidden @ X15 @ ( a_2_1_orders_2 @ X12 @ X13 ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( u1_struct_0 @ X7 ) )
      | ~ ( r2_orders_2 @ X7 @ X6 @ X8 )
      | ( X6 != X8 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) )
      | ~ ( l1_orders_2 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('42',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( l1_orders_2 @ X7 )
      | ~ ( r2_orders_2 @ X7 @ X8 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( u1_struct_0 @ X7 ) ) ) ),
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
    ! [X11: $i] :
      ( ( l1_struct_0 @ X11 )
      | ~ ( l1_orders_2 @ X11 ) ) ),
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
    ! [X3: $i] :
      ( ( ( k2_struct_0 @ X3 )
        = ( u1_struct_0 @ X3 ) )
      | ~ ( l1_struct_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('63',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 )
      | ( v2_struct_0 @ X5 ) ) ),
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
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KBsjYyYpJH
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:16:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.45/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.70  % Solved by: fo/fo7.sh
% 0.45/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.70  % done 235 iterations in 0.237s
% 0.45/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.70  % SZS output start Refutation
% 0.45/0.70  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.70  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.45/0.70  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 0.45/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.70  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.45/0.70  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.45/0.70  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.45/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.70  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.70  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.45/0.70  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.45/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.70  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.45/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.70  thf(sk_B_type, type, sk_B: $i > $i).
% 0.45/0.70  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.45/0.70  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.45/0.70  thf(t46_orders_2, conjecture,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.45/0.70         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.45/0.70       ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 0.45/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.70    (~( ![A:$i]:
% 0.45/0.70        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.45/0.70            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.45/0.70          ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 0.45/0.70    inference('cnf.neg', [status(esa)], [t46_orders_2])).
% 0.45/0.70  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(d3_struct_0, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.70  thf('1', plain,
% 0.45/0.70      (![X3 : $i]:
% 0.45/0.70         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.45/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.70  thf(t7_xboole_0, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.45/0.70          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.45/0.70  thf('2', plain,
% 0.45/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.45/0.70      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.70  thf(dt_k2_struct_0, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( l1_struct_0 @ A ) =>
% 0.45/0.70       ( m1_subset_1 @
% 0.45/0.70         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.70  thf('3', plain,
% 0.45/0.70      (![X4 : $i]:
% 0.45/0.70         ((m1_subset_1 @ (k2_struct_0 @ X4) @ 
% 0.45/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.45/0.70          | ~ (l1_struct_0 @ X4))),
% 0.45/0.70      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.45/0.70  thf(d13_orders_2, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.45/0.70         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.45/0.70       ( ![B:$i]:
% 0.45/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.70           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 0.45/0.70  thf('4', plain,
% 0.45/0.70      (![X9 : $i, X10 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (u1_struct_0 @ X10)))
% 0.45/0.70          | ((k2_orders_2 @ X10 @ X9) = (a_2_1_orders_2 @ X10 @ X9))
% 0.45/0.70          | ~ (l1_orders_2 @ X10)
% 0.45/0.70          | ~ (v5_orders_2 @ X10)
% 0.45/0.70          | ~ (v4_orders_2 @ X10)
% 0.45/0.70          | ~ (v3_orders_2 @ X10)
% 0.45/0.70          | (v2_struct_0 @ X10))),
% 0.45/0.70      inference('cnf', [status(esa)], [d13_orders_2])).
% 0.45/0.70  thf('5', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (l1_struct_0 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 0.45/0.70              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.70  thf('6', plain,
% 0.45/0.70      (![X4 : $i]:
% 0.45/0.70         ((m1_subset_1 @ (k2_struct_0 @ X4) @ 
% 0.45/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.45/0.70          | ~ (l1_struct_0 @ X4))),
% 0.45/0.70      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.45/0.70  thf(fraenkel_a_2_1_orders_2, axiom,
% 0.45/0.70    (![A:$i,B:$i,C:$i]:
% 0.45/0.70     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.45/0.70         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.45/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.45/0.70       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 0.45/0.70         ( ?[D:$i]:
% 0.45/0.70           ( ( ![E:$i]:
% 0.45/0.70               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.45/0.70                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 0.45/0.70             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.45/0.70  thf('7', plain,
% 0.45/0.70      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.45/0.70         (~ (l1_orders_2 @ X12)
% 0.45/0.70          | ~ (v5_orders_2 @ X12)
% 0.45/0.70          | ~ (v4_orders_2 @ X12)
% 0.45/0.70          | ~ (v3_orders_2 @ X12)
% 0.45/0.70          | (v2_struct_0 @ X12)
% 0.45/0.70          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.45/0.70          | ((X15) = (sk_D @ X13 @ X12 @ X15))
% 0.45/0.70          | ~ (r2_hidden @ X15 @ (a_2_1_orders_2 @ X12 @ X13)))),
% 0.45/0.70      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.45/0.70  thf('8', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (~ (l1_struct_0 @ X0)
% 0.45/0.70          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.45/0.70          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.45/0.70  thf('9', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 0.45/0.70          | ~ (l1_struct_0 @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['5', '8'])).
% 0.45/0.70  thf('10', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.45/0.70      inference('simplify', [status(thm)], ['9'])).
% 0.45/0.70  thf('11', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.45/0.70              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.45/0.70                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['2', '10'])).
% 0.45/0.70  thf('12', plain,
% 0.45/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.45/0.70      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.70  thf('13', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (l1_struct_0 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 0.45/0.70              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.70  thf('14', plain,
% 0.45/0.70      (![X4 : $i]:
% 0.45/0.70         ((m1_subset_1 @ (k2_struct_0 @ X4) @ 
% 0.45/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.45/0.70          | ~ (l1_struct_0 @ X4))),
% 0.45/0.70      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.45/0.70  thf('15', plain,
% 0.45/0.70      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.45/0.70         (~ (l1_orders_2 @ X12)
% 0.45/0.70          | ~ (v5_orders_2 @ X12)
% 0.45/0.70          | ~ (v4_orders_2 @ X12)
% 0.45/0.70          | ~ (v3_orders_2 @ X12)
% 0.45/0.70          | (v2_struct_0 @ X12)
% 0.45/0.70          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.45/0.70          | (m1_subset_1 @ (sk_D @ X13 @ X12 @ X15) @ (u1_struct_0 @ X12))
% 0.45/0.70          | ~ (r2_hidden @ X15 @ (a_2_1_orders_2 @ X12 @ X13)))),
% 0.45/0.70      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.45/0.70  thf('16', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (~ (l1_struct_0 @ X0)
% 0.45/0.70          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.45/0.70          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 0.45/0.70             (u1_struct_0 @ X0))
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.70  thf('17', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 0.45/0.70             (u1_struct_0 @ X0))
% 0.45/0.70          | ~ (l1_struct_0 @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['13', '16'])).
% 0.45/0.70  thf('18', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         ((m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 0.45/0.70           (u1_struct_0 @ X0))
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.45/0.70      inference('simplify', [status(thm)], ['17'])).
% 0.45/0.70  thf('19', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | (m1_subset_1 @ 
% 0.45/0.70             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.45/0.70              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.45/0.70             (u1_struct_0 @ X0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['12', '18'])).
% 0.45/0.70  thf('20', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.45/0.70           (u1_struct_0 @ X0))
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.45/0.70      inference('sup+', [status(thm)], ['11', '19'])).
% 0.45/0.70  thf('21', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.45/0.70             (u1_struct_0 @ X0)))),
% 0.45/0.70      inference('simplify', [status(thm)], ['20'])).
% 0.45/0.70  thf('22', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.45/0.70           (k2_struct_0 @ X0))
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.45/0.70      inference('sup+', [status(thm)], ['1', '21'])).
% 0.45/0.70  thf('23', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.45/0.70             (k2_struct_0 @ X0)))),
% 0.45/0.70      inference('simplify', [status(thm)], ['22'])).
% 0.45/0.70  thf(t2_subset, axiom,
% 0.45/0.70    (![A:$i,B:$i]:
% 0.45/0.70     ( ( m1_subset_1 @ A @ B ) =>
% 0.45/0.70       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.70  thf('24', plain,
% 0.45/0.70      (![X1 : $i, X2 : $i]:
% 0.45/0.70         ((r2_hidden @ X1 @ X2)
% 0.45/0.70          | (v1_xboole_0 @ X2)
% 0.45/0.70          | ~ (m1_subset_1 @ X1 @ X2))),
% 0.45/0.70      inference('cnf', [status(esa)], [t2_subset])).
% 0.45/0.70  thf('25', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (l1_struct_0 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.45/0.70          | (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.45/0.70             (k2_struct_0 @ X0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.45/0.70  thf('26', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.45/0.70             (u1_struct_0 @ X0)))),
% 0.45/0.70      inference('simplify', [status(thm)], ['20'])).
% 0.45/0.70  thf('27', plain,
% 0.45/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.45/0.70      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.45/0.70  thf('28', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (l1_struct_0 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 0.45/0.70              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.45/0.70  thf('29', plain,
% 0.45/0.70      (![X4 : $i]:
% 0.45/0.70         ((m1_subset_1 @ (k2_struct_0 @ X4) @ 
% 0.45/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X4)))
% 0.45/0.70          | ~ (l1_struct_0 @ X4))),
% 0.45/0.70      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.45/0.70  thf('30', plain,
% 0.45/0.70      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.70         (~ (l1_orders_2 @ X12)
% 0.45/0.70          | ~ (v5_orders_2 @ X12)
% 0.45/0.70          | ~ (v4_orders_2 @ X12)
% 0.45/0.70          | ~ (v3_orders_2 @ X12)
% 0.45/0.70          | (v2_struct_0 @ X12)
% 0.45/0.70          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 0.45/0.70          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X12))
% 0.45/0.70          | (r2_orders_2 @ X12 @ (sk_D @ X13 @ X12 @ X15) @ X14)
% 0.45/0.70          | ~ (r2_hidden @ X14 @ X13)
% 0.45/0.70          | ~ (r2_hidden @ X15 @ (a_2_1_orders_2 @ X12 @ X13)))),
% 0.45/0.70      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.45/0.70  thf('31', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         (~ (l1_struct_0 @ X0)
% 0.45/0.70          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.45/0.70          | ~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 0.45/0.70          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 0.45/0.70          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.70  thf('32', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.45/0.70          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 0.45/0.70          | ~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 0.45/0.70          | ~ (l1_struct_0 @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['28', '31'])).
% 0.45/0.70  thf('33', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.70         (~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 0.45/0.70          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 0.45/0.70          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.45/0.70      inference('simplify', [status(thm)], ['32'])).
% 0.45/0.70  thf('34', plain,
% 0.45/0.70      (![X0 : $i, X1 : $i]:
% 0.45/0.70         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.45/0.70          | (r2_orders_2 @ X0 @ 
% 0.45/0.70             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.45/0.70              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.45/0.70             X1)
% 0.45/0.70          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['27', '33'])).
% 0.45/0.70  thf('35', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (l1_struct_0 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.45/0.70               (k2_struct_0 @ X0))
% 0.45/0.70          | (r2_orders_2 @ X0 @ 
% 0.45/0.70             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.45/0.70              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.45/0.70             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['26', '34'])).
% 0.45/0.70  thf('36', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((r2_orders_2 @ X0 @ 
% 0.45/0.70           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.45/0.70            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.45/0.70           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 0.45/0.70          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.45/0.70               (k2_struct_0 @ X0))
% 0.45/0.70          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0))),
% 0.45/0.70      inference('simplify', [status(thm)], ['35'])).
% 0.45/0.70  thf('37', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.45/0.70          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | (r2_orders_2 @ X0 @ 
% 0.45/0.70             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.45/0.70              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.45/0.70             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['25', '36'])).
% 0.45/0.70  thf('38', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((r2_orders_2 @ X0 @ 
% 0.45/0.70           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.45/0.70            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.45/0.70           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.45/0.70      inference('simplify', [status(thm)], ['37'])).
% 0.45/0.70  thf('39', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.45/0.70              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.45/0.70                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 0.45/0.70      inference('sup-', [status(thm)], ['2', '10'])).
% 0.45/0.70  thf('40', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | (m1_subset_1 @ 
% 0.45/0.70             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.45/0.70              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.45/0.70             (u1_struct_0 @ X0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['12', '18'])).
% 0.45/0.70  thf(d10_orders_2, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( l1_orders_2 @ A ) =>
% 0.45/0.70       ( ![B:$i]:
% 0.45/0.70         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.70           ( ![C:$i]:
% 0.45/0.70             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.45/0.70               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.45/0.70                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 0.45/0.70  thf('41', plain,
% 0.45/0.70      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.45/0.70         (~ (m1_subset_1 @ X6 @ (u1_struct_0 @ X7))
% 0.45/0.70          | ~ (r2_orders_2 @ X7 @ X6 @ X8)
% 0.45/0.70          | ((X6) != (X8))
% 0.45/0.70          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7))
% 0.45/0.70          | ~ (l1_orders_2 @ X7))),
% 0.45/0.70      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.45/0.70  thf('42', plain,
% 0.45/0.70      (![X7 : $i, X8 : $i]:
% 0.45/0.70         (~ (l1_orders_2 @ X7)
% 0.45/0.70          | ~ (r2_orders_2 @ X7 @ X8 @ X8)
% 0.45/0.70          | ~ (m1_subset_1 @ X8 @ (u1_struct_0 @ X7)))),
% 0.45/0.70      inference('simplify', [status(thm)], ['41'])).
% 0.45/0.70  thf('43', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (l1_struct_0 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | ~ (r2_orders_2 @ X0 @ 
% 0.45/0.70               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.45/0.70                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.45/0.70               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.45/0.70                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 0.45/0.70          | ~ (l1_orders_2 @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['40', '42'])).
% 0.45/0.70  thf('44', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (r2_orders_2 @ X0 @ 
% 0.45/0.70             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.45/0.70              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.45/0.70             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.45/0.70              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 0.45/0.70          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0))),
% 0.45/0.70      inference('simplify', [status(thm)], ['43'])).
% 0.45/0.70  thf('45', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (r2_orders_2 @ X0 @ 
% 0.45/0.70             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.45/0.70              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.45/0.70             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['39', '44'])).
% 0.45/0.70  thf('46', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | ~ (r2_orders_2 @ X0 @ 
% 0.45/0.70               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.45/0.70                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.45/0.70               (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 0.45/0.70      inference('simplify', [status(thm)], ['45'])).
% 0.45/0.70  thf('47', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.45/0.70          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.45/0.70      inference('sup-', [status(thm)], ['38', '46'])).
% 0.45/0.70  thf('48', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (l1_struct_0 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (v3_orders_2 @ X0)
% 0.45/0.70          | ~ (v4_orders_2 @ X0)
% 0.45/0.70          | ~ (v5_orders_2 @ X0)
% 0.45/0.70          | ~ (l1_orders_2 @ X0)
% 0.45/0.70          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.45/0.70          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.45/0.70      inference('simplify', [status(thm)], ['47'])).
% 0.45/0.70  thf('49', plain,
% 0.45/0.70      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('50', plain,
% 0.45/0.70      ((((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.70        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.45/0.70        | ~ (l1_orders_2 @ sk_A)
% 0.45/0.70        | ~ (v5_orders_2 @ sk_A)
% 0.45/0.70        | ~ (v4_orders_2 @ sk_A)
% 0.45/0.70        | ~ (v3_orders_2 @ sk_A)
% 0.45/0.70        | (v2_struct_0 @ sk_A)
% 0.45/0.70        | ~ (l1_struct_0 @ sk_A))),
% 0.45/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.70  thf('51', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('52', plain, ((v5_orders_2 @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('53', plain, ((v4_orders_2 @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('54', plain, ((v3_orders_2 @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('55', plain, ((l1_orders_2 @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf(dt_l1_orders_2, axiom,
% 0.45/0.70    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.70  thf('56', plain,
% 0.45/0.70      (![X11 : $i]: ((l1_struct_0 @ X11) | ~ (l1_orders_2 @ X11))),
% 0.45/0.70      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.45/0.70  thf('57', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.70      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.70  thf('58', plain,
% 0.45/0.70      ((((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.70        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.45/0.70        | (v2_struct_0 @ sk_A))),
% 0.45/0.70      inference('demod', [status(thm)], ['50', '51', '52', '53', '54', '57'])).
% 0.45/0.70  thf('59', plain,
% 0.45/0.70      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.45/0.70      inference('simplify', [status(thm)], ['58'])).
% 0.45/0.70  thf('60', plain, (~ (v2_struct_0 @ sk_A)),
% 0.45/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.70  thf('61', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.45/0.70      inference('clc', [status(thm)], ['59', '60'])).
% 0.45/0.70  thf('62', plain,
% 0.45/0.70      (![X3 : $i]:
% 0.45/0.70         (((k2_struct_0 @ X3) = (u1_struct_0 @ X3)) | ~ (l1_struct_0 @ X3))),
% 0.45/0.70      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.70  thf(fc2_struct_0, axiom,
% 0.45/0.70    (![A:$i]:
% 0.45/0.70     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.45/0.70       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.45/0.70  thf('63', plain,
% 0.45/0.70      (![X5 : $i]:
% 0.45/0.70         (~ (v1_xboole_0 @ (u1_struct_0 @ X5))
% 0.45/0.70          | ~ (l1_struct_0 @ X5)
% 0.45/0.70          | (v2_struct_0 @ X5))),
% 0.45/0.70      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.45/0.70  thf('64', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | (v2_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0))),
% 0.45/0.70      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.70  thf('65', plain,
% 0.45/0.70      (![X0 : $i]:
% 0.45/0.70         ((v2_struct_0 @ X0)
% 0.45/0.70          | ~ (l1_struct_0 @ X0)
% 0.45/0.70          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.45/0.70      inference('simplify', [status(thm)], ['64'])).
% 0.45/0.70  thf('66', plain, ((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 0.45/0.70      inference('sup-', [status(thm)], ['61', '65'])).
% 0.45/0.70  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.70      inference('sup-', [status(thm)], ['55', '56'])).
% 0.45/0.70  thf('68', plain, ((v2_struct_0 @ sk_A)),
% 0.45/0.70      inference('demod', [status(thm)], ['66', '67'])).
% 0.45/0.70  thf('69', plain, ($false), inference('demod', [status(thm)], ['0', '68'])).
% 0.45/0.70  
% 0.45/0.70  % SZS output end Refutation
% 0.45/0.70  
% 0.45/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
