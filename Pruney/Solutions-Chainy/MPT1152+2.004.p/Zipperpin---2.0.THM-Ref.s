%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.debhPPqo6z

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:42 EST 2020

% Result     : Theorem 9.51s
% Output     : Refutation 9.51s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 184 expanded)
%              Number of leaves         :   31 (  67 expanded)
%              Depth                    :   20
%              Number of atoms          : 1949 (2981 expanded)
%              Number of equality atoms :   55 (  91 expanded)
%              Maximal formula depth    :   25 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

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
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
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

thf('3',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( v5_orders_2 @ X14 )
      | ~ ( v4_orders_2 @ X14 )
      | ~ ( v3_orders_2 @ X14 )
      | ( v2_struct_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) )
      | ( m1_subset_1 @ ( k2_orders_2 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_orders_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ~ ( r2_hidden @ C @ B ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X3 @ X4 ) @ X4 )
      | ( X3 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X5: $i] :
      ( ( ( k2_struct_0 @ X5 )
        = ( u1_struct_0 @ X5 ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X3 @ X4 ) @ X4 )
      | ( X3 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ ( sk_C @ X3 @ X4 ) @ X3 )
      | ( X3 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t10_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
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

thf('21',plain,(
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

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
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

thf('24',plain,(
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

thf('25',plain,(
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
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
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
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
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
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
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
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) @ X1 )
      | ~ ( r2_hidden @ X1 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['16','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( m1_subset_1 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('36',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('37',plain,(
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

thf('38',plain,(
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
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
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
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
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
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
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
      | ( ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) )
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) )
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('45',plain,(
    ! [X6: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X6 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X6 ) ) )
      | ~ ( l1_struct_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('46',plain,(
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

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
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
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
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
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['43','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['50'])).

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

thf('52',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X10 ) )
      | ~ ( r2_orders_2 @ X10 @ X9 @ X11 )
      | ( X9 != X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_orders_2 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('53',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( l1_orders_2 @ X10 )
      | ~ ( r2_orders_2 @ X10 @ X11 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) @ ( sk_C @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('63',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['61','64','65','66','67','68'])).

thf('70',plain,
    ( ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
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

thf('74',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_struct_0 @ X8 )
      | ( v2_struct_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['72','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('79',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    $false ),
    inference(demod,[status(thm)],['0','79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.debhPPqo6z
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:48:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 9.51/9.74  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 9.51/9.74  % Solved by: fo/fo7.sh
% 9.51/9.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 9.51/9.74  % done 3237 iterations in 9.229s
% 9.51/9.74  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 9.51/9.74  % SZS output start Refutation
% 9.51/9.74  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 9.51/9.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 9.51/9.74  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 9.51/9.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 9.51/9.74  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 9.51/9.74  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 9.51/9.74  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 9.51/9.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 9.51/9.74  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 9.51/9.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 9.51/9.74  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 9.51/9.74  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 9.51/9.74  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 9.51/9.74  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 9.51/9.74  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 9.51/9.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 9.51/9.74  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 9.51/9.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 9.51/9.74  thf(sk_A_type, type, sk_A: $i).
% 9.51/9.74  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 9.51/9.74  thf(t46_orders_2, conjecture,
% 9.51/9.74    (![A:$i]:
% 9.51/9.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 9.51/9.74         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 9.51/9.74       ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 9.51/9.74  thf(zf_stmt_0, negated_conjecture,
% 9.51/9.74    (~( ![A:$i]:
% 9.51/9.74        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 9.51/9.74            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 9.51/9.74          ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 9.51/9.74    inference('cnf.neg', [status(esa)], [t46_orders_2])).
% 9.51/9.74  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 9.51/9.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.51/9.74  thf(d3_struct_0, axiom,
% 9.51/9.74    (![A:$i]:
% 9.51/9.74     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 9.51/9.74  thf('1', plain,
% 9.51/9.74      (![X5 : $i]:
% 9.51/9.74         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 9.51/9.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 9.51/9.74  thf(dt_k2_struct_0, axiom,
% 9.51/9.74    (![A:$i]:
% 9.51/9.74     ( ( l1_struct_0 @ A ) =>
% 9.51/9.74       ( m1_subset_1 @
% 9.51/9.74         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 9.51/9.74  thf('2', plain,
% 9.51/9.74      (![X6 : $i]:
% 9.51/9.74         ((m1_subset_1 @ (k2_struct_0 @ X6) @ 
% 9.51/9.74           (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 9.51/9.74          | ~ (l1_struct_0 @ X6))),
% 9.51/9.74      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 9.51/9.74  thf(dt_k2_orders_2, axiom,
% 9.51/9.74    (![A:$i,B:$i]:
% 9.51/9.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 9.51/9.74         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 9.51/9.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 9.51/9.74       ( m1_subset_1 @
% 9.51/9.74         ( k2_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 9.51/9.74  thf('3', plain,
% 9.51/9.74      (![X14 : $i, X15 : $i]:
% 9.51/9.74         (~ (l1_orders_2 @ X14)
% 9.51/9.74          | ~ (v5_orders_2 @ X14)
% 9.51/9.74          | ~ (v4_orders_2 @ X14)
% 9.51/9.74          | ~ (v3_orders_2 @ X14)
% 9.51/9.74          | (v2_struct_0 @ X14)
% 9.51/9.74          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X14)))
% 9.51/9.74          | (m1_subset_1 @ (k2_orders_2 @ X14 @ X15) @ 
% 9.51/9.74             (k1_zfmisc_1 @ (u1_struct_0 @ X14))))),
% 9.51/9.74      inference('cnf', [status(esa)], [dt_k2_orders_2])).
% 9.51/9.74  thf('4', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         (~ (l1_struct_0 @ X0)
% 9.51/9.74          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0))),
% 9.51/9.74      inference('sup-', [status(thm)], ['2', '3'])).
% 9.51/9.74  thf(t10_subset_1, axiom,
% 9.51/9.74    (![A:$i,B:$i]:
% 9.51/9.74     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 9.51/9.74       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 9.51/9.74            ( ![C:$i]:
% 9.51/9.74              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 9.51/9.74  thf('5', plain,
% 9.51/9.74      (![X3 : $i, X4 : $i]:
% 9.51/9.74         ((m1_subset_1 @ (sk_C @ X3 @ X4) @ X4)
% 9.51/9.74          | ((X3) = (k1_xboole_0))
% 9.51/9.74          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 9.51/9.74      inference('cnf', [status(esa)], [t10_subset_1])).
% 9.51/9.74  thf('6', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         (~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.74          | (m1_subset_1 @ 
% 9.51/9.74             (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74              (u1_struct_0 @ X0)) @ 
% 9.51/9.74             (u1_struct_0 @ X0)))),
% 9.51/9.74      inference('sup-', [status(thm)], ['4', '5'])).
% 9.51/9.74  thf('7', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         ((m1_subset_1 @ 
% 9.51/9.74           (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74           (u1_struct_0 @ X0))
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0))),
% 9.51/9.74      inference('sup+', [status(thm)], ['1', '6'])).
% 9.51/9.74  thf('8', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         (~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | (m1_subset_1 @ 
% 9.51/9.74             (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74              (k2_struct_0 @ X0)) @ 
% 9.51/9.74             (u1_struct_0 @ X0)))),
% 9.51/9.74      inference('simplify', [status(thm)], ['7'])).
% 9.51/9.74  thf('9', plain,
% 9.51/9.74      (![X5 : $i]:
% 9.51/9.74         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 9.51/9.74      inference('cnf', [status(esa)], [d3_struct_0])).
% 9.51/9.74  thf('10', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         (~ (l1_struct_0 @ X0)
% 9.51/9.74          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0))),
% 9.51/9.74      inference('sup-', [status(thm)], ['2', '3'])).
% 9.51/9.74  thf('11', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         ((m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74           (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_struct_0 @ X0))),
% 9.51/9.74      inference('sup+', [status(thm)], ['9', '10'])).
% 9.51/9.74  thf('12', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         ((v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 9.51/9.74      inference('simplify', [status(thm)], ['11'])).
% 9.51/9.74  thf('13', plain,
% 9.51/9.74      (![X3 : $i, X4 : $i]:
% 9.51/9.74         ((m1_subset_1 @ (sk_C @ X3 @ X4) @ X4)
% 9.51/9.74          | ((X3) = (k1_xboole_0))
% 9.51/9.74          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 9.51/9.74      inference('cnf', [status(esa)], [t10_subset_1])).
% 9.51/9.74  thf('14', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         (~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.74          | (m1_subset_1 @ 
% 9.51/9.74             (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74              (k2_struct_0 @ X0)) @ 
% 9.51/9.74             (k2_struct_0 @ X0)))),
% 9.51/9.74      inference('sup-', [status(thm)], ['12', '13'])).
% 9.51/9.74  thf(d2_subset_1, axiom,
% 9.51/9.74    (![A:$i,B:$i]:
% 9.51/9.74     ( ( ( v1_xboole_0 @ A ) =>
% 9.51/9.74         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 9.51/9.74       ( ( ~( v1_xboole_0 @ A ) ) =>
% 9.51/9.74         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 9.51/9.74  thf('15', plain,
% 9.51/9.74      (![X0 : $i, X1 : $i]:
% 9.51/9.74         (~ (m1_subset_1 @ X0 @ X1)
% 9.51/9.74          | (r2_hidden @ X0 @ X1)
% 9.51/9.74          | (v1_xboole_0 @ X1))),
% 9.51/9.74      inference('cnf', [status(esa)], [d2_subset_1])).
% 9.51/9.74  thf('16', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 9.51/9.74          | (r2_hidden @ 
% 9.51/9.74             (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74              (k2_struct_0 @ X0)) @ 
% 9.51/9.74             (k2_struct_0 @ X0)))),
% 9.51/9.74      inference('sup-', [status(thm)], ['14', '15'])).
% 9.51/9.74  thf('17', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         ((v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 9.51/9.74      inference('simplify', [status(thm)], ['11'])).
% 9.51/9.74  thf('18', plain,
% 9.51/9.74      (![X3 : $i, X4 : $i]:
% 9.51/9.74         ((r2_hidden @ (sk_C @ X3 @ X4) @ X3)
% 9.51/9.74          | ((X3) = (k1_xboole_0))
% 9.51/9.74          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4)))),
% 9.51/9.74      inference('cnf', [status(esa)], [t10_subset_1])).
% 9.51/9.74  thf('19', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         (~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.74          | (r2_hidden @ 
% 9.51/9.74             (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74              (k2_struct_0 @ X0)) @ 
% 9.51/9.74             (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 9.51/9.74      inference('sup-', [status(thm)], ['17', '18'])).
% 9.51/9.74  thf('20', plain,
% 9.51/9.74      (![X6 : $i]:
% 9.51/9.74         ((m1_subset_1 @ (k2_struct_0 @ X6) @ 
% 9.51/9.74           (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 9.51/9.74          | ~ (l1_struct_0 @ X6))),
% 9.51/9.74      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 9.51/9.74  thf(d13_orders_2, axiom,
% 9.51/9.74    (![A:$i]:
% 9.51/9.74     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 9.51/9.74         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 9.51/9.74       ( ![B:$i]:
% 9.51/9.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 9.51/9.74           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 9.51/9.74  thf('21', plain,
% 9.51/9.74      (![X12 : $i, X13 : $i]:
% 9.51/9.74         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (u1_struct_0 @ X13)))
% 9.51/9.74          | ((k2_orders_2 @ X13 @ X12) = (a_2_1_orders_2 @ X13 @ X12))
% 9.51/9.74          | ~ (l1_orders_2 @ X13)
% 9.51/9.74          | ~ (v5_orders_2 @ X13)
% 9.51/9.74          | ~ (v4_orders_2 @ X13)
% 9.51/9.74          | ~ (v3_orders_2 @ X13)
% 9.51/9.74          | (v2_struct_0 @ X13))),
% 9.51/9.74      inference('cnf', [status(esa)], [d13_orders_2])).
% 9.51/9.74  thf('22', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         (~ (l1_struct_0 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 9.51/9.74              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 9.51/9.74      inference('sup-', [status(thm)], ['20', '21'])).
% 9.51/9.74  thf('23', plain,
% 9.51/9.74      (![X6 : $i]:
% 9.51/9.74         ((m1_subset_1 @ (k2_struct_0 @ X6) @ 
% 9.51/9.74           (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 9.51/9.74          | ~ (l1_struct_0 @ X6))),
% 9.51/9.74      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 9.51/9.74  thf(fraenkel_a_2_1_orders_2, axiom,
% 9.51/9.74    (![A:$i,B:$i,C:$i]:
% 9.51/9.74     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 9.51/9.74         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 9.51/9.74         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 9.51/9.74       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 9.51/9.74         ( ?[D:$i]:
% 9.51/9.74           ( ( ![E:$i]:
% 9.51/9.74               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 9.51/9.74                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 9.51/9.74             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 9.51/9.74  thf('24', plain,
% 9.51/9.74      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 9.51/9.74         (~ (l1_orders_2 @ X17)
% 9.51/9.74          | ~ (v5_orders_2 @ X17)
% 9.51/9.74          | ~ (v4_orders_2 @ X17)
% 9.51/9.74          | ~ (v3_orders_2 @ X17)
% 9.51/9.74          | (v2_struct_0 @ X17)
% 9.51/9.74          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 9.51/9.74          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 9.51/9.74          | (r2_orders_2 @ X17 @ (sk_D @ X18 @ X17 @ X20) @ X19)
% 9.51/9.74          | ~ (r2_hidden @ X19 @ X18)
% 9.51/9.74          | ~ (r2_hidden @ X20 @ (a_2_1_orders_2 @ X17 @ X18)))),
% 9.51/9.74      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 9.51/9.74  thf('25', plain,
% 9.51/9.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.51/9.74         (~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 9.51/9.74          | ~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 9.51/9.74          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 9.51/9.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0))),
% 9.51/9.74      inference('sup-', [status(thm)], ['23', '24'])).
% 9.51/9.74  thf('26', plain,
% 9.51/9.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.51/9.74         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 9.51/9.74          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 9.51/9.74          | ~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 9.51/9.74          | ~ (l1_struct_0 @ X0))),
% 9.51/9.74      inference('sup-', [status(thm)], ['22', '25'])).
% 9.51/9.74  thf('27', plain,
% 9.51/9.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 9.51/9.74         (~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 9.51/9.74          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 9.51/9.74          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 9.51/9.74      inference('simplify', [status(thm)], ['26'])).
% 9.51/9.74  thf('28', plain,
% 9.51/9.74      (![X0 : $i, X1 : $i]:
% 9.51/9.74         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 9.51/9.74          | (r2_orders_2 @ X0 @ 
% 9.51/9.74             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 9.51/9.74              (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74               (k2_struct_0 @ X0))) @ 
% 9.51/9.74             X1)
% 9.51/9.74          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0)))),
% 9.51/9.74      inference('sup-', [status(thm)], ['19', '27'])).
% 9.51/9.74  thf('29', plain,
% 9.51/9.74      (![X0 : $i, X1 : $i]:
% 9.51/9.74         (~ (r2_hidden @ X1 @ (k2_struct_0 @ X0))
% 9.51/9.74          | (r2_orders_2 @ X0 @ 
% 9.51/9.74             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 9.51/9.74              (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74               (k2_struct_0 @ X0))) @ 
% 9.51/9.74             X1)
% 9.51/9.74          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 9.51/9.74      inference('simplify', [status(thm)], ['28'])).
% 9.51/9.74  thf('30', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (m1_subset_1 @ 
% 9.51/9.74               (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74                (k2_struct_0 @ X0)) @ 
% 9.51/9.74               (u1_struct_0 @ X0))
% 9.51/9.74          | (r2_orders_2 @ X0 @ 
% 9.51/9.74             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 9.51/9.74              (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74               (k2_struct_0 @ X0))) @ 
% 9.51/9.74             (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74              (k2_struct_0 @ X0))))),
% 9.51/9.74      inference('sup-', [status(thm)], ['16', '29'])).
% 9.51/9.74  thf('31', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         ((r2_orders_2 @ X0 @ 
% 9.51/9.74           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 9.51/9.74            (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74             (k2_struct_0 @ X0))) @ 
% 9.51/9.74           (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ (k2_struct_0 @ X0)))
% 9.51/9.74          | ~ (m1_subset_1 @ 
% 9.51/9.74               (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74                (k2_struct_0 @ X0)) @ 
% 9.51/9.74               (u1_struct_0 @ X0))
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 9.51/9.74      inference('simplify', [status(thm)], ['30'])).
% 9.51/9.74  thf('32', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         (~ (l1_struct_0 @ X0)
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.74          | (r2_orders_2 @ X0 @ 
% 9.51/9.74             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 9.51/9.74              (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74               (k2_struct_0 @ X0))) @ 
% 9.51/9.74             (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74              (k2_struct_0 @ X0))))),
% 9.51/9.74      inference('sup-', [status(thm)], ['8', '31'])).
% 9.51/9.74  thf('33', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         ((r2_orders_2 @ X0 @ 
% 9.51/9.74           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 9.51/9.74            (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74             (k2_struct_0 @ X0))) @ 
% 9.51/9.74           (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ (k2_struct_0 @ X0)))
% 9.51/9.74          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.74          | ~ (l1_struct_0 @ X0))),
% 9.51/9.74      inference('simplify', [status(thm)], ['32'])).
% 9.51/9.74  thf('34', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         (~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.74          | (r2_hidden @ 
% 9.51/9.74             (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74              (k2_struct_0 @ X0)) @ 
% 9.51/9.74             (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 9.51/9.74      inference('sup-', [status(thm)], ['17', '18'])).
% 9.51/9.74  thf('35', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         (~ (l1_struct_0 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 9.51/9.74              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 9.51/9.74      inference('sup-', [status(thm)], ['20', '21'])).
% 9.51/9.74  thf('36', plain,
% 9.51/9.74      (![X6 : $i]:
% 9.51/9.74         ((m1_subset_1 @ (k2_struct_0 @ X6) @ 
% 9.51/9.74           (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 9.51/9.74          | ~ (l1_struct_0 @ X6))),
% 9.51/9.74      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 9.51/9.74  thf('37', plain,
% 9.51/9.74      (![X17 : $i, X18 : $i, X20 : $i]:
% 9.51/9.74         (~ (l1_orders_2 @ X17)
% 9.51/9.74          | ~ (v5_orders_2 @ X17)
% 9.51/9.74          | ~ (v4_orders_2 @ X17)
% 9.51/9.74          | ~ (v3_orders_2 @ X17)
% 9.51/9.74          | (v2_struct_0 @ X17)
% 9.51/9.74          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 9.51/9.74          | ((X20) = (sk_D @ X18 @ X17 @ X20))
% 9.51/9.74          | ~ (r2_hidden @ X20 @ (a_2_1_orders_2 @ X17 @ X18)))),
% 9.51/9.74      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 9.51/9.74  thf('38', plain,
% 9.51/9.74      (![X0 : $i, X1 : $i]:
% 9.51/9.74         (~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 9.51/9.74          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0))),
% 9.51/9.74      inference('sup-', [status(thm)], ['36', '37'])).
% 9.51/9.74  thf('39', plain,
% 9.51/9.74      (![X0 : $i, X1 : $i]:
% 9.51/9.74         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 9.51/9.74          | ~ (l1_struct_0 @ X0))),
% 9.51/9.74      inference('sup-', [status(thm)], ['35', '38'])).
% 9.51/9.74  thf('40', plain,
% 9.51/9.74      (![X0 : $i, X1 : $i]:
% 9.51/9.74         (((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 9.51/9.74      inference('simplify', [status(thm)], ['39'])).
% 9.51/9.74  thf('41', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | ((sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74              (k2_struct_0 @ X0))
% 9.51/9.74              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 9.51/9.74                 (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74                  (k2_struct_0 @ X0)))))),
% 9.51/9.74      inference('sup-', [status(thm)], ['34', '40'])).
% 9.51/9.74  thf('42', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         (((sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ (k2_struct_0 @ X0))
% 9.51/9.74            = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 9.51/9.74               (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74                (k2_struct_0 @ X0))))
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 9.51/9.74      inference('simplify', [status(thm)], ['41'])).
% 9.51/9.74  thf('43', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         (~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.74          | (r2_hidden @ 
% 9.51/9.74             (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74              (k2_struct_0 @ X0)) @ 
% 9.51/9.74             (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 9.51/9.74      inference('sup-', [status(thm)], ['17', '18'])).
% 9.51/9.74  thf('44', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         (~ (l1_struct_0 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 9.51/9.74              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 9.51/9.74      inference('sup-', [status(thm)], ['20', '21'])).
% 9.51/9.74  thf('45', plain,
% 9.51/9.74      (![X6 : $i]:
% 9.51/9.74         ((m1_subset_1 @ (k2_struct_0 @ X6) @ 
% 9.51/9.74           (k1_zfmisc_1 @ (u1_struct_0 @ X6)))
% 9.51/9.74          | ~ (l1_struct_0 @ X6))),
% 9.51/9.74      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 9.51/9.74  thf('46', plain,
% 9.51/9.74      (![X17 : $i, X18 : $i, X20 : $i]:
% 9.51/9.74         (~ (l1_orders_2 @ X17)
% 9.51/9.74          | ~ (v5_orders_2 @ X17)
% 9.51/9.74          | ~ (v4_orders_2 @ X17)
% 9.51/9.74          | ~ (v3_orders_2 @ X17)
% 9.51/9.74          | (v2_struct_0 @ X17)
% 9.51/9.74          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 9.51/9.74          | (m1_subset_1 @ (sk_D @ X18 @ X17 @ X20) @ (u1_struct_0 @ X17))
% 9.51/9.74          | ~ (r2_hidden @ X20 @ (a_2_1_orders_2 @ X17 @ X18)))),
% 9.51/9.74      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 9.51/9.74  thf('47', plain,
% 9.51/9.74      (![X0 : $i, X1 : $i]:
% 9.51/9.74         (~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 9.51/9.74          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 9.51/9.74             (u1_struct_0 @ X0))
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0))),
% 9.51/9.74      inference('sup-', [status(thm)], ['45', '46'])).
% 9.51/9.74  thf('48', plain,
% 9.51/9.74      (![X0 : $i, X1 : $i]:
% 9.51/9.74         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 9.51/9.74             (u1_struct_0 @ X0))
% 9.51/9.74          | ~ (l1_struct_0 @ X0))),
% 9.51/9.74      inference('sup-', [status(thm)], ['44', '47'])).
% 9.51/9.74  thf('49', plain,
% 9.51/9.74      (![X0 : $i, X1 : $i]:
% 9.51/9.74         ((m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 9.51/9.74           (u1_struct_0 @ X0))
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 9.51/9.74      inference('simplify', [status(thm)], ['48'])).
% 9.51/9.74  thf('50', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | (m1_subset_1 @ 
% 9.51/9.74             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 9.51/9.74              (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74               (k2_struct_0 @ X0))) @ 
% 9.51/9.74             (u1_struct_0 @ X0)))),
% 9.51/9.74      inference('sup-', [status(thm)], ['43', '49'])).
% 9.51/9.74  thf('51', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         ((m1_subset_1 @ 
% 9.51/9.74           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 9.51/9.74            (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74             (k2_struct_0 @ X0))) @ 
% 9.51/9.74           (u1_struct_0 @ X0))
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 9.51/9.74      inference('simplify', [status(thm)], ['50'])).
% 9.51/9.74  thf(d10_orders_2, axiom,
% 9.51/9.74    (![A:$i]:
% 9.51/9.74     ( ( l1_orders_2 @ A ) =>
% 9.51/9.74       ( ![B:$i]:
% 9.51/9.74         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 9.51/9.74           ( ![C:$i]:
% 9.51/9.74             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 9.51/9.74               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 9.51/9.74                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 9.51/9.74  thf('52', plain,
% 9.51/9.74      (![X9 : $i, X10 : $i, X11 : $i]:
% 9.51/9.74         (~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X10))
% 9.51/9.74          | ~ (r2_orders_2 @ X10 @ X9 @ X11)
% 9.51/9.74          | ((X9) != (X11))
% 9.51/9.74          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10))
% 9.51/9.74          | ~ (l1_orders_2 @ X10))),
% 9.51/9.74      inference('cnf', [status(esa)], [d10_orders_2])).
% 9.51/9.74  thf('53', plain,
% 9.51/9.74      (![X10 : $i, X11 : $i]:
% 9.51/9.74         (~ (l1_orders_2 @ X10)
% 9.51/9.74          | ~ (r2_orders_2 @ X10 @ X11 @ X11)
% 9.51/9.74          | ~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X10)))),
% 9.51/9.74      inference('simplify', [status(thm)], ['52'])).
% 9.51/9.74  thf('54', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (r2_orders_2 @ X0 @ 
% 9.51/9.74               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 9.51/9.74                (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74                 (k2_struct_0 @ X0))) @ 
% 9.51/9.74               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 9.51/9.74                (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74                 (k2_struct_0 @ X0))))
% 9.51/9.74          | ~ (l1_orders_2 @ X0))),
% 9.51/9.74      inference('sup-', [status(thm)], ['51', '53'])).
% 9.51/9.74  thf('55', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         (~ (r2_orders_2 @ X0 @ 
% 9.51/9.74             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 9.51/9.74              (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74               (k2_struct_0 @ X0))) @ 
% 9.51/9.74             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 9.51/9.74              (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74               (k2_struct_0 @ X0))))
% 9.51/9.74          | ~ (l1_struct_0 @ X0)
% 9.51/9.74          | ~ (l1_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 9.51/9.74      inference('simplify', [status(thm)], ['54'])).
% 9.51/9.74  thf('56', plain,
% 9.51/9.74      (![X0 : $i]:
% 9.51/9.74         (~ (r2_orders_2 @ X0 @ 
% 9.51/9.74             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 9.51/9.74              (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74               (k2_struct_0 @ X0))) @ 
% 9.51/9.74             (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.74              (k2_struct_0 @ X0)))
% 9.51/9.74          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.74          | (v2_struct_0 @ X0)
% 9.51/9.74          | ~ (v3_orders_2 @ X0)
% 9.51/9.74          | ~ (v4_orders_2 @ X0)
% 9.51/9.74          | ~ (v5_orders_2 @ X0)
% 9.51/9.75          | ~ (l1_orders_2 @ X0)
% 9.51/9.75          | ~ (l1_struct_0 @ X0)
% 9.51/9.75          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.75          | (v2_struct_0 @ X0)
% 9.51/9.75          | ~ (v3_orders_2 @ X0)
% 9.51/9.75          | ~ (v4_orders_2 @ X0)
% 9.51/9.75          | ~ (v5_orders_2 @ X0)
% 9.51/9.75          | ~ (l1_orders_2 @ X0)
% 9.51/9.75          | ~ (l1_struct_0 @ X0))),
% 9.51/9.75      inference('sup-', [status(thm)], ['42', '55'])).
% 9.51/9.75  thf('57', plain,
% 9.51/9.75      (![X0 : $i]:
% 9.51/9.75         (~ (l1_struct_0 @ X0)
% 9.51/9.75          | ~ (l1_orders_2 @ X0)
% 9.51/9.75          | ~ (v5_orders_2 @ X0)
% 9.51/9.75          | ~ (v4_orders_2 @ X0)
% 9.51/9.75          | ~ (v3_orders_2 @ X0)
% 9.51/9.75          | (v2_struct_0 @ X0)
% 9.51/9.75          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.75          | ~ (r2_orders_2 @ X0 @ 
% 9.51/9.75               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 9.51/9.75                (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.75                 (k2_struct_0 @ X0))) @ 
% 9.51/9.75               (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 9.51/9.75                (k2_struct_0 @ X0))))),
% 9.51/9.75      inference('simplify', [status(thm)], ['56'])).
% 9.51/9.75  thf('58', plain,
% 9.51/9.75      (![X0 : $i]:
% 9.51/9.75         (~ (l1_struct_0 @ X0)
% 9.51/9.75          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.75          | (v2_struct_0 @ X0)
% 9.51/9.75          | ~ (v3_orders_2 @ X0)
% 9.51/9.75          | ~ (v4_orders_2 @ X0)
% 9.51/9.75          | ~ (v5_orders_2 @ X0)
% 9.51/9.75          | ~ (l1_orders_2 @ X0)
% 9.51/9.75          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 9.51/9.75          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.75          | (v2_struct_0 @ X0)
% 9.51/9.75          | ~ (v3_orders_2 @ X0)
% 9.51/9.75          | ~ (v4_orders_2 @ X0)
% 9.51/9.75          | ~ (v5_orders_2 @ X0)
% 9.51/9.75          | ~ (l1_orders_2 @ X0)
% 9.51/9.75          | ~ (l1_struct_0 @ X0))),
% 9.51/9.75      inference('sup-', [status(thm)], ['33', '57'])).
% 9.51/9.75  thf('59', plain,
% 9.51/9.75      (![X0 : $i]:
% 9.51/9.75         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 9.51/9.75          | ~ (l1_orders_2 @ X0)
% 9.51/9.75          | ~ (v5_orders_2 @ X0)
% 9.51/9.75          | ~ (v4_orders_2 @ X0)
% 9.51/9.75          | ~ (v3_orders_2 @ X0)
% 9.51/9.75          | (v2_struct_0 @ X0)
% 9.51/9.75          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 9.51/9.75          | ~ (l1_struct_0 @ X0))),
% 9.51/9.75      inference('simplify', [status(thm)], ['58'])).
% 9.51/9.75  thf('60', plain,
% 9.51/9.75      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 9.51/9.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.51/9.75  thf('61', plain,
% 9.51/9.75      ((((k1_xboole_0) != (k1_xboole_0))
% 9.51/9.75        | ~ (l1_struct_0 @ sk_A)
% 9.51/9.75        | (v2_struct_0 @ sk_A)
% 9.51/9.75        | ~ (v3_orders_2 @ sk_A)
% 9.51/9.75        | ~ (v4_orders_2 @ sk_A)
% 9.51/9.75        | ~ (v5_orders_2 @ sk_A)
% 9.51/9.75        | ~ (l1_orders_2 @ sk_A)
% 9.51/9.75        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 9.51/9.75      inference('sup-', [status(thm)], ['59', '60'])).
% 9.51/9.75  thf('62', plain, ((l1_orders_2 @ sk_A)),
% 9.51/9.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.51/9.75  thf(dt_l1_orders_2, axiom,
% 9.51/9.75    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 9.51/9.75  thf('63', plain,
% 9.51/9.75      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_orders_2 @ X16))),
% 9.51/9.75      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 9.51/9.75  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 9.51/9.75      inference('sup-', [status(thm)], ['62', '63'])).
% 9.51/9.75  thf('65', plain, ((v3_orders_2 @ sk_A)),
% 9.51/9.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.51/9.75  thf('66', plain, ((v4_orders_2 @ sk_A)),
% 9.51/9.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.51/9.75  thf('67', plain, ((v5_orders_2 @ sk_A)),
% 9.51/9.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.51/9.75  thf('68', plain, ((l1_orders_2 @ sk_A)),
% 9.51/9.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.51/9.75  thf('69', plain,
% 9.51/9.75      ((((k1_xboole_0) != (k1_xboole_0))
% 9.51/9.75        | (v2_struct_0 @ sk_A)
% 9.51/9.75        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 9.51/9.75      inference('demod', [status(thm)], ['61', '64', '65', '66', '67', '68'])).
% 9.51/9.75  thf('70', plain,
% 9.51/9.75      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 9.51/9.75      inference('simplify', [status(thm)], ['69'])).
% 9.51/9.75  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 9.51/9.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 9.51/9.75  thf('72', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 9.51/9.75      inference('clc', [status(thm)], ['70', '71'])).
% 9.51/9.75  thf('73', plain,
% 9.51/9.75      (![X5 : $i]:
% 9.51/9.75         (((k2_struct_0 @ X5) = (u1_struct_0 @ X5)) | ~ (l1_struct_0 @ X5))),
% 9.51/9.75      inference('cnf', [status(esa)], [d3_struct_0])).
% 9.51/9.75  thf(fc2_struct_0, axiom,
% 9.51/9.75    (![A:$i]:
% 9.51/9.75     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 9.51/9.75       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 9.51/9.75  thf('74', plain,
% 9.51/9.75      (![X8 : $i]:
% 9.51/9.75         (~ (v1_xboole_0 @ (u1_struct_0 @ X8))
% 9.51/9.75          | ~ (l1_struct_0 @ X8)
% 9.51/9.75          | (v2_struct_0 @ X8))),
% 9.51/9.75      inference('cnf', [status(esa)], [fc2_struct_0])).
% 9.51/9.75  thf('75', plain,
% 9.51/9.75      (![X0 : $i]:
% 9.51/9.75         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 9.51/9.75          | ~ (l1_struct_0 @ X0)
% 9.51/9.75          | (v2_struct_0 @ X0)
% 9.51/9.75          | ~ (l1_struct_0 @ X0))),
% 9.51/9.75      inference('sup-', [status(thm)], ['73', '74'])).
% 9.51/9.75  thf('76', plain,
% 9.51/9.75      (![X0 : $i]:
% 9.51/9.75         ((v2_struct_0 @ X0)
% 9.51/9.75          | ~ (l1_struct_0 @ X0)
% 9.51/9.75          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 9.51/9.75      inference('simplify', [status(thm)], ['75'])).
% 9.51/9.75  thf('77', plain, ((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 9.51/9.75      inference('sup-', [status(thm)], ['72', '76'])).
% 9.51/9.75  thf('78', plain, ((l1_struct_0 @ sk_A)),
% 9.51/9.75      inference('sup-', [status(thm)], ['62', '63'])).
% 9.51/9.75  thf('79', plain, ((v2_struct_0 @ sk_A)),
% 9.51/9.75      inference('demod', [status(thm)], ['77', '78'])).
% 9.51/9.75  thf('80', plain, ($false), inference('demod', [status(thm)], ['0', '79'])).
% 9.51/9.75  
% 9.51/9.75  % SZS output end Refutation
% 9.51/9.75  
% 9.51/9.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
