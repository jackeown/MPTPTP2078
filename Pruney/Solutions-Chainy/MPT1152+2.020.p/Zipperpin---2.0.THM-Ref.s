%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dl64UKvp6y

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:45 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 184 expanded)
%              Number of leaves         :   31 (  67 expanded)
%              Depth                    :   20
%              Number of atoms          : 1942 (2974 expanded)
%              Number of equality atoms :   55 (  91 expanded)
%              Maximal formula depth    :   25 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

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
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( v5_orders_2 @ X12 )
      | ~ ( v4_orders_2 @ X12 )
      | ~ ( v3_orders_2 @ X12 )
      | ( v2_struct_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ( m1_subset_1 @ ( k2_orders_2 @ X12 @ X13 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
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
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
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

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

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
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
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
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
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
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
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
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('37',plain,(
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
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X5 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X5 ) ) )
      | ~ ( l1_struct_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('46',plain,(
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( u1_struct_0 @ X8 ) )
      | ~ ( r2_orders_2 @ X8 @ X7 @ X9 )
      | ( X7 != X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) )
      | ~ ( l1_orders_2 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('53',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( l1_orders_2 @ X8 )
      | ~ ( r2_orders_2 @ X8 @ X9 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( u1_struct_0 @ X8 ) ) ) ),
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
    ! [X14: $i] :
      ( ( l1_struct_0 @ X14 )
      | ~ ( l1_orders_2 @ X14 ) ) ),
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
    ! [X4: $i] :
      ( ( ( k2_struct_0 @ X4 )
        = ( u1_struct_0 @ X4 ) )
      | ~ ( l1_struct_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('74',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X6 ) )
      | ~ ( l1_struct_0 @ X6 )
      | ( v2_struct_0 @ X6 ) ) ),
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
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dl64UKvp6y
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:21:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.53/1.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.53/1.72  % Solved by: fo/fo7.sh
% 1.53/1.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.53/1.72  % done 880 iterations in 1.262s
% 1.53/1.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.53/1.72  % SZS output start Refutation
% 1.53/1.72  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.53/1.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.53/1.72  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 1.53/1.72  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 1.53/1.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.53/1.72  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.53/1.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.53/1.72  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 1.53/1.72  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 1.53/1.72  thf(sk_A_type, type, sk_A: $i).
% 1.53/1.72  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.53/1.72  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 1.53/1.72  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.53/1.72  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.53/1.72  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 1.53/1.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.53/1.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.53/1.72  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 1.53/1.72  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.53/1.72  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.53/1.72  thf(t46_orders_2, conjecture,
% 1.53/1.72    (![A:$i]:
% 1.53/1.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.53/1.72         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.53/1.72       ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 1.53/1.72  thf(zf_stmt_0, negated_conjecture,
% 1.53/1.72    (~( ![A:$i]:
% 1.53/1.72        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.53/1.72            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.53/1.72          ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 1.53/1.72    inference('cnf.neg', [status(esa)], [t46_orders_2])).
% 1.53/1.72  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.72  thf(d3_struct_0, axiom,
% 1.53/1.72    (![A:$i]:
% 1.53/1.72     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.53/1.72  thf('1', plain,
% 1.53/1.72      (![X4 : $i]:
% 1.53/1.72         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 1.53/1.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.53/1.72  thf(dt_k2_struct_0, axiom,
% 1.53/1.72    (![A:$i]:
% 1.53/1.72     ( ( l1_struct_0 @ A ) =>
% 1.53/1.72       ( m1_subset_1 @
% 1.53/1.72         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.53/1.72  thf('2', plain,
% 1.53/1.72      (![X5 : $i]:
% 1.53/1.72         ((m1_subset_1 @ (k2_struct_0 @ X5) @ 
% 1.53/1.72           (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 1.53/1.72          | ~ (l1_struct_0 @ X5))),
% 1.53/1.72      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.53/1.72  thf(dt_k2_orders_2, axiom,
% 1.53/1.72    (![A:$i,B:$i]:
% 1.53/1.72     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.53/1.72         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 1.53/1.72         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.53/1.72       ( m1_subset_1 @
% 1.53/1.72         ( k2_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.53/1.72  thf('3', plain,
% 1.53/1.72      (![X12 : $i, X13 : $i]:
% 1.53/1.72         (~ (l1_orders_2 @ X12)
% 1.53/1.72          | ~ (v5_orders_2 @ X12)
% 1.53/1.72          | ~ (v4_orders_2 @ X12)
% 1.53/1.72          | ~ (v3_orders_2 @ X12)
% 1.53/1.72          | (v2_struct_0 @ X12)
% 1.53/1.72          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.53/1.72          | (m1_subset_1 @ (k2_orders_2 @ X12 @ X13) @ 
% 1.53/1.72             (k1_zfmisc_1 @ (u1_struct_0 @ X12))))),
% 1.53/1.72      inference('cnf', [status(esa)], [dt_k2_orders_2])).
% 1.53/1.72  thf('4', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         (~ (l1_struct_0 @ X0)
% 1.53/1.72          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.72             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.53/1.72          | (v2_struct_0 @ X0)
% 1.53/1.72          | ~ (v3_orders_2 @ X0)
% 1.53/1.72          | ~ (v4_orders_2 @ X0)
% 1.53/1.72          | ~ (v5_orders_2 @ X0)
% 1.53/1.72          | ~ (l1_orders_2 @ X0))),
% 1.53/1.72      inference('sup-', [status(thm)], ['2', '3'])).
% 1.53/1.72  thf(t10_subset_1, axiom,
% 1.53/1.72    (![A:$i,B:$i]:
% 1.53/1.72     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.53/1.72       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 1.53/1.72            ( ![C:$i]:
% 1.53/1.72              ( ( m1_subset_1 @ C @ A ) => ( ~( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.53/1.72  thf('5', plain,
% 1.53/1.72      (![X0 : $i, X1 : $i]:
% 1.53/1.72         ((m1_subset_1 @ (sk_C @ X0 @ X1) @ X1)
% 1.53/1.72          | ((X0) = (k1_xboole_0))
% 1.53/1.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 1.53/1.72      inference('cnf', [status(esa)], [t10_subset_1])).
% 1.53/1.72  thf('6', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         (~ (l1_orders_2 @ X0)
% 1.53/1.72          | ~ (v5_orders_2 @ X0)
% 1.53/1.72          | ~ (v4_orders_2 @ X0)
% 1.53/1.72          | ~ (v3_orders_2 @ X0)
% 1.53/1.72          | (v2_struct_0 @ X0)
% 1.53/1.72          | ~ (l1_struct_0 @ X0)
% 1.53/1.72          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.72          | (m1_subset_1 @ 
% 1.53/1.72             (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.72              (u1_struct_0 @ X0)) @ 
% 1.53/1.72             (u1_struct_0 @ X0)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['4', '5'])).
% 1.53/1.72  thf('7', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         ((m1_subset_1 @ 
% 1.53/1.72           (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ (k2_struct_0 @ X0)) @ 
% 1.53/1.72           (u1_struct_0 @ X0))
% 1.53/1.72          | ~ (l1_struct_0 @ X0)
% 1.53/1.72          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.72          | ~ (l1_struct_0 @ X0)
% 1.53/1.72          | (v2_struct_0 @ X0)
% 1.53/1.72          | ~ (v3_orders_2 @ X0)
% 1.53/1.72          | ~ (v4_orders_2 @ X0)
% 1.53/1.72          | ~ (v5_orders_2 @ X0)
% 1.53/1.72          | ~ (l1_orders_2 @ X0))),
% 1.53/1.72      inference('sup+', [status(thm)], ['1', '6'])).
% 1.53/1.72  thf('8', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         (~ (l1_orders_2 @ X0)
% 1.53/1.72          | ~ (v5_orders_2 @ X0)
% 1.53/1.72          | ~ (v4_orders_2 @ X0)
% 1.53/1.72          | ~ (v3_orders_2 @ X0)
% 1.53/1.72          | (v2_struct_0 @ X0)
% 1.53/1.72          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.72          | ~ (l1_struct_0 @ X0)
% 1.53/1.72          | (m1_subset_1 @ 
% 1.53/1.72             (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.72              (k2_struct_0 @ X0)) @ 
% 1.53/1.72             (u1_struct_0 @ X0)))),
% 1.53/1.72      inference('simplify', [status(thm)], ['7'])).
% 1.53/1.72  thf('9', plain,
% 1.53/1.72      (![X4 : $i]:
% 1.53/1.72         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 1.53/1.72      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.53/1.72  thf('10', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         (~ (l1_struct_0 @ X0)
% 1.53/1.72          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.72             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.53/1.72          | (v2_struct_0 @ X0)
% 1.53/1.72          | ~ (v3_orders_2 @ X0)
% 1.53/1.72          | ~ (v4_orders_2 @ X0)
% 1.53/1.72          | ~ (v5_orders_2 @ X0)
% 1.53/1.72          | ~ (l1_orders_2 @ X0))),
% 1.53/1.72      inference('sup-', [status(thm)], ['2', '3'])).
% 1.53/1.72  thf('11', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         ((m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.72           (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 1.53/1.72          | ~ (l1_struct_0 @ X0)
% 1.53/1.72          | ~ (l1_orders_2 @ X0)
% 1.53/1.72          | ~ (v5_orders_2 @ X0)
% 1.53/1.72          | ~ (v4_orders_2 @ X0)
% 1.53/1.72          | ~ (v3_orders_2 @ X0)
% 1.53/1.72          | (v2_struct_0 @ X0)
% 1.53/1.72          | ~ (l1_struct_0 @ X0))),
% 1.53/1.72      inference('sup+', [status(thm)], ['9', '10'])).
% 1.53/1.72  thf('12', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         ((v2_struct_0 @ X0)
% 1.53/1.72          | ~ (v3_orders_2 @ X0)
% 1.53/1.72          | ~ (v4_orders_2 @ X0)
% 1.53/1.72          | ~ (v5_orders_2 @ X0)
% 1.53/1.72          | ~ (l1_orders_2 @ X0)
% 1.53/1.72          | ~ (l1_struct_0 @ X0)
% 1.53/1.72          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.72             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 1.53/1.72      inference('simplify', [status(thm)], ['11'])).
% 1.53/1.72  thf('13', plain,
% 1.53/1.72      (![X0 : $i, X1 : $i]:
% 1.53/1.72         ((m1_subset_1 @ (sk_C @ X0 @ X1) @ X1)
% 1.53/1.72          | ((X0) = (k1_xboole_0))
% 1.53/1.72          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 1.53/1.72      inference('cnf', [status(esa)], [t10_subset_1])).
% 1.53/1.72  thf('14', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.72         (~ (l1_struct_0 @ X0)
% 1.53/1.72          | ~ (l1_orders_2 @ X0)
% 1.53/1.72          | ~ (v5_orders_2 @ X0)
% 1.53/1.72          | ~ (v4_orders_2 @ X0)
% 1.53/1.72          | ~ (v3_orders_2 @ X0)
% 1.53/1.72          | (v2_struct_0 @ X0)
% 1.53/1.72          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.72          | (m1_subset_1 @ 
% 1.53/1.72             (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.72              (k2_struct_0 @ X0)) @ 
% 1.53/1.72             (k2_struct_0 @ X0)))),
% 1.53/1.72      inference('sup-', [status(thm)], ['12', '13'])).
% 1.53/1.72  thf(t2_subset, axiom,
% 1.53/1.72    (![A:$i,B:$i]:
% 1.53/1.72     ( ( m1_subset_1 @ A @ B ) =>
% 1.53/1.72       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.53/1.72  thf('15', plain,
% 1.53/1.72      (![X2 : $i, X3 : $i]:
% 1.53/1.72         ((r2_hidden @ X2 @ X3)
% 1.53/1.72          | (v1_xboole_0 @ X3)
% 1.53/1.72          | ~ (m1_subset_1 @ X2 @ X3))),
% 1.53/1.72      inference('cnf', [status(esa)], [t2_subset])).
% 1.53/1.72  thf('16', plain,
% 1.53/1.72      (![X0 : $i]:
% 1.53/1.73         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.53/1.73          | (r2_hidden @ 
% 1.53/1.73             (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73              (k2_struct_0 @ X0)) @ 
% 1.53/1.73             (k2_struct_0 @ X0)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['14', '15'])).
% 1.53/1.73  thf('17', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         ((v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 1.53/1.73      inference('simplify', [status(thm)], ['11'])).
% 1.53/1.73  thf('18', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]:
% 1.53/1.73         ((r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 1.53/1.73          | ((X0) = (k1_xboole_0))
% 1.53/1.73          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 1.53/1.73      inference('cnf', [status(esa)], [t10_subset_1])).
% 1.53/1.73  thf('19', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.73          | (r2_hidden @ 
% 1.53/1.73             (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73              (k2_struct_0 @ X0)) @ 
% 1.53/1.73             (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['17', '18'])).
% 1.53/1.73  thf('20', plain,
% 1.53/1.73      (![X5 : $i]:
% 1.53/1.73         ((m1_subset_1 @ (k2_struct_0 @ X5) @ 
% 1.53/1.73           (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 1.53/1.73          | ~ (l1_struct_0 @ X5))),
% 1.53/1.73      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.53/1.73  thf(d13_orders_2, axiom,
% 1.53/1.73    (![A:$i]:
% 1.53/1.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.53/1.73         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.53/1.73       ( ![B:$i]:
% 1.53/1.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.53/1.73           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 1.53/1.73  thf('21', plain,
% 1.53/1.73      (![X10 : $i, X11 : $i]:
% 1.53/1.73         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 1.53/1.73          | ((k2_orders_2 @ X11 @ X10) = (a_2_1_orders_2 @ X11 @ X10))
% 1.53/1.73          | ~ (l1_orders_2 @ X11)
% 1.53/1.73          | ~ (v5_orders_2 @ X11)
% 1.53/1.73          | ~ (v4_orders_2 @ X11)
% 1.53/1.73          | ~ (v3_orders_2 @ X11)
% 1.53/1.73          | (v2_struct_0 @ X11))),
% 1.53/1.73      inference('cnf', [status(esa)], [d13_orders_2])).
% 1.53/1.73  thf('22', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 1.53/1.73              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['20', '21'])).
% 1.53/1.73  thf('23', plain,
% 1.53/1.73      (![X5 : $i]:
% 1.53/1.73         ((m1_subset_1 @ (k2_struct_0 @ X5) @ 
% 1.53/1.73           (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 1.53/1.73          | ~ (l1_struct_0 @ X5))),
% 1.53/1.73      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.53/1.73  thf(fraenkel_a_2_1_orders_2, axiom,
% 1.53/1.73    (![A:$i,B:$i,C:$i]:
% 1.53/1.73     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 1.53/1.73         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 1.53/1.73         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 1.53/1.73       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 1.53/1.73         ( ?[D:$i]:
% 1.53/1.73           ( ( ![E:$i]:
% 1.53/1.73               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 1.53/1.73                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 1.53/1.73             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.53/1.73  thf('24', plain,
% 1.53/1.73      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 1.53/1.73         (~ (l1_orders_2 @ X15)
% 1.53/1.73          | ~ (v5_orders_2 @ X15)
% 1.53/1.73          | ~ (v4_orders_2 @ X15)
% 1.53/1.73          | ~ (v3_orders_2 @ X15)
% 1.53/1.73          | (v2_struct_0 @ X15)
% 1.53/1.73          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.53/1.73          | ~ (m1_subset_1 @ X17 @ (u1_struct_0 @ X15))
% 1.53/1.73          | (r2_orders_2 @ X15 @ (sk_D @ X16 @ X15 @ X18) @ X17)
% 1.53/1.73          | ~ (r2_hidden @ X17 @ X16)
% 1.53/1.73          | ~ (r2_hidden @ X18 @ (a_2_1_orders_2 @ X15 @ X16)))),
% 1.53/1.73      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 1.53/1.73  thf('25', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 1.53/1.73          | ~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 1.53/1.73          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 1.53/1.73          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0))),
% 1.53/1.73      inference('sup-', [status(thm)], ['23', '24'])).
% 1.53/1.73  thf('26', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.73         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.53/1.73          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 1.53/1.73          | ~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 1.53/1.73          | ~ (l1_struct_0 @ X0))),
% 1.53/1.73      inference('sup-', [status(thm)], ['22', '25'])).
% 1.53/1.73  thf('27', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.53/1.73         (~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 1.53/1.73          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 1.53/1.73          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 1.53/1.73      inference('simplify', [status(thm)], ['26'])).
% 1.53/1.73  thf('28', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]:
% 1.53/1.73         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 1.53/1.73          | (r2_orders_2 @ X0 @ 
% 1.53/1.73             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.53/1.73              (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73               (k2_struct_0 @ X0))) @ 
% 1.53/1.73             X1)
% 1.53/1.73          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['19', '27'])).
% 1.53/1.73  thf('29', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]:
% 1.53/1.73         (~ (r2_hidden @ X1 @ (k2_struct_0 @ X0))
% 1.53/1.73          | (r2_orders_2 @ X0 @ 
% 1.53/1.73             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.53/1.73              (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73               (k2_struct_0 @ X0))) @ 
% 1.53/1.73             X1)
% 1.53/1.73          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 1.53/1.73      inference('simplify', [status(thm)], ['28'])).
% 1.53/1.73  thf('30', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (m1_subset_1 @ 
% 1.53/1.73               (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73                (k2_struct_0 @ X0)) @ 
% 1.53/1.73               (u1_struct_0 @ X0))
% 1.53/1.73          | (r2_orders_2 @ X0 @ 
% 1.53/1.73             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.53/1.73              (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73               (k2_struct_0 @ X0))) @ 
% 1.53/1.73             (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73              (k2_struct_0 @ X0))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['16', '29'])).
% 1.53/1.73  thf('31', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         ((r2_orders_2 @ X0 @ 
% 1.53/1.73           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.53/1.73            (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73             (k2_struct_0 @ X0))) @ 
% 1.53/1.73           (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ (k2_struct_0 @ X0)))
% 1.53/1.73          | ~ (m1_subset_1 @ 
% 1.53/1.73               (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73                (k2_struct_0 @ X0)) @ 
% 1.53/1.73               (u1_struct_0 @ X0))
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 1.53/1.73      inference('simplify', [status(thm)], ['30'])).
% 1.53/1.73  thf('32', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X0)
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.73          | (r2_orders_2 @ X0 @ 
% 1.53/1.73             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.53/1.73              (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73               (k2_struct_0 @ X0))) @ 
% 1.53/1.73             (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73              (k2_struct_0 @ X0))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['8', '31'])).
% 1.53/1.73  thf('33', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         ((r2_orders_2 @ X0 @ 
% 1.53/1.73           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.53/1.73            (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73             (k2_struct_0 @ X0))) @ 
% 1.53/1.73           (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ (k2_struct_0 @ X0)))
% 1.53/1.73          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.73          | ~ (l1_struct_0 @ X0))),
% 1.53/1.73      inference('simplify', [status(thm)], ['32'])).
% 1.53/1.73  thf('34', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.73          | (r2_hidden @ 
% 1.53/1.73             (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73              (k2_struct_0 @ X0)) @ 
% 1.53/1.73             (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['17', '18'])).
% 1.53/1.73  thf('35', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 1.53/1.73              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['20', '21'])).
% 1.53/1.73  thf('36', plain,
% 1.53/1.73      (![X5 : $i]:
% 1.53/1.73         ((m1_subset_1 @ (k2_struct_0 @ X5) @ 
% 1.53/1.73           (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 1.53/1.73          | ~ (l1_struct_0 @ X5))),
% 1.53/1.73      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.53/1.73  thf('37', plain,
% 1.53/1.73      (![X15 : $i, X16 : $i, X18 : $i]:
% 1.53/1.73         (~ (l1_orders_2 @ X15)
% 1.53/1.73          | ~ (v5_orders_2 @ X15)
% 1.53/1.73          | ~ (v4_orders_2 @ X15)
% 1.53/1.73          | ~ (v3_orders_2 @ X15)
% 1.53/1.73          | (v2_struct_0 @ X15)
% 1.53/1.73          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.53/1.73          | ((X18) = (sk_D @ X16 @ X15 @ X18))
% 1.53/1.73          | ~ (r2_hidden @ X18 @ (a_2_1_orders_2 @ X15 @ X16)))),
% 1.53/1.73      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 1.53/1.73  thf('38', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 1.53/1.73          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0))),
% 1.53/1.73      inference('sup-', [status(thm)], ['36', '37'])).
% 1.53/1.73  thf('39', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]:
% 1.53/1.73         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 1.53/1.73          | ~ (l1_struct_0 @ X0))),
% 1.53/1.73      inference('sup-', [status(thm)], ['35', '38'])).
% 1.53/1.73  thf('40', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]:
% 1.53/1.73         (((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 1.53/1.73      inference('simplify', [status(thm)], ['39'])).
% 1.53/1.73  thf('41', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | ((sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73              (k2_struct_0 @ X0))
% 1.53/1.73              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.53/1.73                 (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73                  (k2_struct_0 @ X0)))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['34', '40'])).
% 1.53/1.73  thf('42', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (((sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ (k2_struct_0 @ X0))
% 1.53/1.73            = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.53/1.73               (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73                (k2_struct_0 @ X0))))
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 1.53/1.73      inference('simplify', [status(thm)], ['41'])).
% 1.53/1.73  thf('43', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.73          | (r2_hidden @ 
% 1.53/1.73             (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73              (k2_struct_0 @ X0)) @ 
% 1.53/1.73             (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['17', '18'])).
% 1.53/1.73  thf('44', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 1.53/1.73              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 1.53/1.73      inference('sup-', [status(thm)], ['20', '21'])).
% 1.53/1.73  thf('45', plain,
% 1.53/1.73      (![X5 : $i]:
% 1.53/1.73         ((m1_subset_1 @ (k2_struct_0 @ X5) @ 
% 1.53/1.73           (k1_zfmisc_1 @ (u1_struct_0 @ X5)))
% 1.53/1.73          | ~ (l1_struct_0 @ X5))),
% 1.53/1.73      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.53/1.73  thf('46', plain,
% 1.53/1.73      (![X15 : $i, X16 : $i, X18 : $i]:
% 1.53/1.73         (~ (l1_orders_2 @ X15)
% 1.53/1.73          | ~ (v5_orders_2 @ X15)
% 1.53/1.73          | ~ (v4_orders_2 @ X15)
% 1.53/1.73          | ~ (v3_orders_2 @ X15)
% 1.53/1.73          | (v2_struct_0 @ X15)
% 1.53/1.73          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 1.53/1.73          | (m1_subset_1 @ (sk_D @ X16 @ X15 @ X18) @ (u1_struct_0 @ X15))
% 1.53/1.73          | ~ (r2_hidden @ X18 @ (a_2_1_orders_2 @ X15 @ X16)))),
% 1.53/1.73      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 1.53/1.73  thf('47', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 1.53/1.73          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 1.53/1.73             (u1_struct_0 @ X0))
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0))),
% 1.53/1.73      inference('sup-', [status(thm)], ['45', '46'])).
% 1.53/1.73  thf('48', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]:
% 1.53/1.73         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 1.53/1.73             (u1_struct_0 @ X0))
% 1.53/1.73          | ~ (l1_struct_0 @ X0))),
% 1.53/1.73      inference('sup-', [status(thm)], ['44', '47'])).
% 1.53/1.73  thf('49', plain,
% 1.53/1.73      (![X0 : $i, X1 : $i]:
% 1.53/1.73         ((m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 1.53/1.73           (u1_struct_0 @ X0))
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 1.53/1.73      inference('simplify', [status(thm)], ['48'])).
% 1.53/1.73  thf('50', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | (m1_subset_1 @ 
% 1.53/1.73             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.53/1.73              (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73               (k2_struct_0 @ X0))) @ 
% 1.53/1.73             (u1_struct_0 @ X0)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['43', '49'])).
% 1.53/1.73  thf('51', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         ((m1_subset_1 @ 
% 1.53/1.73           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.53/1.73            (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73             (k2_struct_0 @ X0))) @ 
% 1.53/1.73           (u1_struct_0 @ X0))
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 1.53/1.73      inference('simplify', [status(thm)], ['50'])).
% 1.53/1.73  thf(d10_orders_2, axiom,
% 1.53/1.73    (![A:$i]:
% 1.53/1.73     ( ( l1_orders_2 @ A ) =>
% 1.53/1.73       ( ![B:$i]:
% 1.53/1.73         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.53/1.73           ( ![C:$i]:
% 1.53/1.73             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.53/1.73               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 1.53/1.73                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 1.53/1.73  thf('52', plain,
% 1.53/1.73      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.53/1.73         (~ (m1_subset_1 @ X7 @ (u1_struct_0 @ X8))
% 1.53/1.73          | ~ (r2_orders_2 @ X8 @ X7 @ X9)
% 1.53/1.73          | ((X7) != (X9))
% 1.53/1.73          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8))
% 1.53/1.73          | ~ (l1_orders_2 @ X8))),
% 1.53/1.73      inference('cnf', [status(esa)], [d10_orders_2])).
% 1.53/1.73  thf('53', plain,
% 1.53/1.73      (![X8 : $i, X9 : $i]:
% 1.53/1.73         (~ (l1_orders_2 @ X8)
% 1.53/1.73          | ~ (r2_orders_2 @ X8 @ X9 @ X9)
% 1.53/1.73          | ~ (m1_subset_1 @ X9 @ (u1_struct_0 @ X8)))),
% 1.53/1.73      inference('simplify', [status(thm)], ['52'])).
% 1.53/1.73  thf('54', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (r2_orders_2 @ X0 @ 
% 1.53/1.73               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.53/1.73                (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73                 (k2_struct_0 @ X0))) @ 
% 1.53/1.73               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.53/1.73                (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73                 (k2_struct_0 @ X0))))
% 1.53/1.73          | ~ (l1_orders_2 @ X0))),
% 1.53/1.73      inference('sup-', [status(thm)], ['51', '53'])).
% 1.53/1.73  thf('55', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (~ (r2_orders_2 @ X0 @ 
% 1.53/1.73             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.53/1.73              (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73               (k2_struct_0 @ X0))) @ 
% 1.53/1.73             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.53/1.73              (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73               (k2_struct_0 @ X0))))
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 1.53/1.73      inference('simplify', [status(thm)], ['54'])).
% 1.53/1.73  thf('56', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (~ (r2_orders_2 @ X0 @ 
% 1.53/1.73             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.53/1.73              (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73               (k2_struct_0 @ X0))) @ 
% 1.53/1.73             (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73              (k2_struct_0 @ X0)))
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_struct_0 @ X0))),
% 1.53/1.73      inference('sup-', [status(thm)], ['42', '55'])).
% 1.53/1.73  thf('57', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.73          | ~ (r2_orders_2 @ X0 @ 
% 1.53/1.73               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.53/1.73                (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73                 (k2_struct_0 @ X0))) @ 
% 1.53/1.73               (sk_C @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.53/1.73                (k2_struct_0 @ X0))))),
% 1.53/1.73      inference('simplify', [status(thm)], ['56'])).
% 1.53/1.73  thf('58', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (~ (l1_struct_0 @ X0)
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (l1_struct_0 @ X0))),
% 1.53/1.73      inference('sup-', [status(thm)], ['33', '57'])).
% 1.53/1.73  thf('59', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.53/1.73          | ~ (l1_orders_2 @ X0)
% 1.53/1.73          | ~ (v5_orders_2 @ X0)
% 1.53/1.73          | ~ (v4_orders_2 @ X0)
% 1.53/1.73          | ~ (v3_orders_2 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.53/1.73          | ~ (l1_struct_0 @ X0))),
% 1.53/1.73      inference('simplify', [status(thm)], ['58'])).
% 1.53/1.73  thf('60', plain,
% 1.53/1.73      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('61', plain,
% 1.53/1.73      ((((k1_xboole_0) != (k1_xboole_0))
% 1.53/1.73        | ~ (l1_struct_0 @ sk_A)
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | ~ (v3_orders_2 @ sk_A)
% 1.53/1.73        | ~ (v4_orders_2 @ sk_A)
% 1.53/1.73        | ~ (v5_orders_2 @ sk_A)
% 1.53/1.73        | ~ (l1_orders_2 @ sk_A)
% 1.53/1.73        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 1.53/1.73      inference('sup-', [status(thm)], ['59', '60'])).
% 1.53/1.73  thf('62', plain, ((l1_orders_2 @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf(dt_l1_orders_2, axiom,
% 1.53/1.73    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 1.53/1.73  thf('63', plain,
% 1.53/1.73      (![X14 : $i]: ((l1_struct_0 @ X14) | ~ (l1_orders_2 @ X14))),
% 1.53/1.73      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 1.53/1.73  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 1.53/1.73      inference('sup-', [status(thm)], ['62', '63'])).
% 1.53/1.73  thf('65', plain, ((v3_orders_2 @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('66', plain, ((v4_orders_2 @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('67', plain, ((v5_orders_2 @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('68', plain, ((l1_orders_2 @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('69', plain,
% 1.53/1.73      ((((k1_xboole_0) != (k1_xboole_0))
% 1.53/1.73        | (v2_struct_0 @ sk_A)
% 1.53/1.73        | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 1.53/1.73      inference('demod', [status(thm)], ['61', '64', '65', '66', '67', '68'])).
% 1.53/1.73  thf('70', plain,
% 1.53/1.73      (((v1_xboole_0 @ (k2_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 1.53/1.73      inference('simplify', [status(thm)], ['69'])).
% 1.53/1.73  thf('71', plain, (~ (v2_struct_0 @ sk_A)),
% 1.53/1.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.53/1.73  thf('72', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 1.53/1.73      inference('clc', [status(thm)], ['70', '71'])).
% 1.53/1.73  thf('73', plain,
% 1.53/1.73      (![X4 : $i]:
% 1.53/1.73         (((k2_struct_0 @ X4) = (u1_struct_0 @ X4)) | ~ (l1_struct_0 @ X4))),
% 1.53/1.73      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.53/1.73  thf(fc2_struct_0, axiom,
% 1.53/1.73    (![A:$i]:
% 1.53/1.73     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 1.53/1.73       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.53/1.73  thf('74', plain,
% 1.53/1.73      (![X6 : $i]:
% 1.53/1.73         (~ (v1_xboole_0 @ (u1_struct_0 @ X6))
% 1.53/1.73          | ~ (l1_struct_0 @ X6)
% 1.53/1.73          | (v2_struct_0 @ X6))),
% 1.53/1.73      inference('cnf', [status(esa)], [fc2_struct_0])).
% 1.53/1.73  thf('75', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | (v2_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_struct_0 @ X0))),
% 1.53/1.73      inference('sup-', [status(thm)], ['73', '74'])).
% 1.53/1.73  thf('76', plain,
% 1.53/1.73      (![X0 : $i]:
% 1.53/1.73         ((v2_struct_0 @ X0)
% 1.53/1.73          | ~ (l1_struct_0 @ X0)
% 1.53/1.73          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 1.53/1.73      inference('simplify', [status(thm)], ['75'])).
% 1.53/1.73  thf('77', plain, ((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 1.53/1.73      inference('sup-', [status(thm)], ['72', '76'])).
% 1.53/1.73  thf('78', plain, ((l1_struct_0 @ sk_A)),
% 1.53/1.73      inference('sup-', [status(thm)], ['62', '63'])).
% 1.53/1.73  thf('79', plain, ((v2_struct_0 @ sk_A)),
% 1.53/1.73      inference('demod', [status(thm)], ['77', '78'])).
% 1.53/1.73  thf('80', plain, ($false), inference('demod', [status(thm)], ['0', '79'])).
% 1.53/1.73  
% 1.53/1.73  % SZS output end Refutation
% 1.53/1.73  
% 1.53/1.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
