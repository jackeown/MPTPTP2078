%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LWvY7JbAZT

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:44 EST 2020

% Result     : Theorem 10.64s
% Output     : Refutation 10.64s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 286 expanded)
%              Number of leaves         :   33 ( 102 expanded)
%              Depth                    :   22
%              Number of atoms          : 2195 (4069 expanded)
%              Number of equality atoms :   75 ( 185 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

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

thf(t2_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ B )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_mcart_1])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X1 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k2_subset_1 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('4',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('5',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

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

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k2_orders_2 @ X15 @ X14 )
        = ( a_2_1_orders_2 @ X15 @ X14 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ X1 )
        = ( a_2_1_orders_2 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('10',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
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

thf('11',plain,(
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

thf('12',plain,(
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
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
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
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
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
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
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
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
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
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('18',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_mcart_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('20',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('21',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('22',plain,(
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

thf('23',plain,(
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
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
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
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
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
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
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
    inference('sup+',[status(thm)],['17','27'])).

thf('29',plain,(
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
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
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
    inference('sup+',[status(thm)],['16','29'])).

thf('31',plain,(
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
    inference(simplify,[status(thm)],['30'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('33',plain,(
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
    inference('sup-',[status(thm)],['31','32'])).

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
      | ( ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
        = ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('35',plain,(
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
    inference('sup-',[status(thm)],['18','26'])).

thf('36',plain,(
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
    inference('sup+',[status(thm)],['34','35'])).

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
      | ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('39',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_mcart_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('41',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('42',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('43',plain,(
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

thf('44',plain,(
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
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
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
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
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
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
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
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
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
    inference('sup-',[status(thm)],['39','47'])).

thf('49',plain,(
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
    inference('sup-',[status(thm)],['38','48'])).

thf('50',plain,(
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
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
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
    inference('sup-',[status(thm)],['37','50'])).

thf('52',plain,(
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
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
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
    inference('sup-',[status(thm)],['33','52'])).

thf('54',plain,(
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
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
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
    inference('sup-',[status(thm)],['1','15'])).

thf('56',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('57',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X7 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_mcart_1])).

thf('58',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('59',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('60',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X15 ) ) )
      | ( ( k2_orders_2 @ X15 @ X14 )
        = ( a_2_1_orders_2 @ X15 @ X14 ) )
      | ~ ( l1_orders_2 @ X15 )
      | ~ ( v5_orders_2 @ X15 )
      | ~ ( v4_orders_2 @ X15 )
      | ~ ( v3_orders_2 @ X15 )
      | ( v2_struct_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('63',plain,(
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

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
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
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf('68',plain,(
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
    inference('sup-',[status(thm)],['57','67'])).

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

thf('69',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r2_orders_2 @ X12 @ X11 @ X13 )
      | ( X11 != X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('70',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( r2_orders_2 @ X12 @ X13 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
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
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
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
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['56','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) )
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
    inference('sup-',[status(thm)],['55','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
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
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','76'])).

thf('78',plain,(
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
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('82',plain,(
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('83',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['80','83','84','85','86','87'])).

thf('89',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('93',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('94',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['91','95'])).

thf('97',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['81','82'])).

thf('98',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,(
    $false ),
    inference(demod,[status(thm)],['0','98'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LWvY7JbAZT
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:42:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 10.64/10.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 10.64/10.82  % Solved by: fo/fo7.sh
% 10.64/10.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.64/10.82  % done 7489 iterations in 10.351s
% 10.64/10.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 10.64/10.82  % SZS output start Refutation
% 10.64/10.82  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 10.64/10.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.64/10.82  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 10.64/10.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.64/10.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.64/10.82  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 10.64/10.82  thf(sk_A_type, type, sk_A: $i).
% 10.64/10.82  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 10.64/10.82  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 10.64/10.82  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 10.64/10.82  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 10.64/10.82  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 10.64/10.82  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 10.64/10.82  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 10.64/10.82  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 10.64/10.82  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 10.64/10.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.64/10.82  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 10.64/10.82  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 10.64/10.82  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 10.64/10.82  thf(sk_B_type, type, sk_B: $i > $i).
% 10.64/10.82  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 10.64/10.82  thf(t46_orders_2, conjecture,
% 10.64/10.82    (![A:$i]:
% 10.64/10.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 10.64/10.82         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 10.64/10.82       ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 10.64/10.82  thf(zf_stmt_0, negated_conjecture,
% 10.64/10.82    (~( ![A:$i]:
% 10.64/10.82        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 10.64/10.82            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 10.64/10.82          ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 10.64/10.82    inference('cnf.neg', [status(esa)], [t46_orders_2])).
% 10.64/10.82  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 10.64/10.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.64/10.82  thf(t2_mcart_1, axiom,
% 10.64/10.82    (![A:$i]:
% 10.64/10.82     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 10.64/10.82          ( ![B:$i]:
% 10.64/10.82            ( ~( ( r2_hidden @ B @ A ) & 
% 10.64/10.82                 ( ![C:$i]:
% 10.64/10.82                   ( ( r2_hidden @ C @ B ) => ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 10.64/10.82  thf('1', plain,
% 10.64/10.82      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 10.64/10.82      inference('cnf', [status(esa)], [t2_mcart_1])).
% 10.64/10.82  thf(dt_k2_subset_1, axiom,
% 10.64/10.82    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 10.64/10.82  thf('2', plain,
% 10.64/10.82      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 10.64/10.82      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 10.64/10.82  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 10.64/10.82  thf('3', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 10.64/10.82      inference('cnf', [status(esa)], [d4_subset_1])).
% 10.64/10.82  thf('4', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 10.64/10.82      inference('demod', [status(thm)], ['2', '3'])).
% 10.64/10.82  thf(d3_struct_0, axiom,
% 10.64/10.82    (![A:$i]:
% 10.64/10.82     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 10.64/10.82  thf('5', plain,
% 10.64/10.82      (![X9 : $i]:
% 10.64/10.82         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 10.64/10.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 10.64/10.82  thf(d13_orders_2, axiom,
% 10.64/10.82    (![A:$i]:
% 10.64/10.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 10.64/10.82         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 10.64/10.82       ( ![B:$i]:
% 10.64/10.82         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 10.64/10.82           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 10.64/10.82  thf('6', plain,
% 10.64/10.82      (![X14 : $i, X15 : $i]:
% 10.64/10.82         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 10.64/10.82          | ((k2_orders_2 @ X15 @ X14) = (a_2_1_orders_2 @ X15 @ X14))
% 10.64/10.82          | ~ (l1_orders_2 @ X15)
% 10.64/10.82          | ~ (v5_orders_2 @ X15)
% 10.64/10.82          | ~ (v4_orders_2 @ X15)
% 10.64/10.82          | ~ (v3_orders_2 @ X15)
% 10.64/10.82          | (v2_struct_0 @ X15))),
% 10.64/10.82      inference('cnf', [status(esa)], [d13_orders_2])).
% 10.64/10.82  thf('7', plain,
% 10.64/10.82      (![X0 : $i, X1 : $i]:
% 10.64/10.82         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ((k2_orders_2 @ X0 @ X1) = (a_2_1_orders_2 @ X0 @ X1)))),
% 10.64/10.82      inference('sup-', [status(thm)], ['5', '6'])).
% 10.64/10.82  thf('8', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 10.64/10.82            = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0))),
% 10.64/10.82      inference('sup-', [status(thm)], ['4', '7'])).
% 10.64/10.82  thf('9', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 10.64/10.82      inference('demod', [status(thm)], ['2', '3'])).
% 10.64/10.82  thf('10', plain,
% 10.64/10.82      (![X9 : $i]:
% 10.64/10.82         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 10.64/10.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 10.64/10.82  thf(fraenkel_a_2_1_orders_2, axiom,
% 10.64/10.82    (![A:$i,B:$i,C:$i]:
% 10.64/10.82     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 10.64/10.82         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 10.64/10.82         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 10.64/10.82       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 10.64/10.82         ( ?[D:$i]:
% 10.64/10.82           ( ( ![E:$i]:
% 10.64/10.82               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 10.64/10.82                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 10.64/10.82             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 10.64/10.82  thf('11', plain,
% 10.64/10.82      (![X17 : $i, X18 : $i, X20 : $i]:
% 10.64/10.82         (~ (l1_orders_2 @ X17)
% 10.64/10.82          | ~ (v5_orders_2 @ X17)
% 10.64/10.82          | ~ (v4_orders_2 @ X17)
% 10.64/10.82          | ~ (v3_orders_2 @ X17)
% 10.64/10.82          | (v2_struct_0 @ X17)
% 10.64/10.82          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 10.64/10.82          | ((X20) = (sk_D @ X18 @ X17 @ X20))
% 10.64/10.82          | ~ (r2_hidden @ X20 @ (a_2_1_orders_2 @ X17 @ X18)))),
% 10.64/10.82      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 10.64/10.82  thf('12', plain,
% 10.64/10.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.64/10.82         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ~ (r2_hidden @ X2 @ (a_2_1_orders_2 @ X0 @ X1))
% 10.64/10.82          | ((X2) = (sk_D @ X1 @ X0 @ X2))
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0))),
% 10.64/10.82      inference('sup-', [status(thm)], ['10', '11'])).
% 10.64/10.82  thf('13', plain,
% 10.64/10.82      (![X0 : $i, X1 : $i]:
% 10.64/10.82         (~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 10.64/10.82          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.64/10.82          | ~ (l1_struct_0 @ X0))),
% 10.64/10.82      inference('sup-', [status(thm)], ['9', '12'])).
% 10.64/10.82  thf('14', plain,
% 10.64/10.82      (![X0 : $i, X1 : $i]:
% 10.64/10.82         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0))),
% 10.64/10.82      inference('sup-', [status(thm)], ['8', '13'])).
% 10.64/10.82  thf('15', plain,
% 10.64/10.82      (![X0 : $i, X1 : $i]:
% 10.64/10.82         (((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 10.64/10.82      inference('simplify', [status(thm)], ['14'])).
% 10.64/10.82  thf('16', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.64/10.82              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 10.64/10.82                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 10.64/10.82      inference('sup-', [status(thm)], ['1', '15'])).
% 10.64/10.82  thf('17', plain,
% 10.64/10.82      (![X9 : $i]:
% 10.64/10.82         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 10.64/10.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 10.64/10.82  thf('18', plain,
% 10.64/10.82      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 10.64/10.82      inference('cnf', [status(esa)], [t2_mcart_1])).
% 10.64/10.82  thf('19', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 10.64/10.82            = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0))),
% 10.64/10.82      inference('sup-', [status(thm)], ['4', '7'])).
% 10.64/10.82  thf('20', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 10.64/10.82      inference('demod', [status(thm)], ['2', '3'])).
% 10.64/10.82  thf('21', plain,
% 10.64/10.82      (![X9 : $i]:
% 10.64/10.82         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 10.64/10.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 10.64/10.82  thf('22', plain,
% 10.64/10.82      (![X17 : $i, X18 : $i, X20 : $i]:
% 10.64/10.82         (~ (l1_orders_2 @ X17)
% 10.64/10.82          | ~ (v5_orders_2 @ X17)
% 10.64/10.82          | ~ (v4_orders_2 @ X17)
% 10.64/10.82          | ~ (v3_orders_2 @ X17)
% 10.64/10.82          | (v2_struct_0 @ X17)
% 10.64/10.82          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 10.64/10.82          | (m1_subset_1 @ (sk_D @ X18 @ X17 @ X20) @ (u1_struct_0 @ X17))
% 10.64/10.82          | ~ (r2_hidden @ X20 @ (a_2_1_orders_2 @ X17 @ X18)))),
% 10.64/10.82      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 10.64/10.82  thf('23', plain,
% 10.64/10.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.64/10.82         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ~ (r2_hidden @ X2 @ (a_2_1_orders_2 @ X0 @ X1))
% 10.64/10.82          | (m1_subset_1 @ (sk_D @ X1 @ X0 @ X2) @ (u1_struct_0 @ X0))
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0))),
% 10.64/10.82      inference('sup-', [status(thm)], ['21', '22'])).
% 10.64/10.82  thf('24', plain,
% 10.64/10.82      (![X0 : $i, X1 : $i]:
% 10.64/10.82         (~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 10.64/10.82             (u1_struct_0 @ X0))
% 10.64/10.82          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.64/10.82          | ~ (l1_struct_0 @ X0))),
% 10.64/10.82      inference('sup-', [status(thm)], ['20', '23'])).
% 10.64/10.82  thf('25', plain,
% 10.64/10.82      (![X0 : $i, X1 : $i]:
% 10.64/10.82         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 10.64/10.82             (u1_struct_0 @ X0))
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0))),
% 10.64/10.82      inference('sup-', [status(thm)], ['19', '24'])).
% 10.64/10.82  thf('26', plain,
% 10.64/10.82      (![X0 : $i, X1 : $i]:
% 10.64/10.82         ((m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 10.64/10.82           (u1_struct_0 @ X0))
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 10.64/10.82      inference('simplify', [status(thm)], ['25'])).
% 10.64/10.82  thf('27', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | (m1_subset_1 @ 
% 10.64/10.82             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 10.64/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.64/10.82             (u1_struct_0 @ X0)))),
% 10.64/10.82      inference('sup-', [status(thm)], ['18', '26'])).
% 10.64/10.82  thf('28', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         ((m1_subset_1 @ 
% 10.64/10.82           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 10.64/10.82            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.64/10.82           (k2_struct_0 @ X0))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 10.64/10.82      inference('sup+', [status(thm)], ['17', '27'])).
% 10.64/10.82  thf('29', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | (m1_subset_1 @ 
% 10.64/10.82             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 10.64/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.64/10.82             (k2_struct_0 @ X0)))),
% 10.64/10.82      inference('simplify', [status(thm)], ['28'])).
% 10.64/10.82  thf('30', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.64/10.82           (k2_struct_0 @ X0))
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 10.64/10.82      inference('sup+', [status(thm)], ['16', '29'])).
% 10.64/10.82  thf('31', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.64/10.82             (k2_struct_0 @ X0)))),
% 10.64/10.82      inference('simplify', [status(thm)], ['30'])).
% 10.64/10.82  thf(t2_subset, axiom,
% 10.64/10.82    (![A:$i,B:$i]:
% 10.64/10.82     ( ( m1_subset_1 @ A @ B ) =>
% 10.64/10.82       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 10.64/10.82  thf('32', plain,
% 10.64/10.82      (![X2 : $i, X3 : $i]:
% 10.64/10.82         ((r2_hidden @ X2 @ X3)
% 10.64/10.82          | (v1_xboole_0 @ X3)
% 10.64/10.82          | ~ (m1_subset_1 @ X2 @ X3))),
% 10.64/10.82      inference('cnf', [status(esa)], [t2_subset])).
% 10.64/10.82  thf('33', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 10.64/10.82          | (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.64/10.82             (k2_struct_0 @ X0)))),
% 10.64/10.82      inference('sup-', [status(thm)], ['31', '32'])).
% 10.64/10.82  thf('34', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.64/10.82              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 10.64/10.82                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 10.64/10.82      inference('sup-', [status(thm)], ['1', '15'])).
% 10.64/10.82  thf('35', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | (m1_subset_1 @ 
% 10.64/10.82             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 10.64/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.64/10.82             (u1_struct_0 @ X0)))),
% 10.64/10.82      inference('sup-', [status(thm)], ['18', '26'])).
% 10.64/10.82  thf('36', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.64/10.82           (u1_struct_0 @ X0))
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 10.64/10.82      inference('sup+', [status(thm)], ['34', '35'])).
% 10.64/10.82  thf('37', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.64/10.82             (u1_struct_0 @ X0)))),
% 10.64/10.82      inference('simplify', [status(thm)], ['36'])).
% 10.64/10.82  thf('38', plain,
% 10.64/10.82      (![X9 : $i]:
% 10.64/10.82         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 10.64/10.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 10.64/10.82  thf('39', plain,
% 10.64/10.82      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 10.64/10.82      inference('cnf', [status(esa)], [t2_mcart_1])).
% 10.64/10.82  thf('40', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 10.64/10.82            = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0))),
% 10.64/10.82      inference('sup-', [status(thm)], ['4', '7'])).
% 10.64/10.82  thf('41', plain,
% 10.64/10.82      (![X9 : $i]:
% 10.64/10.82         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 10.64/10.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 10.64/10.82  thf('42', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 10.64/10.82      inference('demod', [status(thm)], ['2', '3'])).
% 10.64/10.82  thf('43', plain,
% 10.64/10.82      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 10.64/10.82         (~ (l1_orders_2 @ X17)
% 10.64/10.82          | ~ (v5_orders_2 @ X17)
% 10.64/10.82          | ~ (v4_orders_2 @ X17)
% 10.64/10.82          | ~ (v3_orders_2 @ X17)
% 10.64/10.82          | (v2_struct_0 @ X17)
% 10.64/10.82          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 10.64/10.82          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 10.64/10.82          | (r2_orders_2 @ X17 @ (sk_D @ X18 @ X17 @ X20) @ X19)
% 10.64/10.82          | ~ (r2_hidden @ X19 @ X18)
% 10.64/10.82          | ~ (r2_hidden @ X20 @ (a_2_1_orders_2 @ X17 @ X18)))),
% 10.64/10.82      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 10.64/10.82  thf('44', plain,
% 10.64/10.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.64/10.82         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 10.64/10.82          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 10.64/10.82          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 10.64/10.82          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0))),
% 10.64/10.82      inference('sup-', [status(thm)], ['42', '43'])).
% 10.64/10.82  thf('45', plain,
% 10.64/10.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.64/10.82         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.64/10.82          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 10.64/10.82          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0)))),
% 10.64/10.82      inference('sup-', [status(thm)], ['41', '44'])).
% 10.64/10.82  thf('46', plain,
% 10.64/10.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.64/10.82         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 10.64/10.82          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 10.64/10.82          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0))),
% 10.64/10.82      inference('sup-', [status(thm)], ['40', '45'])).
% 10.64/10.82  thf('47', plain,
% 10.64/10.82      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.64/10.82         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 10.64/10.82          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 10.64/10.82          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 10.64/10.82      inference('simplify', [status(thm)], ['46'])).
% 10.64/10.82  thf('48', plain,
% 10.64/10.82      (![X0 : $i, X1 : $i]:
% 10.64/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 10.64/10.82          | (r2_orders_2 @ X0 @ 
% 10.64/10.82             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.64/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.64/10.82             X1)
% 10.64/10.82          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0)))),
% 10.64/10.82      inference('sup-', [status(thm)], ['39', '47'])).
% 10.64/10.82  thf('49', plain,
% 10.64/10.82      (![X0 : $i, X1 : $i]:
% 10.64/10.82         (~ (r2_hidden @ X1 @ (k2_struct_0 @ X0))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 10.64/10.82          | (r2_orders_2 @ X0 @ 
% 10.64/10.82             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.64/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.64/10.82             X1)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 10.64/10.82      inference('sup-', [status(thm)], ['38', '48'])).
% 10.64/10.82  thf('50', plain,
% 10.64/10.82      (![X0 : $i, X1 : $i]:
% 10.64/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | (r2_orders_2 @ X0 @ 
% 10.64/10.82             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.64/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.64/10.82             X1)
% 10.64/10.82          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0)))),
% 10.64/10.82      inference('simplify', [status(thm)], ['49'])).
% 10.64/10.82  thf('51', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.64/10.82               (k2_struct_0 @ X0))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | (r2_orders_2 @ X0 @ 
% 10.64/10.82             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.64/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.64/10.82             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 10.64/10.82      inference('sup-', [status(thm)], ['37', '50'])).
% 10.64/10.82  thf('52', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         ((r2_orders_2 @ X0 @ 
% 10.64/10.82           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.64/10.82            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.64/10.82           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 10.64/10.82          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 10.64/10.82               (k2_struct_0 @ X0))
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0))),
% 10.64/10.82      inference('simplify', [status(thm)], ['51'])).
% 10.64/10.82  thf('53', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | (r2_orders_2 @ X0 @ 
% 10.64/10.82             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.64/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.64/10.82             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 10.64/10.82      inference('sup-', [status(thm)], ['33', '52'])).
% 10.64/10.82  thf('54', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         ((r2_orders_2 @ X0 @ 
% 10.64/10.82           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.64/10.82            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.64/10.82           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 10.64/10.82      inference('simplify', [status(thm)], ['53'])).
% 10.64/10.82  thf('55', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.64/10.82              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 10.64/10.82                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 10.64/10.82      inference('sup-', [status(thm)], ['1', '15'])).
% 10.64/10.82  thf('56', plain,
% 10.64/10.82      (![X9 : $i]:
% 10.64/10.82         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 10.64/10.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 10.64/10.82  thf('57', plain,
% 10.64/10.82      (![X7 : $i]: (((X7) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X7) @ X7))),
% 10.64/10.82      inference('cnf', [status(esa)], [t2_mcart_1])).
% 10.64/10.82  thf('58', plain,
% 10.64/10.82      (![X9 : $i]:
% 10.64/10.82         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 10.64/10.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 10.64/10.82  thf('59', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 10.64/10.82      inference('demod', [status(thm)], ['2', '3'])).
% 10.64/10.82  thf('60', plain,
% 10.64/10.82      (![X14 : $i, X15 : $i]:
% 10.64/10.82         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 10.64/10.82          | ((k2_orders_2 @ X15 @ X14) = (a_2_1_orders_2 @ X15 @ X14))
% 10.64/10.82          | ~ (l1_orders_2 @ X15)
% 10.64/10.82          | ~ (v5_orders_2 @ X15)
% 10.64/10.82          | ~ (v4_orders_2 @ X15)
% 10.64/10.82          | ~ (v3_orders_2 @ X15)
% 10.64/10.82          | (v2_struct_0 @ X15))),
% 10.64/10.82      inference('cnf', [status(esa)], [d13_orders_2])).
% 10.64/10.82  thf('61', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         ((v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 10.64/10.82              = (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 10.64/10.82      inference('sup-', [status(thm)], ['59', '60'])).
% 10.64/10.82  thf('62', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 10.64/10.82      inference('demod', [status(thm)], ['2', '3'])).
% 10.64/10.82  thf('63', plain,
% 10.64/10.82      (![X17 : $i, X18 : $i, X20 : $i]:
% 10.64/10.82         (~ (l1_orders_2 @ X17)
% 10.64/10.82          | ~ (v5_orders_2 @ X17)
% 10.64/10.82          | ~ (v4_orders_2 @ X17)
% 10.64/10.82          | ~ (v3_orders_2 @ X17)
% 10.64/10.82          | (v2_struct_0 @ X17)
% 10.64/10.82          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 10.64/10.82          | (m1_subset_1 @ (sk_D @ X18 @ X17 @ X20) @ (u1_struct_0 @ X17))
% 10.64/10.82          | ~ (r2_hidden @ X20 @ (a_2_1_orders_2 @ X17 @ X18)))),
% 10.64/10.82      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 10.64/10.82  thf('64', plain,
% 10.64/10.82      (![X0 : $i, X1 : $i]:
% 10.64/10.82         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 10.64/10.82          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 10.64/10.82             (u1_struct_0 @ X0))
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0))),
% 10.64/10.82      inference('sup-', [status(thm)], ['62', '63'])).
% 10.64/10.82  thf('65', plain,
% 10.64/10.82      (![X0 : $i, X1 : $i]:
% 10.64/10.82         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 10.64/10.82             (u1_struct_0 @ X0)))),
% 10.64/10.82      inference('sup-', [status(thm)], ['61', '64'])).
% 10.64/10.82  thf('66', plain,
% 10.64/10.82      (![X0 : $i, X1 : $i]:
% 10.64/10.82         ((m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 10.64/10.82           (u1_struct_0 @ X0))
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 10.64/10.82      inference('simplify', [status(thm)], ['65'])).
% 10.64/10.82  thf('67', plain,
% 10.64/10.82      (![X0 : $i, X1 : $i]:
% 10.64/10.82         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 10.64/10.82             (u1_struct_0 @ X0)))),
% 10.64/10.82      inference('sup-', [status(thm)], ['58', '66'])).
% 10.64/10.82  thf('68', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | (m1_subset_1 @ 
% 10.64/10.82             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.64/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.64/10.82             (u1_struct_0 @ X0))
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0))),
% 10.64/10.82      inference('sup-', [status(thm)], ['57', '67'])).
% 10.64/10.82  thf(d10_orders_2, axiom,
% 10.64/10.82    (![A:$i]:
% 10.64/10.82     ( ( l1_orders_2 @ A ) =>
% 10.64/10.82       ( ![B:$i]:
% 10.64/10.82         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 10.64/10.82           ( ![C:$i]:
% 10.64/10.82             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 10.64/10.82               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 10.64/10.82                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 10.64/10.82  thf('69', plain,
% 10.64/10.82      (![X11 : $i, X12 : $i, X13 : $i]:
% 10.64/10.82         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 10.64/10.82          | ~ (r2_orders_2 @ X12 @ X11 @ X13)
% 10.64/10.82          | ((X11) != (X13))
% 10.64/10.82          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 10.64/10.82          | ~ (l1_orders_2 @ X12))),
% 10.64/10.82      inference('cnf', [status(esa)], [d10_orders_2])).
% 10.64/10.82  thf('70', plain,
% 10.64/10.82      (![X12 : $i, X13 : $i]:
% 10.64/10.82         (~ (l1_orders_2 @ X12)
% 10.64/10.82          | ~ (r2_orders_2 @ X12 @ X13 @ X13)
% 10.64/10.82          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12)))),
% 10.64/10.82      inference('simplify', [status(thm)], ['69'])).
% 10.64/10.82  thf('71', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (~ (l1_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | ~ (r2_orders_2 @ X0 @ 
% 10.64/10.82               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.64/10.82                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.64/10.82               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.64/10.82                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 10.64/10.82          | ~ (l1_orders_2 @ X0))),
% 10.64/10.82      inference('sup-', [status(thm)], ['68', '70'])).
% 10.64/10.82  thf('72', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (~ (r2_orders_2 @ X0 @ 
% 10.64/10.82             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.64/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.64/10.82             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.64/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0))),
% 10.64/10.82      inference('simplify', [status(thm)], ['71'])).
% 10.64/10.82  thf('73', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (~ (r2_orders_2 @ X0 @ 
% 10.64/10.82             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.64/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.64/10.82             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 10.64/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 10.64/10.82      inference('sup-', [status(thm)], ['56', '72'])).
% 10.64/10.82  thf('74', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ~ (r2_orders_2 @ X0 @ 
% 10.64/10.82               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.64/10.82                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.64/10.82               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 10.64/10.82                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 10.64/10.82      inference('simplify', [status(thm)], ['73'])).
% 10.64/10.82  thf('75', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (~ (r2_orders_2 @ X0 @ 
% 10.64/10.82             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.64/10.82              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.64/10.82             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 10.64/10.82      inference('sup-', [status(thm)], ['55', '74'])).
% 10.64/10.82  thf('76', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (r2_orders_2 @ X0 @ 
% 10.64/10.82               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 10.64/10.82                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 10.64/10.82               (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 10.64/10.82      inference('simplify', [status(thm)], ['75'])).
% 10.64/10.82  thf('77', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 10.64/10.82      inference('sup-', [status(thm)], ['54', '76'])).
% 10.64/10.82  thf('78', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (~ (l1_orders_2 @ X0)
% 10.64/10.82          | ~ (v5_orders_2 @ X0)
% 10.64/10.82          | ~ (v4_orders_2 @ X0)
% 10.64/10.82          | ~ (v3_orders_2 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 10.64/10.82          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 10.64/10.82      inference('simplify', [status(thm)], ['77'])).
% 10.64/10.82  thf('79', plain,
% 10.64/10.82      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 10.64/10.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.64/10.82  thf('80', plain,
% 10.64/10.82      ((((k1_xboole_0) != (k1_xboole_0))
% 10.64/10.82        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 10.64/10.82        | ~ (l1_struct_0 @ sk_A)
% 10.64/10.82        | (v2_struct_0 @ sk_A)
% 10.64/10.82        | ~ (v3_orders_2 @ sk_A)
% 10.64/10.82        | ~ (v4_orders_2 @ sk_A)
% 10.64/10.82        | ~ (v5_orders_2 @ sk_A)
% 10.64/10.82        | ~ (l1_orders_2 @ sk_A))),
% 10.64/10.82      inference('sup-', [status(thm)], ['78', '79'])).
% 10.64/10.82  thf('81', plain, ((l1_orders_2 @ sk_A)),
% 10.64/10.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.64/10.82  thf(dt_l1_orders_2, axiom,
% 10.64/10.82    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 10.64/10.82  thf('82', plain,
% 10.64/10.82      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_orders_2 @ X16))),
% 10.64/10.82      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 10.64/10.82  thf('83', plain, ((l1_struct_0 @ sk_A)),
% 10.64/10.82      inference('sup-', [status(thm)], ['81', '82'])).
% 10.64/10.82  thf('84', plain, ((v3_orders_2 @ sk_A)),
% 10.64/10.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.64/10.82  thf('85', plain, ((v4_orders_2 @ sk_A)),
% 10.64/10.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.64/10.82  thf('86', plain, ((v5_orders_2 @ sk_A)),
% 10.64/10.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.64/10.82  thf('87', plain, ((l1_orders_2 @ sk_A)),
% 10.64/10.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.64/10.82  thf('88', plain,
% 10.64/10.82      ((((k1_xboole_0) != (k1_xboole_0))
% 10.64/10.82        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 10.64/10.82        | (v2_struct_0 @ sk_A))),
% 10.64/10.82      inference('demod', [status(thm)], ['80', '83', '84', '85', '86', '87'])).
% 10.64/10.82  thf('89', plain,
% 10.64/10.82      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 10.64/10.82      inference('simplify', [status(thm)], ['88'])).
% 10.64/10.82  thf('90', plain, (~ (v2_struct_0 @ sk_A)),
% 10.64/10.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.64/10.82  thf('91', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 10.64/10.82      inference('clc', [status(thm)], ['89', '90'])).
% 10.64/10.82  thf('92', plain,
% 10.64/10.82      (![X9 : $i]:
% 10.64/10.82         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 10.64/10.82      inference('cnf', [status(esa)], [d3_struct_0])).
% 10.64/10.82  thf(fc2_struct_0, axiom,
% 10.64/10.82    (![A:$i]:
% 10.64/10.82     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 10.64/10.82       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 10.64/10.82  thf('93', plain,
% 10.64/10.82      (![X10 : $i]:
% 10.64/10.82         (~ (v1_xboole_0 @ (u1_struct_0 @ X10))
% 10.64/10.82          | ~ (l1_struct_0 @ X10)
% 10.64/10.82          | (v2_struct_0 @ X10))),
% 10.64/10.82      inference('cnf', [status(esa)], [fc2_struct_0])).
% 10.64/10.82  thf('94', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | (v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0))),
% 10.64/10.82      inference('sup-', [status(thm)], ['92', '93'])).
% 10.64/10.82  thf('95', plain,
% 10.64/10.82      (![X0 : $i]:
% 10.64/10.82         ((v2_struct_0 @ X0)
% 10.64/10.82          | ~ (l1_struct_0 @ X0)
% 10.64/10.82          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 10.64/10.82      inference('simplify', [status(thm)], ['94'])).
% 10.64/10.82  thf('96', plain, ((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 10.64/10.82      inference('sup-', [status(thm)], ['91', '95'])).
% 10.64/10.82  thf('97', plain, ((l1_struct_0 @ sk_A)),
% 10.64/10.82      inference('sup-', [status(thm)], ['81', '82'])).
% 10.64/10.82  thf('98', plain, ((v2_struct_0 @ sk_A)),
% 10.64/10.82      inference('demod', [status(thm)], ['96', '97'])).
% 10.64/10.82  thf('99', plain, ($false), inference('demod', [status(thm)], ['0', '98'])).
% 10.64/10.82  
% 10.64/10.82  % SZS output end Refutation
% 10.64/10.82  
% 10.64/10.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
