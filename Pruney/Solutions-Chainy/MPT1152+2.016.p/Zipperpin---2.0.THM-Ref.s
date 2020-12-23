%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ddi1VIU9yR

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:44 EST 2020

% Result     : Theorem 4.21s
% Output     : Refutation 4.21s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 299 expanded)
%              Number of leaves         :   33 ( 105 expanded)
%              Depth                    :   25
%              Number of atoms          : 2304 (4240 expanded)
%              Number of equality atoms :   83 ( 205 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

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

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('3',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
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

thf('14',plain,(
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
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

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
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('25',plain,(
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
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('42',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

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
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('46',plain,(
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
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('59',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
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
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf('69',plain,(
    ! [X9: $i] :
      ( ( ( k2_struct_0 @ X9 )
        = ( u1_struct_0 @ X9 ) )
      | ~ ( l1_struct_0 @ X9 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( u1_struct_0 @ X12 ) )
      | ~ ( r2_orders_2 @ X12 @ X11 @ X13 )
      | ( X11 != X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) )
      | ~ ( l1_orders_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('79',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( l1_orders_2 @ X12 )
      | ~ ( r2_orders_2 @ X12 @ X13 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X12 ) ) ) ),
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
    ! [X16: $i] :
      ( ( l1_struct_0 @ X16 )
      | ~ ( l1_orders_2 @ X16 ) ) ),
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

thf('100',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 )
      | ( v2_struct_0 @ X10 ) ) ),
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
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ddi1VIU9yR
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:09:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 4.21/4.38  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 4.21/4.38  % Solved by: fo/fo7.sh
% 4.21/4.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 4.21/4.38  % done 5591 iterations in 3.914s
% 4.21/4.38  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 4.21/4.38  % SZS output start Refutation
% 4.21/4.38  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 4.21/4.38  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 4.21/4.38  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 4.21/4.38  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 4.21/4.38  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 4.21/4.38  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 4.21/4.38  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 4.21/4.38  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 4.21/4.38  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 4.21/4.38  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 4.21/4.38  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 4.21/4.38  thf(sk_A_type, type, sk_A: $i).
% 4.21/4.38  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 4.21/4.38  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 4.21/4.38  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 4.21/4.38  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 4.21/4.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 4.21/4.38  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 4.21/4.38  thf(sk_B_type, type, sk_B: $i > $i).
% 4.21/4.38  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 4.21/4.38  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 4.21/4.38  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 4.21/4.38  thf(t46_orders_2, conjecture,
% 4.21/4.38    (![A:$i]:
% 4.21/4.38     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 4.21/4.38         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 4.21/4.38       ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 4.21/4.38  thf(zf_stmt_0, negated_conjecture,
% 4.21/4.38    (~( ![A:$i]:
% 4.21/4.38        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 4.21/4.38            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 4.21/4.38          ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 4.21/4.38    inference('cnf.neg', [status(esa)], [t46_orders_2])).
% 4.21/4.38  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 4.21/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.21/4.38  thf(t34_mcart_1, axiom,
% 4.21/4.38    (![A:$i]:
% 4.21/4.38     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 4.21/4.38          ( ![B:$i]:
% 4.21/4.38            ( ~( ( r2_hidden @ B @ A ) & 
% 4.21/4.38                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 4.21/4.38                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 4.21/4.38                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 4.21/4.38  thf('1', plain,
% 4.21/4.38      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 4.21/4.38      inference('cnf', [status(esa)], [t34_mcart_1])).
% 4.21/4.38  thf(d3_struct_0, axiom,
% 4.21/4.38    (![A:$i]:
% 4.21/4.38     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 4.21/4.38  thf('2', plain,
% 4.21/4.38      (![X9 : $i]:
% 4.21/4.38         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 4.21/4.38      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.21/4.38  thf('3', plain,
% 4.21/4.38      (![X9 : $i]:
% 4.21/4.38         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 4.21/4.38      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.21/4.38  thf(dt_k2_subset_1, axiom,
% 4.21/4.38    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 4.21/4.38  thf('4', plain,
% 4.21/4.38      (![X1 : $i]: (m1_subset_1 @ (k2_subset_1 @ X1) @ (k1_zfmisc_1 @ X1))),
% 4.21/4.38      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 4.21/4.38  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 4.21/4.38  thf('5', plain, (![X0 : $i]: ((k2_subset_1 @ X0) = (X0))),
% 4.21/4.38      inference('cnf', [status(esa)], [d4_subset_1])).
% 4.21/4.38  thf('6', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 4.21/4.38      inference('demod', [status(thm)], ['4', '5'])).
% 4.21/4.38  thf(d13_orders_2, axiom,
% 4.21/4.38    (![A:$i]:
% 4.21/4.38     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 4.21/4.38         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 4.21/4.38       ( ![B:$i]:
% 4.21/4.38         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 4.21/4.38           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 4.21/4.38  thf('7', plain,
% 4.21/4.38      (![X14 : $i, X15 : $i]:
% 4.21/4.38         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (u1_struct_0 @ X15)))
% 4.21/4.38          | ((k2_orders_2 @ X15 @ X14) = (a_2_1_orders_2 @ X15 @ X14))
% 4.21/4.38          | ~ (l1_orders_2 @ X15)
% 4.21/4.38          | ~ (v5_orders_2 @ X15)
% 4.21/4.38          | ~ (v4_orders_2 @ X15)
% 4.21/4.38          | ~ (v3_orders_2 @ X15)
% 4.21/4.38          | (v2_struct_0 @ X15))),
% 4.21/4.38      inference('cnf', [status(esa)], [d13_orders_2])).
% 4.21/4.38  thf('8', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         ((v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 4.21/4.38              = (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 4.21/4.38      inference('sup-', [status(thm)], ['6', '7'])).
% 4.21/4.38  thf('9', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 4.21/4.38            = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0))),
% 4.21/4.38      inference('sup+', [status(thm)], ['3', '8'])).
% 4.21/4.38  thf('10', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 4.21/4.38            = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0))),
% 4.21/4.38      inference('sup+', [status(thm)], ['2', '9'])).
% 4.21/4.38  thf('11', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 4.21/4.38              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 4.21/4.38      inference('simplify', [status(thm)], ['10'])).
% 4.21/4.38  thf('12', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 4.21/4.38      inference('demod', [status(thm)], ['4', '5'])).
% 4.21/4.38  thf('13', plain,
% 4.21/4.38      (![X9 : $i]:
% 4.21/4.38         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 4.21/4.38      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.21/4.38  thf(fraenkel_a_2_1_orders_2, axiom,
% 4.21/4.38    (![A:$i,B:$i,C:$i]:
% 4.21/4.38     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 4.21/4.38         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 4.21/4.38         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 4.21/4.38       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 4.21/4.38         ( ?[D:$i]:
% 4.21/4.38           ( ( ![E:$i]:
% 4.21/4.38               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 4.21/4.38                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 4.21/4.38             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 4.21/4.38  thf('14', plain,
% 4.21/4.38      (![X17 : $i, X18 : $i, X20 : $i]:
% 4.21/4.38         (~ (l1_orders_2 @ X17)
% 4.21/4.38          | ~ (v5_orders_2 @ X17)
% 4.21/4.38          | ~ (v4_orders_2 @ X17)
% 4.21/4.38          | ~ (v3_orders_2 @ X17)
% 4.21/4.38          | (v2_struct_0 @ X17)
% 4.21/4.38          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 4.21/4.38          | ((X20) = (sk_D @ X18 @ X17 @ X20))
% 4.21/4.38          | ~ (r2_hidden @ X20 @ (a_2_1_orders_2 @ X17 @ X18)))),
% 4.21/4.38      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 4.21/4.38  thf('15', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.21/4.38         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ~ (r2_hidden @ X2 @ (a_2_1_orders_2 @ X0 @ X1))
% 4.21/4.38          | ((X2) = (sk_D @ X1 @ X0 @ X2))
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0))),
% 4.21/4.38      inference('sup-', [status(thm)], ['13', '14'])).
% 4.21/4.38  thf('16', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i]:
% 4.21/4.38         (~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 4.21/4.38          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.21/4.38          | ~ (l1_struct_0 @ X0))),
% 4.21/4.38      inference('sup-', [status(thm)], ['12', '15'])).
% 4.21/4.38  thf('17', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i]:
% 4.21/4.38         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0))),
% 4.21/4.38      inference('sup-', [status(thm)], ['11', '16'])).
% 4.21/4.38  thf('18', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i]:
% 4.21/4.38         (((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 4.21/4.38      inference('simplify', [status(thm)], ['17'])).
% 4.21/4.38  thf('19', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.21/4.38              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 4.21/4.38                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 4.21/4.38      inference('sup-', [status(thm)], ['1', '18'])).
% 4.21/4.38  thf('20', plain,
% 4.21/4.38      (![X9 : $i]:
% 4.21/4.38         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 4.21/4.38      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.21/4.38  thf('21', plain,
% 4.21/4.38      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 4.21/4.38      inference('cnf', [status(esa)], [t34_mcart_1])).
% 4.21/4.38  thf('22', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 4.21/4.38              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 4.21/4.38      inference('simplify', [status(thm)], ['10'])).
% 4.21/4.38  thf('23', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 4.21/4.38      inference('demod', [status(thm)], ['4', '5'])).
% 4.21/4.38  thf('24', plain,
% 4.21/4.38      (![X9 : $i]:
% 4.21/4.38         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 4.21/4.38      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.21/4.38  thf('25', plain,
% 4.21/4.38      (![X17 : $i, X18 : $i, X20 : $i]:
% 4.21/4.38         (~ (l1_orders_2 @ X17)
% 4.21/4.38          | ~ (v5_orders_2 @ X17)
% 4.21/4.38          | ~ (v4_orders_2 @ X17)
% 4.21/4.38          | ~ (v3_orders_2 @ X17)
% 4.21/4.38          | (v2_struct_0 @ X17)
% 4.21/4.38          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 4.21/4.38          | (m1_subset_1 @ (sk_D @ X18 @ X17 @ X20) @ (u1_struct_0 @ X17))
% 4.21/4.38          | ~ (r2_hidden @ X20 @ (a_2_1_orders_2 @ X17 @ X18)))),
% 4.21/4.38      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 4.21/4.38  thf('26', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.21/4.38         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ~ (r2_hidden @ X2 @ (a_2_1_orders_2 @ X0 @ X1))
% 4.21/4.38          | (m1_subset_1 @ (sk_D @ X1 @ X0 @ X2) @ (u1_struct_0 @ X0))
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0))),
% 4.21/4.38      inference('sup-', [status(thm)], ['24', '25'])).
% 4.21/4.38  thf('27', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i]:
% 4.21/4.38         (~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 4.21/4.38             (u1_struct_0 @ X0))
% 4.21/4.38          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.21/4.38          | ~ (l1_struct_0 @ X0))),
% 4.21/4.38      inference('sup-', [status(thm)], ['23', '26'])).
% 4.21/4.38  thf('28', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i]:
% 4.21/4.38         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 4.21/4.38             (u1_struct_0 @ X0))
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0))),
% 4.21/4.38      inference('sup-', [status(thm)], ['22', '27'])).
% 4.21/4.38  thf('29', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i]:
% 4.21/4.38         ((m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 4.21/4.38           (u1_struct_0 @ X0))
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 4.21/4.38      inference('simplify', [status(thm)], ['28'])).
% 4.21/4.38  thf('30', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | (m1_subset_1 @ 
% 4.21/4.38             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 4.21/4.38              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.21/4.38             (u1_struct_0 @ X0)))),
% 4.21/4.38      inference('sup-', [status(thm)], ['21', '29'])).
% 4.21/4.38  thf('31', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         ((m1_subset_1 @ 
% 4.21/4.38           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 4.21/4.38            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.21/4.38           (k2_struct_0 @ X0))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 4.21/4.38      inference('sup+', [status(thm)], ['20', '30'])).
% 4.21/4.38  thf('32', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | (m1_subset_1 @ 
% 4.21/4.38             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 4.21/4.38              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.21/4.38             (k2_struct_0 @ X0)))),
% 4.21/4.38      inference('simplify', [status(thm)], ['31'])).
% 4.21/4.38  thf('33', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 4.21/4.38           (k2_struct_0 @ X0))
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 4.21/4.38      inference('sup+', [status(thm)], ['19', '32'])).
% 4.21/4.38  thf('34', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 4.21/4.38             (k2_struct_0 @ X0)))),
% 4.21/4.38      inference('simplify', [status(thm)], ['33'])).
% 4.21/4.38  thf(t2_subset, axiom,
% 4.21/4.38    (![A:$i,B:$i]:
% 4.21/4.38     ( ( m1_subset_1 @ A @ B ) =>
% 4.21/4.38       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 4.21/4.38  thf('35', plain,
% 4.21/4.38      (![X2 : $i, X3 : $i]:
% 4.21/4.38         ((r2_hidden @ X2 @ X3)
% 4.21/4.38          | (v1_xboole_0 @ X3)
% 4.21/4.38          | ~ (m1_subset_1 @ X2 @ X3))),
% 4.21/4.38      inference('cnf', [status(esa)], [t2_subset])).
% 4.21/4.38  thf('36', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 4.21/4.38          | (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 4.21/4.38             (k2_struct_0 @ X0)))),
% 4.21/4.38      inference('sup-', [status(thm)], ['34', '35'])).
% 4.21/4.38  thf('37', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.21/4.38              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 4.21/4.38                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 4.21/4.38      inference('sup-', [status(thm)], ['1', '18'])).
% 4.21/4.38  thf('38', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | (m1_subset_1 @ 
% 4.21/4.38             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 4.21/4.38              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.21/4.38             (u1_struct_0 @ X0)))),
% 4.21/4.38      inference('sup-', [status(thm)], ['21', '29'])).
% 4.21/4.38  thf('39', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 4.21/4.38           (u1_struct_0 @ X0))
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 4.21/4.38      inference('sup+', [status(thm)], ['37', '38'])).
% 4.21/4.38  thf('40', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 4.21/4.38             (u1_struct_0 @ X0)))),
% 4.21/4.38      inference('simplify', [status(thm)], ['39'])).
% 4.21/4.38  thf('41', plain,
% 4.21/4.38      (![X9 : $i]:
% 4.21/4.38         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 4.21/4.38      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.21/4.38  thf('42', plain,
% 4.21/4.38      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 4.21/4.38      inference('cnf', [status(esa)], [t34_mcart_1])).
% 4.21/4.38  thf('43', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 4.21/4.38              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 4.21/4.38      inference('simplify', [status(thm)], ['10'])).
% 4.21/4.38  thf('44', plain,
% 4.21/4.38      (![X9 : $i]:
% 4.21/4.38         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 4.21/4.38      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.21/4.38  thf('45', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 4.21/4.38      inference('demod', [status(thm)], ['4', '5'])).
% 4.21/4.38  thf('46', plain,
% 4.21/4.38      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 4.21/4.38         (~ (l1_orders_2 @ X17)
% 4.21/4.38          | ~ (v5_orders_2 @ X17)
% 4.21/4.38          | ~ (v4_orders_2 @ X17)
% 4.21/4.38          | ~ (v3_orders_2 @ X17)
% 4.21/4.38          | (v2_struct_0 @ X17)
% 4.21/4.38          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 4.21/4.38          | ~ (m1_subset_1 @ X19 @ (u1_struct_0 @ X17))
% 4.21/4.38          | (r2_orders_2 @ X17 @ (sk_D @ X18 @ X17 @ X20) @ X19)
% 4.21/4.38          | ~ (r2_hidden @ X19 @ X18)
% 4.21/4.38          | ~ (r2_hidden @ X20 @ (a_2_1_orders_2 @ X17 @ X18)))),
% 4.21/4.38      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 4.21/4.38  thf('47', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.21/4.38         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 4.21/4.38          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 4.21/4.38          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 4.21/4.38          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0))),
% 4.21/4.38      inference('sup-', [status(thm)], ['45', '46'])).
% 4.21/4.38  thf('48', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.21/4.38         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.21/4.38          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 4.21/4.38          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0)))),
% 4.21/4.38      inference('sup-', [status(thm)], ['44', '47'])).
% 4.21/4.38  thf('49', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.21/4.38         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 4.21/4.38          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 4.21/4.38          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0))),
% 4.21/4.38      inference('sup-', [status(thm)], ['43', '48'])).
% 4.21/4.38  thf('50', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 4.21/4.38         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 4.21/4.38          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 4.21/4.38          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 4.21/4.38      inference('simplify', [status(thm)], ['49'])).
% 4.21/4.38  thf('51', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i]:
% 4.21/4.38         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 4.21/4.38          | (r2_orders_2 @ X0 @ 
% 4.21/4.38             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.21/4.38              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.21/4.38             X1)
% 4.21/4.38          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0)))),
% 4.21/4.38      inference('sup-', [status(thm)], ['42', '50'])).
% 4.21/4.38  thf('52', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i]:
% 4.21/4.38         (~ (r2_hidden @ X1 @ (k2_struct_0 @ X0))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 4.21/4.38          | (r2_orders_2 @ X0 @ 
% 4.21/4.38             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.21/4.38              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.21/4.38             X1)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 4.21/4.38      inference('sup-', [status(thm)], ['41', '51'])).
% 4.21/4.38  thf('53', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i]:
% 4.21/4.38         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | (r2_orders_2 @ X0 @ 
% 4.21/4.38             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.21/4.38              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.21/4.38             X1)
% 4.21/4.38          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0)))),
% 4.21/4.38      inference('simplify', [status(thm)], ['52'])).
% 4.21/4.38  thf('54', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 4.21/4.38               (k2_struct_0 @ X0))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | (r2_orders_2 @ X0 @ 
% 4.21/4.38             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.21/4.38              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.21/4.38             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 4.21/4.38      inference('sup-', [status(thm)], ['40', '53'])).
% 4.21/4.38  thf('55', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         ((r2_orders_2 @ X0 @ 
% 4.21/4.38           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.21/4.38            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.21/4.38           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 4.21/4.38          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 4.21/4.38               (k2_struct_0 @ X0))
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0))),
% 4.21/4.38      inference('simplify', [status(thm)], ['54'])).
% 4.21/4.38  thf('56', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | (r2_orders_2 @ X0 @ 
% 4.21/4.38             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.21/4.38              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.21/4.38             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 4.21/4.38      inference('sup-', [status(thm)], ['36', '55'])).
% 4.21/4.38  thf('57', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         ((r2_orders_2 @ X0 @ 
% 4.21/4.38           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.21/4.38            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.21/4.38           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 4.21/4.38      inference('simplify', [status(thm)], ['56'])).
% 4.21/4.38  thf('58', plain,
% 4.21/4.38      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 4.21/4.38      inference('cnf', [status(esa)], [t34_mcart_1])).
% 4.21/4.38  thf('59', plain,
% 4.21/4.38      (![X9 : $i]:
% 4.21/4.38         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 4.21/4.38      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.21/4.38  thf('60', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         ((v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 4.21/4.38              = (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 4.21/4.38      inference('sup-', [status(thm)], ['6', '7'])).
% 4.21/4.38  thf('61', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 4.21/4.38      inference('demod', [status(thm)], ['4', '5'])).
% 4.21/4.38  thf('62', plain,
% 4.21/4.38      (![X17 : $i, X18 : $i, X20 : $i]:
% 4.21/4.38         (~ (l1_orders_2 @ X17)
% 4.21/4.38          | ~ (v5_orders_2 @ X17)
% 4.21/4.38          | ~ (v4_orders_2 @ X17)
% 4.21/4.38          | ~ (v3_orders_2 @ X17)
% 4.21/4.38          | (v2_struct_0 @ X17)
% 4.21/4.38          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 4.21/4.38          | ((X20) = (sk_D @ X18 @ X17 @ X20))
% 4.21/4.38          | ~ (r2_hidden @ X20 @ (a_2_1_orders_2 @ X17 @ X18)))),
% 4.21/4.38      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 4.21/4.38  thf('63', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i]:
% 4.21/4.38         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 4.21/4.38          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0))),
% 4.21/4.38      inference('sup-', [status(thm)], ['61', '62'])).
% 4.21/4.38  thf('64', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i]:
% 4.21/4.38         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1)))),
% 4.21/4.38      inference('sup-', [status(thm)], ['60', '63'])).
% 4.21/4.38  thf('65', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i]:
% 4.21/4.38         (((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1))
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 4.21/4.38      inference('simplify', [status(thm)], ['64'])).
% 4.21/4.38  thf('66', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i]:
% 4.21/4.38         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ((X1) = (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1)))),
% 4.21/4.38      inference('sup-', [status(thm)], ['59', '65'])).
% 4.21/4.38  thf('67', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.21/4.38              = (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.21/4.38                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0))),
% 4.21/4.38      inference('sup-', [status(thm)], ['58', '66'])).
% 4.21/4.38  thf('68', plain,
% 4.21/4.38      (![X4 : $i]: (((X4) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X4) @ X4))),
% 4.21/4.38      inference('cnf', [status(esa)], [t34_mcart_1])).
% 4.21/4.38  thf('69', plain,
% 4.21/4.38      (![X9 : $i]:
% 4.21/4.38         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 4.21/4.38      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.21/4.38  thf('70', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         ((v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 4.21/4.38              = (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 4.21/4.38      inference('sup-', [status(thm)], ['6', '7'])).
% 4.21/4.38  thf('71', plain, (![X1 : $i]: (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X1))),
% 4.21/4.38      inference('demod', [status(thm)], ['4', '5'])).
% 4.21/4.38  thf('72', plain,
% 4.21/4.38      (![X17 : $i, X18 : $i, X20 : $i]:
% 4.21/4.38         (~ (l1_orders_2 @ X17)
% 4.21/4.38          | ~ (v5_orders_2 @ X17)
% 4.21/4.38          | ~ (v4_orders_2 @ X17)
% 4.21/4.38          | ~ (v3_orders_2 @ X17)
% 4.21/4.38          | (v2_struct_0 @ X17)
% 4.21/4.38          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 4.21/4.38          | (m1_subset_1 @ (sk_D @ X18 @ X17 @ X20) @ (u1_struct_0 @ X17))
% 4.21/4.38          | ~ (r2_hidden @ X20 @ (a_2_1_orders_2 @ X17 @ X18)))),
% 4.21/4.38      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 4.21/4.38  thf('73', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i]:
% 4.21/4.38         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 4.21/4.38          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 4.21/4.38             (u1_struct_0 @ X0))
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0))),
% 4.21/4.38      inference('sup-', [status(thm)], ['71', '72'])).
% 4.21/4.38  thf('74', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i]:
% 4.21/4.38         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 4.21/4.38             (u1_struct_0 @ X0)))),
% 4.21/4.38      inference('sup-', [status(thm)], ['70', '73'])).
% 4.21/4.38  thf('75', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i]:
% 4.21/4.38         ((m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 4.21/4.38           (u1_struct_0 @ X0))
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 4.21/4.38      inference('simplify', [status(thm)], ['74'])).
% 4.21/4.38  thf('76', plain,
% 4.21/4.38      (![X0 : $i, X1 : $i]:
% 4.21/4.38         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 4.21/4.38             (u1_struct_0 @ X0)))),
% 4.21/4.38      inference('sup-', [status(thm)], ['69', '75'])).
% 4.21/4.38  thf('77', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | (m1_subset_1 @ 
% 4.21/4.38             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.21/4.38              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.21/4.38             (u1_struct_0 @ X0))
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0))),
% 4.21/4.38      inference('sup-', [status(thm)], ['68', '76'])).
% 4.21/4.38  thf(d10_orders_2, axiom,
% 4.21/4.38    (![A:$i]:
% 4.21/4.38     ( ( l1_orders_2 @ A ) =>
% 4.21/4.38       ( ![B:$i]:
% 4.21/4.38         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 4.21/4.38           ( ![C:$i]:
% 4.21/4.38             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 4.21/4.38               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 4.21/4.38                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 4.21/4.38  thf('78', plain,
% 4.21/4.38      (![X11 : $i, X12 : $i, X13 : $i]:
% 4.21/4.38         (~ (m1_subset_1 @ X11 @ (u1_struct_0 @ X12))
% 4.21/4.38          | ~ (r2_orders_2 @ X12 @ X11 @ X13)
% 4.21/4.38          | ((X11) != (X13))
% 4.21/4.38          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12))
% 4.21/4.38          | ~ (l1_orders_2 @ X12))),
% 4.21/4.38      inference('cnf', [status(esa)], [d10_orders_2])).
% 4.21/4.38  thf('79', plain,
% 4.21/4.38      (![X12 : $i, X13 : $i]:
% 4.21/4.38         (~ (l1_orders_2 @ X12)
% 4.21/4.38          | ~ (r2_orders_2 @ X12 @ X13 @ X13)
% 4.21/4.38          | ~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X12)))),
% 4.21/4.38      inference('simplify', [status(thm)], ['78'])).
% 4.21/4.38  thf('80', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (~ (l1_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | ~ (r2_orders_2 @ X0 @ 
% 4.21/4.38               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.21/4.38                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.21/4.38               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.21/4.38                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 4.21/4.38          | ~ (l1_orders_2 @ X0))),
% 4.21/4.38      inference('sup-', [status(thm)], ['77', '79'])).
% 4.21/4.38  thf('81', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (~ (r2_orders_2 @ X0 @ 
% 4.21/4.38             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.21/4.38              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.21/4.38             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.21/4.38              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0))),
% 4.21/4.38      inference('simplify', [status(thm)], ['80'])).
% 4.21/4.38  thf('82', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (~ (r2_orders_2 @ X0 @ 
% 4.21/4.38             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.21/4.38              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.21/4.38             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 4.21/4.38      inference('sup-', [status(thm)], ['67', '81'])).
% 4.21/4.38  thf('83', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ~ (r2_orders_2 @ X0 @ 
% 4.21/4.38               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 4.21/4.38                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 4.21/4.38               (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 4.21/4.38      inference('simplify', [status(thm)], ['82'])).
% 4.21/4.38  thf('84', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 4.21/4.38      inference('sup-', [status(thm)], ['57', '83'])).
% 4.21/4.38  thf('85', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (~ (l1_orders_2 @ X0)
% 4.21/4.38          | ~ (v5_orders_2 @ X0)
% 4.21/4.38          | ~ (v4_orders_2 @ X0)
% 4.21/4.38          | ~ (v3_orders_2 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 4.21/4.38          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 4.21/4.38      inference('simplify', [status(thm)], ['84'])).
% 4.21/4.38  thf('86', plain,
% 4.21/4.38      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 4.21/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.21/4.38  thf('87', plain,
% 4.21/4.38      ((((k1_xboole_0) != (k1_xboole_0))
% 4.21/4.38        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 4.21/4.38        | ~ (l1_struct_0 @ sk_A)
% 4.21/4.38        | (v2_struct_0 @ sk_A)
% 4.21/4.38        | ~ (v3_orders_2 @ sk_A)
% 4.21/4.38        | ~ (v4_orders_2 @ sk_A)
% 4.21/4.38        | ~ (v5_orders_2 @ sk_A)
% 4.21/4.38        | ~ (l1_orders_2 @ sk_A))),
% 4.21/4.38      inference('sup-', [status(thm)], ['85', '86'])).
% 4.21/4.38  thf('88', plain, ((l1_orders_2 @ sk_A)),
% 4.21/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.21/4.38  thf(dt_l1_orders_2, axiom,
% 4.21/4.38    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 4.21/4.38  thf('89', plain,
% 4.21/4.38      (![X16 : $i]: ((l1_struct_0 @ X16) | ~ (l1_orders_2 @ X16))),
% 4.21/4.38      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 4.21/4.38  thf('90', plain, ((l1_struct_0 @ sk_A)),
% 4.21/4.38      inference('sup-', [status(thm)], ['88', '89'])).
% 4.21/4.38  thf('91', plain, ((v3_orders_2 @ sk_A)),
% 4.21/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.21/4.38  thf('92', plain, ((v4_orders_2 @ sk_A)),
% 4.21/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.21/4.38  thf('93', plain, ((v5_orders_2 @ sk_A)),
% 4.21/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.21/4.38  thf('94', plain, ((l1_orders_2 @ sk_A)),
% 4.21/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.21/4.38  thf('95', plain,
% 4.21/4.38      ((((k1_xboole_0) != (k1_xboole_0))
% 4.21/4.38        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 4.21/4.38        | (v2_struct_0 @ sk_A))),
% 4.21/4.38      inference('demod', [status(thm)], ['87', '90', '91', '92', '93', '94'])).
% 4.21/4.38  thf('96', plain,
% 4.21/4.38      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 4.21/4.38      inference('simplify', [status(thm)], ['95'])).
% 4.21/4.38  thf('97', plain, (~ (v2_struct_0 @ sk_A)),
% 4.21/4.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 4.21/4.38  thf('98', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 4.21/4.38      inference('clc', [status(thm)], ['96', '97'])).
% 4.21/4.38  thf('99', plain,
% 4.21/4.38      (![X9 : $i]:
% 4.21/4.38         (((k2_struct_0 @ X9) = (u1_struct_0 @ X9)) | ~ (l1_struct_0 @ X9))),
% 4.21/4.38      inference('cnf', [status(esa)], [d3_struct_0])).
% 4.21/4.38  thf(fc2_struct_0, axiom,
% 4.21/4.38    (![A:$i]:
% 4.21/4.38     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 4.21/4.38       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 4.21/4.38  thf('100', plain,
% 4.21/4.38      (![X10 : $i]:
% 4.21/4.38         (~ (v1_xboole_0 @ (u1_struct_0 @ X10))
% 4.21/4.38          | ~ (l1_struct_0 @ X10)
% 4.21/4.38          | (v2_struct_0 @ X10))),
% 4.21/4.38      inference('cnf', [status(esa)], [fc2_struct_0])).
% 4.21/4.38  thf('101', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | (v2_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0))),
% 4.21/4.38      inference('sup-', [status(thm)], ['99', '100'])).
% 4.21/4.38  thf('102', plain,
% 4.21/4.38      (![X0 : $i]:
% 4.21/4.38         ((v2_struct_0 @ X0)
% 4.21/4.38          | ~ (l1_struct_0 @ X0)
% 4.21/4.38          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 4.21/4.38      inference('simplify', [status(thm)], ['101'])).
% 4.21/4.38  thf('103', plain, ((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 4.21/4.38      inference('sup-', [status(thm)], ['98', '102'])).
% 4.21/4.38  thf('104', plain, ((l1_struct_0 @ sk_A)),
% 4.21/4.38      inference('sup-', [status(thm)], ['88', '89'])).
% 4.21/4.38  thf('105', plain, ((v2_struct_0 @ sk_A)),
% 4.21/4.38      inference('demod', [status(thm)], ['103', '104'])).
% 4.21/4.38  thf('106', plain, ($false), inference('demod', [status(thm)], ['0', '105'])).
% 4.21/4.38  
% 4.21/4.38  % SZS output end Refutation
% 4.21/4.38  
% 4.21/4.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
