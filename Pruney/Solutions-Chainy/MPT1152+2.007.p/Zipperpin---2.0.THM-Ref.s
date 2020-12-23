%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LJrA73EpAH

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:43 EST 2020

% Result     : Theorem 57.11s
% Output     : Refutation 57.11s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 343 expanded)
%              Number of leaves         :   34 ( 117 expanded)
%              Depth                    :   24
%              Number of atoms          : 2231 (4657 expanded)
%              Number of equality atoms :   74 ( 164 expanded)
%              Maximal formula depth    :   23 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

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

thf('1',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

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
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('8',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
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

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k2_orders_2 @ X22 @ X21 )
        = ( a_2_1_orders_2 @ X22 @ X21 ) )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('10',plain,(
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
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('13',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
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
    ! [X24: $i,X25: $i,X27: $i] :
      ( ~ ( l1_orders_2 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( X27
        = ( sk_D @ X25 @ X24 @ X27 ) )
      | ~ ( r2_hidden @ X27 @ ( a_2_1_orders_2 @ X24 @ X25 ) ) ) ),
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
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('21',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('23',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('24',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('25',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ~ ( l1_orders_2 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X25 @ X24 @ X27 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( r2_hidden @ X27 @ ( a_2_1_orders_2 @ X24 @ X25 ) ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
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
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('42',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('44',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('46',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( l1_orders_2 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X24 ) )
      | ( r2_orders_2 @ X24 @ ( sk_D @ X25 @ X24 @ X27 ) @ X26 )
      | ~ ( r2_hidden @ X26 @ X25 )
      | ~ ( r2_hidden @ X27 @ ( a_2_1_orders_2 @ X24 @ X25 ) ) ) ),
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

thf('59',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('60',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X12 ) @ X12 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('61',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('63',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( ( k2_orders_2 @ X22 @ X21 )
        = ( a_2_1_orders_2 @ X22 @ X21 ) )
      | ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('66',plain,(
    ! [X24: $i,X25: $i,X27: $i] :
      ( ~ ( l1_orders_2 @ X24 )
      | ~ ( v5_orders_2 @ X24 )
      | ~ ( v4_orders_2 @ X24 )
      | ~ ( v3_orders_2 @ X24 )
      | ( v2_struct_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X25 @ X24 @ X27 ) @ ( u1_struct_0 @ X24 ) )
      | ~ ( r2_hidden @ X27 @ ( a_2_1_orders_2 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
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
    inference('sup-',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ ( sk_D @ ( u1_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['61','69'])).

thf('71',plain,(
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
    inference('sup-',[status(thm)],['60','70'])).

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

thf('72',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( u1_struct_0 @ X19 ) )
      | ~ ( r2_orders_2 @ X19 @ X18 @ X20 )
      | ( X18 != X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('73',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ~ ( r2_orders_2 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( u1_struct_0 @ X19 ) ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
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
    inference('sup-',[status(thm)],['71','73'])).

thf('75',plain,(
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
    inference(simplify,[status(thm)],['74'])).

thf('76',plain,(
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
    inference('sup-',[status(thm)],['59','75'])).

thf('77',plain,(
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
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
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
    inference('sup-',[status(thm)],['58','77'])).

thf('79',plain,(
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
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
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
    inference('sup-',[status(thm)],['57','79'])).

thf('81',plain,(
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
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('85',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_orders_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('86',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['83','86','87','88','89','90'])).

thf('92',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X16: $i] :
      ( ( ( k2_struct_0 @ X16 )
        = ( u1_struct_0 @ X16 ) )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('96',plain,(
    ! [X17: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X17 ) )
      | ~ ( l1_struct_0 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['94','98'])).

thf('100',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['84','85'])).

thf('101',plain,(
    v2_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,(
    $false ),
    inference(demod,[status(thm)],['0','101'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LJrA73EpAH
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:38:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 57.11/57.31  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 57.11/57.31  % Solved by: fo/fo7.sh
% 57.11/57.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 57.11/57.31  % done 13662 iterations in 56.840s
% 57.11/57.31  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 57.11/57.31  % SZS output start Refutation
% 57.11/57.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 57.11/57.31  thf(sk_B_type, type, sk_B: $i > $i).
% 57.11/57.31  thf(sk_A_type, type, sk_A: $i).
% 57.11/57.31  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 57.11/57.31  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 57.11/57.31  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 57.11/57.31  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 57.11/57.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 57.11/57.31  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 57.11/57.31  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 57.11/57.31  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 57.11/57.31  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 57.11/57.31  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 57.11/57.31  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 57.11/57.31  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 57.11/57.31  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 57.11/57.31  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 57.11/57.31  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 57.11/57.31  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 57.11/57.31  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 57.11/57.31  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 57.11/57.31  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 57.11/57.31  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 57.11/57.31  thf(t46_orders_2, conjecture,
% 57.11/57.31    (![A:$i]:
% 57.11/57.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 57.11/57.31         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 57.11/57.31       ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 57.11/57.31  thf(zf_stmt_0, negated_conjecture,
% 57.11/57.31    (~( ![A:$i]:
% 57.11/57.31        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 57.11/57.31            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 57.11/57.31          ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 57.11/57.31    inference('cnf.neg', [status(esa)], [t46_orders_2])).
% 57.11/57.31  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 57.11/57.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.11/57.31  thf(t29_mcart_1, axiom,
% 57.11/57.31    (![A:$i]:
% 57.11/57.31     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 57.11/57.31          ( ![B:$i]:
% 57.11/57.31            ( ~( ( r2_hidden @ B @ A ) & 
% 57.11/57.31                 ( ![C:$i,D:$i,E:$i]:
% 57.11/57.31                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 57.11/57.31                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 57.11/57.31  thf('1', plain,
% 57.11/57.31      (![X12 : $i]:
% 57.11/57.31         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 57.11/57.31      inference('cnf', [status(esa)], [t29_mcart_1])).
% 57.11/57.31  thf(d3_tarski, axiom,
% 57.11/57.31    (![A:$i,B:$i]:
% 57.11/57.31     ( ( r1_tarski @ A @ B ) <=>
% 57.11/57.31       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 57.11/57.31  thf('2', plain,
% 57.11/57.31      (![X1 : $i, X3 : $i]:
% 57.11/57.31         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 57.11/57.31      inference('cnf', [status(esa)], [d3_tarski])).
% 57.11/57.31  thf('3', plain,
% 57.11/57.31      (![X1 : $i, X3 : $i]:
% 57.11/57.31         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 57.11/57.31      inference('cnf', [status(esa)], [d3_tarski])).
% 57.11/57.31  thf('4', plain,
% 57.11/57.31      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['2', '3'])).
% 57.11/57.31  thf('5', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 57.11/57.31      inference('simplify', [status(thm)], ['4'])).
% 57.11/57.31  thf(t3_subset, axiom,
% 57.11/57.31    (![A:$i,B:$i]:
% 57.11/57.31     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 57.11/57.31  thf('6', plain,
% 57.11/57.31      (![X6 : $i, X8 : $i]:
% 57.11/57.31         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 57.11/57.31      inference('cnf', [status(esa)], [t3_subset])).
% 57.11/57.31  thf('7', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['5', '6'])).
% 57.11/57.31  thf(d3_struct_0, axiom,
% 57.11/57.31    (![A:$i]:
% 57.11/57.31     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 57.11/57.31  thf('8', plain,
% 57.11/57.31      (![X16 : $i]:
% 57.11/57.31         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 57.11/57.31      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.11/57.31  thf(d13_orders_2, axiom,
% 57.11/57.31    (![A:$i]:
% 57.11/57.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 57.11/57.31         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 57.11/57.31       ( ![B:$i]:
% 57.11/57.31         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 57.11/57.31           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 57.11/57.31  thf('9', plain,
% 57.11/57.31      (![X21 : $i, X22 : $i]:
% 57.11/57.31         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 57.11/57.31          | ((k2_orders_2 @ X22 @ X21) = (a_2_1_orders_2 @ X22 @ X21))
% 57.11/57.31          | ~ (l1_orders_2 @ X22)
% 57.11/57.31          | ~ (v5_orders_2 @ X22)
% 57.11/57.31          | ~ (v4_orders_2 @ X22)
% 57.11/57.31          | ~ (v3_orders_2 @ X22)
% 57.11/57.31          | (v2_struct_0 @ X22))),
% 57.11/57.31      inference('cnf', [status(esa)], [d13_orders_2])).
% 57.11/57.31  thf('10', plain,
% 57.11/57.31      (![X0 : $i, X1 : $i]:
% 57.11/57.31         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ((k2_orders_2 @ X0 @ X1) = (a_2_1_orders_2 @ X0 @ X1)))),
% 57.11/57.31      inference('sup-', [status(thm)], ['8', '9'])).
% 57.11/57.31  thf('11', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 57.11/57.31            = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['7', '10'])).
% 57.11/57.31  thf('12', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['5', '6'])).
% 57.11/57.31  thf('13', plain,
% 57.11/57.31      (![X16 : $i]:
% 57.11/57.31         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 57.11/57.31      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.11/57.31  thf(fraenkel_a_2_1_orders_2, axiom,
% 57.11/57.31    (![A:$i,B:$i,C:$i]:
% 57.11/57.31     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 57.11/57.31         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 57.11/57.31         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 57.11/57.31       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 57.11/57.31         ( ?[D:$i]:
% 57.11/57.31           ( ( ![E:$i]:
% 57.11/57.31               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 57.11/57.31                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 57.11/57.31             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 57.11/57.31  thf('14', plain,
% 57.11/57.31      (![X24 : $i, X25 : $i, X27 : $i]:
% 57.11/57.31         (~ (l1_orders_2 @ X24)
% 57.11/57.31          | ~ (v5_orders_2 @ X24)
% 57.11/57.31          | ~ (v4_orders_2 @ X24)
% 57.11/57.31          | ~ (v3_orders_2 @ X24)
% 57.11/57.31          | (v2_struct_0 @ X24)
% 57.11/57.31          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 57.11/57.31          | ((X27) = (sk_D @ X25 @ X24 @ X27))
% 57.11/57.31          | ~ (r2_hidden @ X27 @ (a_2_1_orders_2 @ X24 @ X25)))),
% 57.11/57.31      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 57.11/57.31  thf('15', plain,
% 57.11/57.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 57.11/57.31         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ~ (r2_hidden @ X2 @ (a_2_1_orders_2 @ X0 @ X1))
% 57.11/57.31          | ((X2) = (sk_D @ X1 @ X0 @ X2))
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['13', '14'])).
% 57.11/57.31  thf('16', plain,
% 57.11/57.31      (![X0 : $i, X1 : $i]:
% 57.11/57.31         (~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 57.11/57.31          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 57.11/57.31          | ~ (l1_struct_0 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['12', '15'])).
% 57.11/57.31  thf('17', plain,
% 57.11/57.31      (![X0 : $i, X1 : $i]:
% 57.11/57.31         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['11', '16'])).
% 57.11/57.31  thf('18', plain,
% 57.11/57.31      (![X0 : $i, X1 : $i]:
% 57.11/57.31         (((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 57.11/57.31      inference('simplify', [status(thm)], ['17'])).
% 57.11/57.31  thf('19', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 57.11/57.31              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 57.11/57.31                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 57.11/57.31      inference('sup-', [status(thm)], ['1', '18'])).
% 57.11/57.31  thf('20', plain,
% 57.11/57.31      (![X16 : $i]:
% 57.11/57.31         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 57.11/57.31      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.11/57.31  thf('21', plain,
% 57.11/57.31      (![X12 : $i]:
% 57.11/57.31         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 57.11/57.31      inference('cnf', [status(esa)], [t29_mcart_1])).
% 57.11/57.31  thf('22', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 57.11/57.31            = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['7', '10'])).
% 57.11/57.31  thf('23', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['5', '6'])).
% 57.11/57.31  thf('24', plain,
% 57.11/57.31      (![X16 : $i]:
% 57.11/57.31         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 57.11/57.31      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.11/57.31  thf('25', plain,
% 57.11/57.31      (![X24 : $i, X25 : $i, X27 : $i]:
% 57.11/57.31         (~ (l1_orders_2 @ X24)
% 57.11/57.31          | ~ (v5_orders_2 @ X24)
% 57.11/57.31          | ~ (v4_orders_2 @ X24)
% 57.11/57.31          | ~ (v3_orders_2 @ X24)
% 57.11/57.31          | (v2_struct_0 @ X24)
% 57.11/57.31          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 57.11/57.31          | (m1_subset_1 @ (sk_D @ X25 @ X24 @ X27) @ (u1_struct_0 @ X24))
% 57.11/57.31          | ~ (r2_hidden @ X27 @ (a_2_1_orders_2 @ X24 @ X25)))),
% 57.11/57.31      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 57.11/57.31  thf('26', plain,
% 57.11/57.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 57.11/57.31         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ~ (r2_hidden @ X2 @ (a_2_1_orders_2 @ X0 @ X1))
% 57.11/57.31          | (m1_subset_1 @ (sk_D @ X1 @ X0 @ X2) @ (u1_struct_0 @ X0))
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['24', '25'])).
% 57.11/57.31  thf('27', plain,
% 57.11/57.31      (![X0 : $i, X1 : $i]:
% 57.11/57.31         (~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 57.11/57.31             (u1_struct_0 @ X0))
% 57.11/57.31          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 57.11/57.31          | ~ (l1_struct_0 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['23', '26'])).
% 57.11/57.31  thf('28', plain,
% 57.11/57.31      (![X0 : $i, X1 : $i]:
% 57.11/57.31         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 57.11/57.31             (u1_struct_0 @ X0))
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['22', '27'])).
% 57.11/57.31  thf('29', plain,
% 57.11/57.31      (![X0 : $i, X1 : $i]:
% 57.11/57.31         ((m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 57.11/57.31           (u1_struct_0 @ X0))
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 57.11/57.31      inference('simplify', [status(thm)], ['28'])).
% 57.11/57.31  thf('30', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | (m1_subset_1 @ 
% 57.11/57.31             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 57.11/57.31              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 57.11/57.31             (u1_struct_0 @ X0)))),
% 57.11/57.31      inference('sup-', [status(thm)], ['21', '29'])).
% 57.11/57.31  thf('31', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         ((m1_subset_1 @ 
% 57.11/57.31           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 57.11/57.31            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 57.11/57.31           (k2_struct_0 @ X0))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 57.11/57.31      inference('sup+', [status(thm)], ['20', '30'])).
% 57.11/57.31  thf('32', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | (m1_subset_1 @ 
% 57.11/57.31             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 57.11/57.31              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 57.11/57.31             (k2_struct_0 @ X0)))),
% 57.11/57.31      inference('simplify', [status(thm)], ['31'])).
% 57.11/57.31  thf('33', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 57.11/57.31           (k2_struct_0 @ X0))
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 57.11/57.31      inference('sup+', [status(thm)], ['19', '32'])).
% 57.11/57.31  thf('34', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 57.11/57.31             (k2_struct_0 @ X0)))),
% 57.11/57.31      inference('simplify', [status(thm)], ['33'])).
% 57.11/57.31  thf(t2_subset, axiom,
% 57.11/57.31    (![A:$i,B:$i]:
% 57.11/57.31     ( ( m1_subset_1 @ A @ B ) =>
% 57.11/57.31       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 57.11/57.31  thf('35', plain,
% 57.11/57.31      (![X4 : $i, X5 : $i]:
% 57.11/57.31         ((r2_hidden @ X4 @ X5)
% 57.11/57.31          | (v1_xboole_0 @ X5)
% 57.11/57.31          | ~ (m1_subset_1 @ X4 @ X5))),
% 57.11/57.31      inference('cnf', [status(esa)], [t2_subset])).
% 57.11/57.31  thf('36', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 57.11/57.31          | (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 57.11/57.31             (k2_struct_0 @ X0)))),
% 57.11/57.31      inference('sup-', [status(thm)], ['34', '35'])).
% 57.11/57.31  thf('37', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 57.11/57.31              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 57.11/57.31                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 57.11/57.31      inference('sup-', [status(thm)], ['1', '18'])).
% 57.11/57.31  thf('38', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | (m1_subset_1 @ 
% 57.11/57.31             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 57.11/57.31              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 57.11/57.31             (u1_struct_0 @ X0)))),
% 57.11/57.31      inference('sup-', [status(thm)], ['21', '29'])).
% 57.11/57.31  thf('39', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         ((m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 57.11/57.31           (u1_struct_0 @ X0))
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 57.11/57.31      inference('sup+', [status(thm)], ['37', '38'])).
% 57.11/57.31  thf('40', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 57.11/57.31             (u1_struct_0 @ X0)))),
% 57.11/57.31      inference('simplify', [status(thm)], ['39'])).
% 57.11/57.31  thf('41', plain,
% 57.11/57.31      (![X16 : $i]:
% 57.11/57.31         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 57.11/57.31      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.11/57.31  thf('42', plain,
% 57.11/57.31      (![X12 : $i]:
% 57.11/57.31         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 57.11/57.31      inference('cnf', [status(esa)], [t29_mcart_1])).
% 57.11/57.31  thf('43', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 57.11/57.31            = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['7', '10'])).
% 57.11/57.31  thf('44', plain,
% 57.11/57.31      (![X16 : $i]:
% 57.11/57.31         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 57.11/57.31      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.11/57.31  thf('45', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['5', '6'])).
% 57.11/57.31  thf('46', plain,
% 57.11/57.31      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 57.11/57.31         (~ (l1_orders_2 @ X24)
% 57.11/57.31          | ~ (v5_orders_2 @ X24)
% 57.11/57.31          | ~ (v4_orders_2 @ X24)
% 57.11/57.31          | ~ (v3_orders_2 @ X24)
% 57.11/57.31          | (v2_struct_0 @ X24)
% 57.11/57.31          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 57.11/57.31          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X24))
% 57.11/57.31          | (r2_orders_2 @ X24 @ (sk_D @ X25 @ X24 @ X27) @ X26)
% 57.11/57.31          | ~ (r2_hidden @ X26 @ X25)
% 57.11/57.31          | ~ (r2_hidden @ X27 @ (a_2_1_orders_2 @ X24 @ X25)))),
% 57.11/57.31      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 57.11/57.31  thf('47', plain,
% 57.11/57.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 57.11/57.31         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 57.11/57.31          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 57.11/57.31          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 57.11/57.31          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['45', '46'])).
% 57.11/57.31  thf('48', plain,
% 57.11/57.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 57.11/57.31         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 57.11/57.31          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 57.11/57.31          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0)))),
% 57.11/57.31      inference('sup-', [status(thm)], ['44', '47'])).
% 57.11/57.31  thf('49', plain,
% 57.11/57.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 57.11/57.31         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 57.11/57.31          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 57.11/57.31          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['43', '48'])).
% 57.11/57.31  thf('50', plain,
% 57.11/57.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 57.11/57.31         (~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 57.11/57.31          | (r2_orders_2 @ X0 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ X2)
% 57.11/57.31          | ~ (r2_hidden @ X2 @ (u1_struct_0 @ X0))
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 57.11/57.31      inference('simplify', [status(thm)], ['49'])).
% 57.11/57.31  thf('51', plain,
% 57.11/57.31      (![X0 : $i, X1 : $i]:
% 57.11/57.31         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 57.11/57.31          | (r2_orders_2 @ X0 @ 
% 57.11/57.31             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 57.11/57.31              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 57.11/57.31             X1)
% 57.11/57.31          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0)))),
% 57.11/57.31      inference('sup-', [status(thm)], ['42', '50'])).
% 57.11/57.31  thf('52', plain,
% 57.11/57.31      (![X0 : $i, X1 : $i]:
% 57.11/57.31         (~ (r2_hidden @ X1 @ (k2_struct_0 @ X0))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 57.11/57.31          | (r2_orders_2 @ X0 @ 
% 57.11/57.31             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 57.11/57.31              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 57.11/57.31             X1)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 57.11/57.31      inference('sup-', [status(thm)], ['41', '51'])).
% 57.11/57.31  thf('53', plain,
% 57.11/57.31      (![X0 : $i, X1 : $i]:
% 57.11/57.31         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | (r2_orders_2 @ X0 @ 
% 57.11/57.31             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 57.11/57.31              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 57.11/57.31             X1)
% 57.11/57.31          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0)))),
% 57.11/57.31      inference('simplify', [status(thm)], ['52'])).
% 57.11/57.31  thf('54', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 57.11/57.31               (k2_struct_0 @ X0))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | (r2_orders_2 @ X0 @ 
% 57.11/57.31             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 57.11/57.31              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 57.11/57.31             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 57.11/57.31      inference('sup-', [status(thm)], ['40', '53'])).
% 57.11/57.31  thf('55', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         ((r2_orders_2 @ X0 @ 
% 57.11/57.31           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 57.11/57.31            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 57.11/57.31           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 57.11/57.31          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 57.11/57.31               (k2_struct_0 @ X0))
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0))),
% 57.11/57.31      inference('simplify', [status(thm)], ['54'])).
% 57.11/57.31  thf('56', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | (r2_orders_2 @ X0 @ 
% 57.11/57.31             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 57.11/57.31              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 57.11/57.31             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 57.11/57.31      inference('sup-', [status(thm)], ['36', '55'])).
% 57.11/57.31  thf('57', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         ((r2_orders_2 @ X0 @ 
% 57.11/57.31           (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 57.11/57.31            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 57.11/57.31           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 57.11/57.31      inference('simplify', [status(thm)], ['56'])).
% 57.11/57.31  thf('58', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 57.11/57.31              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 57.11/57.31                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 57.11/57.31      inference('sup-', [status(thm)], ['1', '18'])).
% 57.11/57.31  thf('59', plain,
% 57.11/57.31      (![X16 : $i]:
% 57.11/57.31         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 57.11/57.31      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.11/57.31  thf('60', plain,
% 57.11/57.31      (![X12 : $i]:
% 57.11/57.31         (((X12) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X12) @ X12))),
% 57.11/57.31      inference('cnf', [status(esa)], [t29_mcart_1])).
% 57.11/57.31  thf('61', plain,
% 57.11/57.31      (![X16 : $i]:
% 57.11/57.31         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 57.11/57.31      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.11/57.31  thf('62', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['5', '6'])).
% 57.11/57.31  thf('63', plain,
% 57.11/57.31      (![X21 : $i, X22 : $i]:
% 57.11/57.31         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 57.11/57.31          | ((k2_orders_2 @ X22 @ X21) = (a_2_1_orders_2 @ X22 @ X21))
% 57.11/57.31          | ~ (l1_orders_2 @ X22)
% 57.11/57.31          | ~ (v5_orders_2 @ X22)
% 57.11/57.31          | ~ (v4_orders_2 @ X22)
% 57.11/57.31          | ~ (v3_orders_2 @ X22)
% 57.11/57.31          | (v2_struct_0 @ X22))),
% 57.11/57.31      inference('cnf', [status(esa)], [d13_orders_2])).
% 57.11/57.31  thf('64', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         ((v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (u1_struct_0 @ X0))
% 57.11/57.31              = (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 57.11/57.31      inference('sup-', [status(thm)], ['62', '63'])).
% 57.11/57.31  thf('65', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['5', '6'])).
% 57.11/57.31  thf('66', plain,
% 57.11/57.31      (![X24 : $i, X25 : $i, X27 : $i]:
% 57.11/57.31         (~ (l1_orders_2 @ X24)
% 57.11/57.31          | ~ (v5_orders_2 @ X24)
% 57.11/57.31          | ~ (v4_orders_2 @ X24)
% 57.11/57.31          | ~ (v3_orders_2 @ X24)
% 57.11/57.31          | (v2_struct_0 @ X24)
% 57.11/57.31          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 57.11/57.31          | (m1_subset_1 @ (sk_D @ X25 @ X24 @ X27) @ (u1_struct_0 @ X24))
% 57.11/57.31          | ~ (r2_hidden @ X27 @ (a_2_1_orders_2 @ X24 @ X25)))),
% 57.11/57.31      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 57.11/57.31  thf('67', plain,
% 57.11/57.31      (![X0 : $i, X1 : $i]:
% 57.11/57.31         (~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 57.11/57.31          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 57.11/57.31             (u1_struct_0 @ X0))
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['65', '66'])).
% 57.11/57.31  thf('68', plain,
% 57.11/57.31      (![X0 : $i, X1 : $i]:
% 57.11/57.31         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0)))
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 57.11/57.31             (u1_struct_0 @ X0)))),
% 57.11/57.31      inference('sup-', [status(thm)], ['64', '67'])).
% 57.11/57.31  thf('69', plain,
% 57.11/57.31      (![X0 : $i, X1 : $i]:
% 57.11/57.31         ((m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 57.11/57.31           (u1_struct_0 @ X0))
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (u1_struct_0 @ X0))))),
% 57.11/57.31      inference('simplify', [status(thm)], ['68'])).
% 57.11/57.31  thf('70', plain,
% 57.11/57.31      (![X0 : $i, X1 : $i]:
% 57.11/57.31         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | (m1_subset_1 @ (sk_D @ (u1_struct_0 @ X0) @ X0 @ X1) @ 
% 57.11/57.31             (u1_struct_0 @ X0)))),
% 57.11/57.31      inference('sup-', [status(thm)], ['61', '69'])).
% 57.11/57.31  thf('71', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | (m1_subset_1 @ 
% 57.11/57.31             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 57.11/57.31              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 57.11/57.31             (u1_struct_0 @ X0))
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['60', '70'])).
% 57.11/57.31  thf(d10_orders_2, axiom,
% 57.11/57.31    (![A:$i]:
% 57.11/57.31     ( ( l1_orders_2 @ A ) =>
% 57.11/57.31       ( ![B:$i]:
% 57.11/57.31         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 57.11/57.31           ( ![C:$i]:
% 57.11/57.31             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 57.11/57.31               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 57.11/57.31                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 57.11/57.31  thf('72', plain,
% 57.11/57.31      (![X18 : $i, X19 : $i, X20 : $i]:
% 57.11/57.31         (~ (m1_subset_1 @ X18 @ (u1_struct_0 @ X19))
% 57.11/57.31          | ~ (r2_orders_2 @ X19 @ X18 @ X20)
% 57.11/57.31          | ((X18) != (X20))
% 57.11/57.31          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19))
% 57.11/57.31          | ~ (l1_orders_2 @ X19))),
% 57.11/57.31      inference('cnf', [status(esa)], [d10_orders_2])).
% 57.11/57.31  thf('73', plain,
% 57.11/57.31      (![X19 : $i, X20 : $i]:
% 57.11/57.31         (~ (l1_orders_2 @ X19)
% 57.11/57.31          | ~ (r2_orders_2 @ X19 @ X20 @ X20)
% 57.11/57.31          | ~ (m1_subset_1 @ X20 @ (u1_struct_0 @ X19)))),
% 57.11/57.31      inference('simplify', [status(thm)], ['72'])).
% 57.11/57.31  thf('74', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (~ (l1_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | ~ (r2_orders_2 @ X0 @ 
% 57.11/57.31               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 57.11/57.31                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 57.11/57.31               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 57.11/57.31                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 57.11/57.31          | ~ (l1_orders_2 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['71', '73'])).
% 57.11/57.31  thf('75', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (~ (r2_orders_2 @ X0 @ 
% 57.11/57.31             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 57.11/57.31              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 57.11/57.31             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 57.11/57.31              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0))),
% 57.11/57.31      inference('simplify', [status(thm)], ['74'])).
% 57.11/57.31  thf('76', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (~ (r2_orders_2 @ X0 @ 
% 57.11/57.31             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 57.11/57.31              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 57.11/57.31             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 57.11/57.31              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 57.11/57.31      inference('sup-', [status(thm)], ['59', '75'])).
% 57.11/57.31  thf('77', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ~ (r2_orders_2 @ X0 @ 
% 57.11/57.31               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 57.11/57.31                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 57.11/57.31               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 57.11/57.31                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 57.11/57.31      inference('simplify', [status(thm)], ['76'])).
% 57.11/57.31  thf('78', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (~ (r2_orders_2 @ X0 @ 
% 57.11/57.31             (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 57.11/57.31              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 57.11/57.31             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 57.11/57.31      inference('sup-', [status(thm)], ['58', '77'])).
% 57.11/57.31  thf('79', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (r2_orders_2 @ X0 @ 
% 57.11/57.31               (sk_D @ (u1_struct_0 @ X0) @ X0 @ 
% 57.11/57.31                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 57.11/57.31               (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 57.11/57.31      inference('simplify', [status(thm)], ['78'])).
% 57.11/57.31  thf('80', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 57.11/57.31      inference('sup-', [status(thm)], ['57', '79'])).
% 57.11/57.31  thf('81', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (~ (l1_orders_2 @ X0)
% 57.11/57.31          | ~ (v5_orders_2 @ X0)
% 57.11/57.31          | ~ (v4_orders_2 @ X0)
% 57.11/57.31          | ~ (v3_orders_2 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 57.11/57.31          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 57.11/57.31      inference('simplify', [status(thm)], ['80'])).
% 57.11/57.31  thf('82', plain,
% 57.11/57.31      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 57.11/57.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.11/57.31  thf('83', plain,
% 57.11/57.31      ((((k1_xboole_0) != (k1_xboole_0))
% 57.11/57.31        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 57.11/57.31        | ~ (l1_struct_0 @ sk_A)
% 57.11/57.31        | (v2_struct_0 @ sk_A)
% 57.11/57.31        | ~ (v3_orders_2 @ sk_A)
% 57.11/57.31        | ~ (v4_orders_2 @ sk_A)
% 57.11/57.31        | ~ (v5_orders_2 @ sk_A)
% 57.11/57.31        | ~ (l1_orders_2 @ sk_A))),
% 57.11/57.31      inference('sup-', [status(thm)], ['81', '82'])).
% 57.11/57.31  thf('84', plain, ((l1_orders_2 @ sk_A)),
% 57.11/57.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.11/57.31  thf(dt_l1_orders_2, axiom,
% 57.11/57.31    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 57.11/57.31  thf('85', plain,
% 57.11/57.31      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_orders_2 @ X23))),
% 57.11/57.31      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 57.11/57.31  thf('86', plain, ((l1_struct_0 @ sk_A)),
% 57.11/57.31      inference('sup-', [status(thm)], ['84', '85'])).
% 57.11/57.31  thf('87', plain, ((v3_orders_2 @ sk_A)),
% 57.11/57.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.11/57.31  thf('88', plain, ((v4_orders_2 @ sk_A)),
% 57.11/57.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.11/57.31  thf('89', plain, ((v5_orders_2 @ sk_A)),
% 57.11/57.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.11/57.31  thf('90', plain, ((l1_orders_2 @ sk_A)),
% 57.11/57.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.11/57.31  thf('91', plain,
% 57.11/57.31      ((((k1_xboole_0) != (k1_xboole_0))
% 57.11/57.31        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 57.11/57.31        | (v2_struct_0 @ sk_A))),
% 57.11/57.31      inference('demod', [status(thm)], ['83', '86', '87', '88', '89', '90'])).
% 57.11/57.31  thf('92', plain,
% 57.11/57.31      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 57.11/57.31      inference('simplify', [status(thm)], ['91'])).
% 57.11/57.31  thf('93', plain, (~ (v2_struct_0 @ sk_A)),
% 57.11/57.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 57.11/57.31  thf('94', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 57.11/57.31      inference('clc', [status(thm)], ['92', '93'])).
% 57.11/57.31  thf('95', plain,
% 57.11/57.31      (![X16 : $i]:
% 57.11/57.31         (((k2_struct_0 @ X16) = (u1_struct_0 @ X16)) | ~ (l1_struct_0 @ X16))),
% 57.11/57.31      inference('cnf', [status(esa)], [d3_struct_0])).
% 57.11/57.31  thf(fc2_struct_0, axiom,
% 57.11/57.31    (![A:$i]:
% 57.11/57.31     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 57.11/57.31       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 57.11/57.31  thf('96', plain,
% 57.11/57.31      (![X17 : $i]:
% 57.11/57.31         (~ (v1_xboole_0 @ (u1_struct_0 @ X17))
% 57.11/57.31          | ~ (l1_struct_0 @ X17)
% 57.11/57.31          | (v2_struct_0 @ X17))),
% 57.11/57.31      inference('cnf', [status(esa)], [fc2_struct_0])).
% 57.11/57.31  thf('97', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | (v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0))),
% 57.11/57.31      inference('sup-', [status(thm)], ['95', '96'])).
% 57.11/57.31  thf('98', plain,
% 57.11/57.31      (![X0 : $i]:
% 57.11/57.31         ((v2_struct_0 @ X0)
% 57.11/57.31          | ~ (l1_struct_0 @ X0)
% 57.11/57.31          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 57.11/57.31      inference('simplify', [status(thm)], ['97'])).
% 57.11/57.31  thf('99', plain, ((~ (l1_struct_0 @ sk_A) | (v2_struct_0 @ sk_A))),
% 57.11/57.31      inference('sup-', [status(thm)], ['94', '98'])).
% 57.11/57.31  thf('100', plain, ((l1_struct_0 @ sk_A)),
% 57.11/57.31      inference('sup-', [status(thm)], ['84', '85'])).
% 57.11/57.31  thf('101', plain, ((v2_struct_0 @ sk_A)),
% 57.11/57.31      inference('demod', [status(thm)], ['99', '100'])).
% 57.11/57.31  thf('102', plain, ($false), inference('demod', [status(thm)], ['0', '101'])).
% 57.11/57.31  
% 57.11/57.31  % SZS output end Refutation
% 57.11/57.31  
% 57.11/57.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
