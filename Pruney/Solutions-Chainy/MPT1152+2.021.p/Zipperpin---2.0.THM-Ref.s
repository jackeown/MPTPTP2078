%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fGnINiZAFQ

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:45 EST 2020

% Result     : Theorem 8.85s
% Output     : Refutation 8.85s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 132 expanded)
%              Number of leaves         :   31 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          : 1529 (2045 expanded)
%              Number of equality atoms :   45 (  67 expanded)
%              Maximal formula depth    :   24 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

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

thf(t1_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
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

thf('4',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_orders_2 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_orders_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ X1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf('11',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf('17',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
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

thf('18',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( ( k2_orders_2 @ X17 @ X16 )
        = ( a_2_1_orders_2 @ X17 @ X16 ) )
      | ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
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

thf('21',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( u1_struct_0 @ X21 ) )
      | ( r2_orders_2 @ X21 @ ( sk_D @ X22 @ X21 @ X24 ) @ X23 )
      | ~ ( r2_hidden @ X23 @ X22 )
      | ~ ( r2_hidden @ X24 @ ( a_2_1_orders_2 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('22',plain,(
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
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
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
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
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
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
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
    inference('sup-',[status(thm)],['16','24'])).

thf('26',plain,(
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
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( r2_hidden @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['10','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('32',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('33',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( X24
        = ( sk_D @ X22 @ X21 @ X24 ) )
      | ~ ( r2_hidden @ X24 @ ( a_2_1_orders_2 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('34',plain,(
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
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
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
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
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
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
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
    inference('sup-',[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X10: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X10 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('40',plain,(
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('41',plain,(
    ! [X21: $i,X22: $i,X24: $i] :
      ( ~ ( l1_orders_2 @ X21 )
      | ~ ( v5_orders_2 @ X21 )
      | ~ ( v4_orders_2 @ X21 )
      | ~ ( v3_orders_2 @ X21 )
      | ( v2_struct_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X21 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X22 @ X21 @ X24 ) @ ( u1_struct_0 @ X21 ) )
      | ~ ( r2_hidden @ X24 @ ( a_2_1_orders_2 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
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
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
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
    inference('sup-',[status(thm)],['38','44'])).

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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r2_orders_2 @ X14 @ X13 @ X15 )
      | ( X13 != X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('47',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( r2_orders_2 @ X14 @ X15 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

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
      | ~ ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
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
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
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
    inference('sup-',[status(thm)],['37','49'])).

thf('51',plain,(
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
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
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
    inference('sup-',[status(thm)],['29','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('57',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_orders_2 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('58',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','58','59','60','61','62'])).

thf('64',plain,(
    v2_struct_0 @ sk_A ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['0','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fGnINiZAFQ
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:07:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 8.85/9.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.85/9.08  % Solved by: fo/fo7.sh
% 8.85/9.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.85/9.08  % done 7894 iterations in 8.619s
% 8.85/9.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.85/9.08  % SZS output start Refutation
% 8.85/9.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.85/9.08  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 8.85/9.08  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 8.85/9.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.85/9.08  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 8.85/9.08  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 8.85/9.08  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 8.85/9.08  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 8.85/9.08  thf(sk_A_type, type, sk_A: $i).
% 8.85/9.08  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.85/9.08  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 8.85/9.08  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 8.85/9.08  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 8.85/9.08  thf(sk_B_type, type, sk_B: $i > $i).
% 8.85/9.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.85/9.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.85/9.08  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 8.85/9.08  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 8.85/9.08  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 8.85/9.08  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 8.85/9.08  thf(t46_orders_2, conjecture,
% 8.85/9.08    (![A:$i]:
% 8.85/9.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 8.85/9.08         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 8.85/9.08       ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 8.85/9.08  thf(zf_stmt_0, negated_conjecture,
% 8.85/9.08    (~( ![A:$i]:
% 8.85/9.08        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 8.85/9.08            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 8.85/9.08          ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 8.85/9.08    inference('cnf.neg', [status(esa)], [t46_orders_2])).
% 8.85/9.08  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 8.85/9.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.08  thf(t1_mcart_1, axiom,
% 8.85/9.08    (![A:$i]:
% 8.85/9.08     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 8.85/9.08          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 8.85/9.08  thf('1', plain,
% 8.85/9.08      (![X10 : $i]:
% 8.85/9.08         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 8.85/9.08      inference('cnf', [status(esa)], [t1_mcart_1])).
% 8.85/9.08  thf(d3_struct_0, axiom,
% 8.85/9.08    (![A:$i]:
% 8.85/9.08     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 8.85/9.08  thf('2', plain,
% 8.85/9.08      (![X11 : $i]:
% 8.85/9.08         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 8.85/9.08      inference('cnf', [status(esa)], [d3_struct_0])).
% 8.85/9.08  thf(dt_k2_struct_0, axiom,
% 8.85/9.08    (![A:$i]:
% 8.85/9.08     ( ( l1_struct_0 @ A ) =>
% 8.85/9.08       ( m1_subset_1 @
% 8.85/9.08         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 8.85/9.08  thf('3', plain,
% 8.85/9.08      (![X12 : $i]:
% 8.85/9.08         ((m1_subset_1 @ (k2_struct_0 @ X12) @ 
% 8.85/9.08           (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 8.85/9.08          | ~ (l1_struct_0 @ X12))),
% 8.85/9.08      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 8.85/9.08  thf(dt_k2_orders_2, axiom,
% 8.85/9.08    (![A:$i,B:$i]:
% 8.85/9.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 8.85/9.08         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 8.85/9.08         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.85/9.08       ( m1_subset_1 @
% 8.85/9.08         ( k2_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 8.85/9.08  thf('4', plain,
% 8.85/9.08      (![X18 : $i, X19 : $i]:
% 8.85/9.08         (~ (l1_orders_2 @ X18)
% 8.85/9.08          | ~ (v5_orders_2 @ X18)
% 8.85/9.08          | ~ (v4_orders_2 @ X18)
% 8.85/9.08          | ~ (v3_orders_2 @ X18)
% 8.85/9.08          | (v2_struct_0 @ X18)
% 8.85/9.08          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 8.85/9.08          | (m1_subset_1 @ (k2_orders_2 @ X18 @ X19) @ 
% 8.85/9.08             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 8.85/9.08      inference('cnf', [status(esa)], [dt_k2_orders_2])).
% 8.85/9.08  thf('5', plain,
% 8.85/9.08      (![X0 : $i]:
% 8.85/9.08         (~ (l1_struct_0 @ X0)
% 8.85/9.08          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 8.85/9.08             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 8.85/9.08          | (v2_struct_0 @ X0)
% 8.85/9.08          | ~ (v3_orders_2 @ X0)
% 8.85/9.08          | ~ (v4_orders_2 @ X0)
% 8.85/9.08          | ~ (v5_orders_2 @ X0)
% 8.85/9.08          | ~ (l1_orders_2 @ X0))),
% 8.85/9.08      inference('sup-', [status(thm)], ['3', '4'])).
% 8.85/9.08  thf('6', plain,
% 8.85/9.08      (![X0 : $i]:
% 8.85/9.08         ((m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 8.85/9.08           (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 8.85/9.08          | ~ (l1_struct_0 @ X0)
% 8.85/9.08          | ~ (l1_orders_2 @ X0)
% 8.85/9.08          | ~ (v5_orders_2 @ X0)
% 8.85/9.08          | ~ (v4_orders_2 @ X0)
% 8.85/9.08          | ~ (v3_orders_2 @ X0)
% 8.85/9.08          | (v2_struct_0 @ X0)
% 8.85/9.08          | ~ (l1_struct_0 @ X0))),
% 8.85/9.08      inference('sup+', [status(thm)], ['2', '5'])).
% 8.85/9.08  thf('7', plain,
% 8.85/9.08      (![X0 : $i]:
% 8.85/9.08         ((v2_struct_0 @ X0)
% 8.85/9.08          | ~ (v3_orders_2 @ X0)
% 8.85/9.08          | ~ (v4_orders_2 @ X0)
% 8.85/9.08          | ~ (v5_orders_2 @ X0)
% 8.85/9.08          | ~ (l1_orders_2 @ X0)
% 8.85/9.08          | ~ (l1_struct_0 @ X0)
% 8.85/9.08          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 8.85/9.08             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 8.85/9.08      inference('simplify', [status(thm)], ['6'])).
% 8.85/9.08  thf(l3_subset_1, axiom,
% 8.85/9.08    (![A:$i,B:$i]:
% 8.85/9.08     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.85/9.08       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 8.85/9.08  thf('8', plain,
% 8.85/9.08      (![X1 : $i, X2 : $i, X3 : $i]:
% 8.85/9.08         (~ (r2_hidden @ X1 @ X2)
% 8.85/9.08          | (r2_hidden @ X1 @ X3)
% 8.85/9.08          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 8.85/9.08      inference('cnf', [status(esa)], [l3_subset_1])).
% 8.85/9.08  thf('9', plain,
% 8.85/9.08      (![X0 : $i, X1 : $i]:
% 8.85/9.08         (~ (l1_struct_0 @ X0)
% 8.85/9.08          | ~ (l1_orders_2 @ X0)
% 8.85/9.08          | ~ (v5_orders_2 @ X0)
% 8.85/9.08          | ~ (v4_orders_2 @ X0)
% 8.85/9.08          | ~ (v3_orders_2 @ X0)
% 8.85/9.08          | (v2_struct_0 @ X0)
% 8.85/9.08          | (r2_hidden @ X1 @ (k2_struct_0 @ X0))
% 8.85/9.08          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 8.85/9.08      inference('sup-', [status(thm)], ['7', '8'])).
% 8.85/9.08  thf('10', plain,
% 8.85/9.08      (![X0 : $i]:
% 8.85/9.08         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 8.85/9.08          | (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 8.85/9.08             (k2_struct_0 @ X0))
% 8.85/9.08          | (v2_struct_0 @ X0)
% 8.85/9.08          | ~ (v3_orders_2 @ X0)
% 8.85/9.08          | ~ (v4_orders_2 @ X0)
% 8.85/9.08          | ~ (v5_orders_2 @ X0)
% 8.85/9.08          | ~ (l1_orders_2 @ X0)
% 8.85/9.08          | ~ (l1_struct_0 @ X0))),
% 8.85/9.08      inference('sup-', [status(thm)], ['1', '9'])).
% 8.85/9.08  thf('11', plain,
% 8.85/9.08      (![X10 : $i]:
% 8.85/9.08         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 8.85/9.08      inference('cnf', [status(esa)], [t1_mcart_1])).
% 8.85/9.08  thf('12', plain,
% 8.85/9.08      (![X0 : $i]:
% 8.85/9.08         (~ (l1_struct_0 @ X0)
% 8.85/9.08          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 8.85/9.08             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 8.85/9.08          | (v2_struct_0 @ X0)
% 8.85/9.08          | ~ (v3_orders_2 @ X0)
% 8.85/9.08          | ~ (v4_orders_2 @ X0)
% 8.85/9.08          | ~ (v5_orders_2 @ X0)
% 8.85/9.08          | ~ (l1_orders_2 @ X0))),
% 8.85/9.08      inference('sup-', [status(thm)], ['3', '4'])).
% 8.85/9.08  thf(t4_subset, axiom,
% 8.85/9.08    (![A:$i,B:$i,C:$i]:
% 8.85/9.08     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 8.85/9.08       ( m1_subset_1 @ A @ C ) ))).
% 8.85/9.08  thf('13', plain,
% 8.85/9.08      (![X5 : $i, X6 : $i, X7 : $i]:
% 8.85/9.08         (~ (r2_hidden @ X5 @ X6)
% 8.85/9.08          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 8.85/9.08          | (m1_subset_1 @ X5 @ X7))),
% 8.85/9.08      inference('cnf', [status(esa)], [t4_subset])).
% 8.85/9.08  thf('14', plain,
% 8.85/9.08      (![X0 : $i, X1 : $i]:
% 8.85/9.08         (~ (l1_orders_2 @ X0)
% 8.85/9.08          | ~ (v5_orders_2 @ X0)
% 8.85/9.08          | ~ (v4_orders_2 @ X0)
% 8.85/9.08          | ~ (v3_orders_2 @ X0)
% 8.85/9.08          | (v2_struct_0 @ X0)
% 8.85/9.08          | ~ (l1_struct_0 @ X0)
% 8.85/9.08          | (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 8.85/9.08          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 8.85/9.08      inference('sup-', [status(thm)], ['12', '13'])).
% 8.85/9.08  thf('15', plain,
% 8.85/9.08      (![X0 : $i]:
% 8.85/9.08         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 8.85/9.08          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 8.85/9.08             (u1_struct_0 @ X0))
% 8.85/9.08          | ~ (l1_struct_0 @ X0)
% 8.85/9.08          | (v2_struct_0 @ X0)
% 8.85/9.08          | ~ (v3_orders_2 @ X0)
% 8.85/9.08          | ~ (v4_orders_2 @ X0)
% 8.85/9.08          | ~ (v5_orders_2 @ X0)
% 8.85/9.08          | ~ (l1_orders_2 @ X0))),
% 8.85/9.08      inference('sup-', [status(thm)], ['11', '14'])).
% 8.85/9.08  thf('16', plain,
% 8.85/9.08      (![X10 : $i]:
% 8.85/9.08         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 8.85/9.08      inference('cnf', [status(esa)], [t1_mcart_1])).
% 8.85/9.08  thf('17', plain,
% 8.85/9.08      (![X12 : $i]:
% 8.85/9.08         ((m1_subset_1 @ (k2_struct_0 @ X12) @ 
% 8.85/9.08           (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 8.85/9.08          | ~ (l1_struct_0 @ X12))),
% 8.85/9.08      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 8.85/9.08  thf(d13_orders_2, axiom,
% 8.85/9.08    (![A:$i]:
% 8.85/9.08     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 8.85/9.08         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 8.85/9.08       ( ![B:$i]:
% 8.85/9.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.85/9.08           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 8.85/9.08  thf('18', plain,
% 8.85/9.08      (![X16 : $i, X17 : $i]:
% 8.85/9.08         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 8.85/9.08          | ((k2_orders_2 @ X17 @ X16) = (a_2_1_orders_2 @ X17 @ X16))
% 8.85/9.08          | ~ (l1_orders_2 @ X17)
% 8.85/9.08          | ~ (v5_orders_2 @ X17)
% 8.85/9.08          | ~ (v4_orders_2 @ X17)
% 8.85/9.08          | ~ (v3_orders_2 @ X17)
% 8.85/9.08          | (v2_struct_0 @ X17))),
% 8.85/9.08      inference('cnf', [status(esa)], [d13_orders_2])).
% 8.85/9.08  thf('19', plain,
% 8.85/9.08      (![X0 : $i]:
% 8.85/9.08         (~ (l1_struct_0 @ X0)
% 8.85/9.08          | (v2_struct_0 @ X0)
% 8.85/9.08          | ~ (v3_orders_2 @ X0)
% 8.85/9.08          | ~ (v4_orders_2 @ X0)
% 8.85/9.08          | ~ (v5_orders_2 @ X0)
% 8.85/9.08          | ~ (l1_orders_2 @ X0)
% 8.85/9.08          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 8.85/9.08              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 8.85/9.08      inference('sup-', [status(thm)], ['17', '18'])).
% 8.85/9.08  thf('20', plain,
% 8.85/9.08      (![X12 : $i]:
% 8.85/9.08         ((m1_subset_1 @ (k2_struct_0 @ X12) @ 
% 8.85/9.08           (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 8.85/9.08          | ~ (l1_struct_0 @ X12))),
% 8.85/9.08      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 8.85/9.08  thf(fraenkel_a_2_1_orders_2, axiom,
% 8.85/9.08    (![A:$i,B:$i,C:$i]:
% 8.85/9.08     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 8.85/9.08         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 8.85/9.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 8.85/9.08       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 8.85/9.08         ( ?[D:$i]:
% 8.85/9.08           ( ( ![E:$i]:
% 8.85/9.08               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 8.85/9.08                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 8.85/9.08             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 8.85/9.08  thf('21', plain,
% 8.85/9.08      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 8.85/9.08         (~ (l1_orders_2 @ X21)
% 8.85/9.08          | ~ (v5_orders_2 @ X21)
% 8.85/9.08          | ~ (v4_orders_2 @ X21)
% 8.85/9.08          | ~ (v3_orders_2 @ X21)
% 8.85/9.08          | (v2_struct_0 @ X21)
% 8.85/9.08          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 8.85/9.08          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 8.85/9.08          | (r2_orders_2 @ X21 @ (sk_D @ X22 @ X21 @ X24) @ X23)
% 8.85/9.08          | ~ (r2_hidden @ X23 @ X22)
% 8.85/9.08          | ~ (r2_hidden @ X24 @ (a_2_1_orders_2 @ X21 @ X22)))),
% 8.85/9.08      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 8.85/9.08  thf('22', plain,
% 8.85/9.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.85/9.08         (~ (l1_struct_0 @ X0)
% 8.85/9.08          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 8.85/9.08          | ~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 8.85/9.08          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 8.85/9.08          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 8.85/9.08          | (v2_struct_0 @ X0)
% 8.85/9.08          | ~ (v3_orders_2 @ X0)
% 8.85/9.08          | ~ (v4_orders_2 @ X0)
% 8.85/9.08          | ~ (v5_orders_2 @ X0)
% 8.85/9.08          | ~ (l1_orders_2 @ X0))),
% 8.85/9.09      inference('sup-', [status(thm)], ['20', '21'])).
% 8.85/9.09  thf('23', plain,
% 8.85/9.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.85/9.09         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (l1_struct_0 @ X0)
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 8.85/9.09          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 8.85/9.09          | ~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 8.85/9.09          | ~ (l1_struct_0 @ X0))),
% 8.85/9.09      inference('sup-', [status(thm)], ['19', '22'])).
% 8.85/9.09  thf('24', plain,
% 8.85/9.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.85/9.09         (~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 8.85/9.09          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 8.85/9.09          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 8.85/9.09          | ~ (l1_struct_0 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 8.85/9.09      inference('simplify', [status(thm)], ['23'])).
% 8.85/9.09  thf('25', plain,
% 8.85/9.09      (![X0 : $i, X1 : $i]:
% 8.85/9.09         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (l1_struct_0 @ X0)
% 8.85/9.09          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 8.85/9.09          | (r2_orders_2 @ X0 @ 
% 8.85/9.09             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 8.85/9.09              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 8.85/9.09             X1)
% 8.85/9.09          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0)))),
% 8.85/9.09      inference('sup-', [status(thm)], ['16', '24'])).
% 8.85/9.09  thf('26', plain,
% 8.85/9.09      (![X0 : $i]:
% 8.85/9.09         (~ (l1_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (l1_struct_0 @ X0)
% 8.85/9.09          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 8.85/9.09          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 8.85/9.09               (k2_struct_0 @ X0))
% 8.85/9.09          | (r2_orders_2 @ X0 @ 
% 8.85/9.09             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 8.85/9.09              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 8.85/9.09             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 8.85/9.09          | ~ (l1_struct_0 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 8.85/9.09      inference('sup-', [status(thm)], ['15', '25'])).
% 8.85/9.09  thf('27', plain,
% 8.85/9.09      (![X0 : $i]:
% 8.85/9.09         ((r2_orders_2 @ X0 @ 
% 8.85/9.09           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 8.85/9.09            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 8.85/9.09           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 8.85/9.09          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 8.85/9.09               (k2_struct_0 @ X0))
% 8.85/9.09          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 8.85/9.09          | ~ (l1_struct_0 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (l1_orders_2 @ X0))),
% 8.85/9.09      inference('simplify', [status(thm)], ['26'])).
% 8.85/9.09  thf('28', plain,
% 8.85/9.09      (![X0 : $i]:
% 8.85/9.09         (~ (l1_struct_0 @ X0)
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (l1_struct_0 @ X0)
% 8.85/9.09          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 8.85/9.09          | (r2_orders_2 @ X0 @ 
% 8.85/9.09             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 8.85/9.09              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 8.85/9.09             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 8.85/9.09      inference('sup-', [status(thm)], ['10', '27'])).
% 8.85/9.09  thf('29', plain,
% 8.85/9.09      (![X0 : $i]:
% 8.85/9.09         ((r2_orders_2 @ X0 @ 
% 8.85/9.09           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 8.85/9.09            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 8.85/9.09           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 8.85/9.09          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ~ (l1_struct_0 @ X0))),
% 8.85/9.09      inference('simplify', [status(thm)], ['28'])).
% 8.85/9.09  thf('30', plain,
% 8.85/9.09      (![X10 : $i]:
% 8.85/9.09         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 8.85/9.09      inference('cnf', [status(esa)], [t1_mcart_1])).
% 8.85/9.09  thf('31', plain,
% 8.85/9.09      (![X0 : $i]:
% 8.85/9.09         (~ (l1_struct_0 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 8.85/9.09              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 8.85/9.09      inference('sup-', [status(thm)], ['17', '18'])).
% 8.85/9.09  thf('32', plain,
% 8.85/9.09      (![X12 : $i]:
% 8.85/9.09         ((m1_subset_1 @ (k2_struct_0 @ X12) @ 
% 8.85/9.09           (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 8.85/9.09          | ~ (l1_struct_0 @ X12))),
% 8.85/9.09      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 8.85/9.09  thf('33', plain,
% 8.85/9.09      (![X21 : $i, X22 : $i, X24 : $i]:
% 8.85/9.09         (~ (l1_orders_2 @ X21)
% 8.85/9.09          | ~ (v5_orders_2 @ X21)
% 8.85/9.09          | ~ (v4_orders_2 @ X21)
% 8.85/9.09          | ~ (v3_orders_2 @ X21)
% 8.85/9.09          | (v2_struct_0 @ X21)
% 8.85/9.09          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 8.85/9.09          | ((X24) = (sk_D @ X22 @ X21 @ X24))
% 8.85/9.09          | ~ (r2_hidden @ X24 @ (a_2_1_orders_2 @ X21 @ X22)))),
% 8.85/9.09      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 8.85/9.09  thf('34', plain,
% 8.85/9.09      (![X0 : $i, X1 : $i]:
% 8.85/9.09         (~ (l1_struct_0 @ X0)
% 8.85/9.09          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 8.85/9.09          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (l1_orders_2 @ X0))),
% 8.85/9.09      inference('sup-', [status(thm)], ['32', '33'])).
% 8.85/9.09  thf('35', plain,
% 8.85/9.09      (![X0 : $i, X1 : $i]:
% 8.85/9.09         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (l1_struct_0 @ X0)
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 8.85/9.09          | ~ (l1_struct_0 @ X0))),
% 8.85/9.09      inference('sup-', [status(thm)], ['31', '34'])).
% 8.85/9.09  thf('36', plain,
% 8.85/9.09      (![X0 : $i, X1 : $i]:
% 8.85/9.09         (((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 8.85/9.09          | ~ (l1_struct_0 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 8.85/9.09      inference('simplify', [status(thm)], ['35'])).
% 8.85/9.09  thf('37', plain,
% 8.85/9.09      (![X0 : $i]:
% 8.85/9.09         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (l1_struct_0 @ X0)
% 8.85/9.09          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 8.85/9.09              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 8.85/9.09                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 8.85/9.09      inference('sup-', [status(thm)], ['30', '36'])).
% 8.85/9.09  thf('38', plain,
% 8.85/9.09      (![X10 : $i]:
% 8.85/9.09         (((X10) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X10) @ X10))),
% 8.85/9.09      inference('cnf', [status(esa)], [t1_mcart_1])).
% 8.85/9.09  thf('39', plain,
% 8.85/9.09      (![X0 : $i]:
% 8.85/9.09         (~ (l1_struct_0 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 8.85/9.09              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 8.85/9.09      inference('sup-', [status(thm)], ['17', '18'])).
% 8.85/9.09  thf('40', plain,
% 8.85/9.09      (![X12 : $i]:
% 8.85/9.09         ((m1_subset_1 @ (k2_struct_0 @ X12) @ 
% 8.85/9.09           (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 8.85/9.09          | ~ (l1_struct_0 @ X12))),
% 8.85/9.09      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 8.85/9.09  thf('41', plain,
% 8.85/9.09      (![X21 : $i, X22 : $i, X24 : $i]:
% 8.85/9.09         (~ (l1_orders_2 @ X21)
% 8.85/9.09          | ~ (v5_orders_2 @ X21)
% 8.85/9.09          | ~ (v4_orders_2 @ X21)
% 8.85/9.09          | ~ (v3_orders_2 @ X21)
% 8.85/9.09          | (v2_struct_0 @ X21)
% 8.85/9.09          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 8.85/9.09          | (m1_subset_1 @ (sk_D @ X22 @ X21 @ X24) @ (u1_struct_0 @ X21))
% 8.85/9.09          | ~ (r2_hidden @ X24 @ (a_2_1_orders_2 @ X21 @ X22)))),
% 8.85/9.09      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 8.85/9.09  thf('42', plain,
% 8.85/9.09      (![X0 : $i, X1 : $i]:
% 8.85/9.09         (~ (l1_struct_0 @ X0)
% 8.85/9.09          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 8.85/9.09          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 8.85/9.09             (u1_struct_0 @ X0))
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (l1_orders_2 @ X0))),
% 8.85/9.09      inference('sup-', [status(thm)], ['40', '41'])).
% 8.85/9.09  thf('43', plain,
% 8.85/9.09      (![X0 : $i, X1 : $i]:
% 8.85/9.09         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (l1_struct_0 @ X0)
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 8.85/9.09             (u1_struct_0 @ X0))
% 8.85/9.09          | ~ (l1_struct_0 @ X0))),
% 8.85/9.09      inference('sup-', [status(thm)], ['39', '42'])).
% 8.85/9.09  thf('44', plain,
% 8.85/9.09      (![X0 : $i, X1 : $i]:
% 8.85/9.09         ((m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 8.85/9.09           (u1_struct_0 @ X0))
% 8.85/9.09          | ~ (l1_struct_0 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 8.85/9.09      inference('simplify', [status(thm)], ['43'])).
% 8.85/9.09  thf('45', plain,
% 8.85/9.09      (![X0 : $i]:
% 8.85/9.09         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (l1_struct_0 @ X0)
% 8.85/9.09          | (m1_subset_1 @ 
% 8.85/9.09             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 8.85/9.09              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 8.85/9.09             (u1_struct_0 @ X0)))),
% 8.85/9.09      inference('sup-', [status(thm)], ['38', '44'])).
% 8.85/9.09  thf(d10_orders_2, axiom,
% 8.85/9.09    (![A:$i]:
% 8.85/9.09     ( ( l1_orders_2 @ A ) =>
% 8.85/9.09       ( ![B:$i]:
% 8.85/9.09         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 8.85/9.09           ( ![C:$i]:
% 8.85/9.09             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 8.85/9.09               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 8.85/9.09                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 8.85/9.09  thf('46', plain,
% 8.85/9.09      (![X13 : $i, X14 : $i, X15 : $i]:
% 8.85/9.09         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 8.85/9.09          | ~ (r2_orders_2 @ X14 @ X13 @ X15)
% 8.85/9.09          | ((X13) != (X15))
% 8.85/9.09          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 8.85/9.09          | ~ (l1_orders_2 @ X14))),
% 8.85/9.09      inference('cnf', [status(esa)], [d10_orders_2])).
% 8.85/9.09  thf('47', plain,
% 8.85/9.09      (![X14 : $i, X15 : $i]:
% 8.85/9.09         (~ (l1_orders_2 @ X14)
% 8.85/9.09          | ~ (r2_orders_2 @ X14 @ X15 @ X15)
% 8.85/9.09          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14)))),
% 8.85/9.09      inference('simplify', [status(thm)], ['46'])).
% 8.85/9.09  thf('48', plain,
% 8.85/9.09      (![X0 : $i]:
% 8.85/9.09         (~ (l1_struct_0 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 8.85/9.09          | ~ (r2_orders_2 @ X0 @ 
% 8.85/9.09               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 8.85/9.09                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 8.85/9.09               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 8.85/9.09                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 8.85/9.09          | ~ (l1_orders_2 @ X0))),
% 8.85/9.09      inference('sup-', [status(thm)], ['45', '47'])).
% 8.85/9.09  thf('49', plain,
% 8.85/9.09      (![X0 : $i]:
% 8.85/9.09         (~ (r2_orders_2 @ X0 @ 
% 8.85/9.09             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 8.85/9.09              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 8.85/9.09             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 8.85/9.09              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 8.85/9.09          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (l1_struct_0 @ X0))),
% 8.85/9.09      inference('simplify', [status(thm)], ['48'])).
% 8.85/9.09  thf('50', plain,
% 8.85/9.09      (![X0 : $i]:
% 8.85/9.09         (~ (r2_orders_2 @ X0 @ 
% 8.85/9.09             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 8.85/9.09              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 8.85/9.09             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 8.85/9.09          | ~ (l1_struct_0 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 8.85/9.09          | ~ (l1_struct_0 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 8.85/9.09      inference('sup-', [status(thm)], ['37', '49'])).
% 8.85/9.09  thf('51', plain,
% 8.85/9.09      (![X0 : $i]:
% 8.85/9.09         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (l1_struct_0 @ X0)
% 8.85/9.09          | ~ (r2_orders_2 @ X0 @ 
% 8.85/9.09               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 8.85/9.09                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 8.85/9.09               (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 8.85/9.09      inference('simplify', [status(thm)], ['50'])).
% 8.85/9.09  thf('52', plain,
% 8.85/9.09      (![X0 : $i]:
% 8.85/9.09         (~ (l1_struct_0 @ X0)
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 8.85/9.09          | ~ (l1_struct_0 @ X0)
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 8.85/9.09      inference('sup-', [status(thm)], ['29', '51'])).
% 8.85/9.09  thf('53', plain,
% 8.85/9.09      (![X0 : $i]:
% 8.85/9.09         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 8.85/9.09          | (v2_struct_0 @ X0)
% 8.85/9.09          | ~ (v3_orders_2 @ X0)
% 8.85/9.09          | ~ (v4_orders_2 @ X0)
% 8.85/9.09          | ~ (v5_orders_2 @ X0)
% 8.85/9.09          | ~ (l1_orders_2 @ X0)
% 8.85/9.09          | ~ (l1_struct_0 @ X0))),
% 8.85/9.09      inference('simplify', [status(thm)], ['52'])).
% 8.85/9.09  thf('54', plain,
% 8.85/9.09      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 8.85/9.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.09  thf('55', plain,
% 8.85/9.09      ((((k1_xboole_0) != (k1_xboole_0))
% 8.85/9.09        | ~ (l1_struct_0 @ sk_A)
% 8.85/9.09        | ~ (l1_orders_2 @ sk_A)
% 8.85/9.09        | ~ (v5_orders_2 @ sk_A)
% 8.85/9.09        | ~ (v4_orders_2 @ sk_A)
% 8.85/9.09        | ~ (v3_orders_2 @ sk_A)
% 8.85/9.09        | (v2_struct_0 @ sk_A))),
% 8.85/9.09      inference('sup-', [status(thm)], ['53', '54'])).
% 8.85/9.09  thf('56', plain, ((l1_orders_2 @ sk_A)),
% 8.85/9.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.09  thf(dt_l1_orders_2, axiom,
% 8.85/9.09    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 8.85/9.09  thf('57', plain,
% 8.85/9.09      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_orders_2 @ X20))),
% 8.85/9.09      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 8.85/9.09  thf('58', plain, ((l1_struct_0 @ sk_A)),
% 8.85/9.09      inference('sup-', [status(thm)], ['56', '57'])).
% 8.85/9.09  thf('59', plain, ((l1_orders_2 @ sk_A)),
% 8.85/9.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.09  thf('60', plain, ((v5_orders_2 @ sk_A)),
% 8.85/9.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.09  thf('61', plain, ((v4_orders_2 @ sk_A)),
% 8.85/9.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.09  thf('62', plain, ((v3_orders_2 @ sk_A)),
% 8.85/9.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.85/9.09  thf('63', plain, ((((k1_xboole_0) != (k1_xboole_0)) | (v2_struct_0 @ sk_A))),
% 8.85/9.09      inference('demod', [status(thm)], ['55', '58', '59', '60', '61', '62'])).
% 8.85/9.09  thf('64', plain, ((v2_struct_0 @ sk_A)),
% 8.85/9.09      inference('simplify', [status(thm)], ['63'])).
% 8.85/9.09  thf('65', plain, ($false), inference('demod', [status(thm)], ['0', '64'])).
% 8.85/9.09  
% 8.85/9.09  % SZS output end Refutation
% 8.85/9.09  
% 8.85/9.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
