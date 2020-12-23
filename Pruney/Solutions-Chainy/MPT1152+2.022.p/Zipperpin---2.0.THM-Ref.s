%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.g7Q3YvpmV0

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:45 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 179 expanded)
%              Number of leaves         :   33 (  68 expanded)
%              Depth                    :   19
%              Number of atoms          : 1724 (2624 expanded)
%              Number of equality atoms :   51 (  90 expanded)
%              Maximal formula depth    :   24 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_mcart_1])).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( ( ( k2_struct_0 @ X10 )
        = ( u1_struct_0 @ X10 ) )
      | ~ ( l1_struct_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ~ ( l1_orders_2 @ X17 )
      | ~ ( v5_orders_2 @ X17 )
      | ~ ( v4_orders_2 @ X17 )
      | ~ ( v3_orders_2 @ X17 )
      | ( v2_struct_0 @ X17 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) )
      | ( m1_subset_1 @ ( k2_orders_2 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X17 ) ) ) ) ),
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

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( m1_subset_1 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( m1_subset_1 @ X1 @ ( k2_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_mcart_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('15',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( m1_subset_1 @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
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
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_mcart_1])).

thf('19',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
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

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X16 ) ) )
      | ( ( k2_orders_2 @ X16 @ X15 )
        = ( a_2_1_orders_2 @ X16 @ X15 ) )
      | ~ ( l1_orders_2 @ X16 )
      | ~ ( v5_orders_2 @ X16 )
      | ~ ( v4_orders_2 @ X16 )
      | ~ ( v3_orders_2 @ X16 )
      | ( v2_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
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

thf('23',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( u1_struct_0 @ X20 ) )
      | ( r2_orders_2 @ X20 @ ( sk_D @ X21 @ X20 @ X23 ) @ X22 )
      | ~ ( r2_hidden @ X22 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( a_2_1_orders_2 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('24',plain,(
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
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
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
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
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
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
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
    inference('sup-',[status(thm)],['18','26'])).

thf('28',plain,(
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
    inference('sup-',[status(thm)],['17','27'])).

thf('29',plain,(
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
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
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
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['12','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_orders_2 @ X0 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) @ ( sk_B @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_mcart_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('34',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('35',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( X23
        = ( sk_D @ X21 @ X20 @ X23 ) )
      | ~ ( r2_hidden @ X23 @ ( a_2_1_orders_2 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('36',plain,(
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
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
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
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
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
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_mcart_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('42',plain,(
    ! [X11: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X11 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X11 ) ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('43',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ~ ( l1_orders_2 @ X20 )
      | ~ ( v5_orders_2 @ X20 )
      | ~ ( v4_orders_2 @ X20 )
      | ~ ( v3_orders_2 @ X20 )
      | ( v2_struct_0 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_subset_1 @ ( sk_D @ X21 @ X20 @ X23 ) @ ( u1_struct_0 @ X20 ) )
      | ~ ( r2_hidden @ X23 @ ( a_2_1_orders_2 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
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
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( sk_D @ ( k2_struct_0 @ X0 ) @ X0 @ X1 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
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
    inference('sup-',[status(thm)],['40','46'])).

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

thf('48',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( u1_struct_0 @ X13 ) )
      | ~ ( r2_orders_2 @ X13 @ X12 @ X14 )
      | ( X12 != X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) )
      | ~ ( l1_orders_2 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('49',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( l1_orders_2 @ X13 )
      | ~ ( r2_orders_2 @ X13 @ X14 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( u1_struct_0 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
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
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
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
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
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
    inference('sup-',[status(thm)],['39','51'])).

thf('53',plain,(
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
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['31','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('63',plain,(
    ! [X19: $i] :
      ( ( l1_struct_0 @ X19 )
      | ~ ( l1_orders_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59','60','61','64'])).

thf('66',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_xboole_0 @ ( k2_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t2_mcart_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('71',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','73'])).

thf('75',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('76',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75','76','77','78','79'])).

thf('81',plain,(
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['80','81'])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['0','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.g7Q3YvpmV0
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:23:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.10  % Solved by: fo/fo7.sh
% 0.91/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.10  % done 704 iterations in 0.643s
% 0.91/1.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.10  % SZS output start Refutation
% 0.91/1.10  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.91/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.10  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.91/1.10  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.91/1.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.10  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.91/1.10  thf(sk_B_type, type, sk_B: $i > $i).
% 0.91/1.10  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.91/1.10  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 0.91/1.10  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.91/1.10  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.91/1.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.10  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.91/1.10  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.91/1.10  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 0.91/1.10  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.91/1.10  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 0.91/1.10  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.91/1.10  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.10  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.91/1.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.10  thf(t46_orders_2, conjecture,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.91/1.10         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.91/1.10       ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 0.91/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.10    (~( ![A:$i]:
% 0.91/1.10        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.91/1.10            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.91/1.10          ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 0.91/1.10    inference('cnf.neg', [status(esa)], [t46_orders_2])).
% 0.91/1.10  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf(t2_mcart_1, axiom,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.91/1.10          ( ![B:$i]:
% 0.91/1.10            ( ~( ( r2_hidden @ B @ A ) & 
% 0.91/1.10                 ( ![C:$i]:
% 0.91/1.10                   ( ( r2_hidden @ C @ B ) => ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.91/1.10  thf('1', plain,
% 0.91/1.10      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.91/1.10      inference('cnf', [status(esa)], [t2_mcart_1])).
% 0.91/1.10  thf(d3_struct_0, axiom,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.91/1.10  thf('2', plain,
% 0.91/1.10      (![X10 : $i]:
% 0.91/1.10         (((k2_struct_0 @ X10) = (u1_struct_0 @ X10)) | ~ (l1_struct_0 @ X10))),
% 0.91/1.10      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.91/1.10  thf(dt_k2_struct_0, axiom,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( l1_struct_0 @ A ) =>
% 0.91/1.10       ( m1_subset_1 @
% 0.91/1.10         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.91/1.10  thf('3', plain,
% 0.91/1.10      (![X11 : $i]:
% 0.91/1.10         ((m1_subset_1 @ (k2_struct_0 @ X11) @ 
% 0.91/1.10           (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.91/1.10          | ~ (l1_struct_0 @ X11))),
% 0.91/1.10      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.91/1.10  thf(dt_k2_orders_2, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.91/1.10         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 0.91/1.10         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.10       ( m1_subset_1 @
% 0.91/1.10         ( k2_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.91/1.10  thf('4', plain,
% 0.91/1.10      (![X17 : $i, X18 : $i]:
% 0.91/1.10         (~ (l1_orders_2 @ X17)
% 0.91/1.10          | ~ (v5_orders_2 @ X17)
% 0.91/1.10          | ~ (v4_orders_2 @ X17)
% 0.91/1.10          | ~ (v3_orders_2 @ X17)
% 0.91/1.10          | (v2_struct_0 @ X17)
% 0.91/1.10          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 0.91/1.10          | (m1_subset_1 @ (k2_orders_2 @ X17 @ X18) @ 
% 0.91/1.10             (k1_zfmisc_1 @ (u1_struct_0 @ X17))))),
% 0.91/1.10      inference('cnf', [status(esa)], [dt_k2_orders_2])).
% 0.91/1.10  thf('5', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (l1_struct_0 @ X0)
% 0.91/1.10          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.91/1.10             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['3', '4'])).
% 0.91/1.10  thf('6', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.91/1.10           (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (l1_struct_0 @ X0))),
% 0.91/1.10      inference('sup+', [status(thm)], ['2', '5'])).
% 0.91/1.10  thf('7', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((v2_struct_0 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.91/1.10             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 0.91/1.10      inference('simplify', [status(thm)], ['6'])).
% 0.91/1.10  thf(t4_subset, axiom,
% 0.91/1.10    (![A:$i,B:$i,C:$i]:
% 0.91/1.10     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.91/1.10       ( m1_subset_1 @ A @ C ) ))).
% 0.91/1.10  thf('8', plain,
% 0.91/1.10      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.91/1.10         (~ (r2_hidden @ X2 @ X3)
% 0.91/1.10          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.91/1.10          | (m1_subset_1 @ X2 @ X4))),
% 0.91/1.10      inference('cnf', [status(esa)], [t4_subset])).
% 0.91/1.10  thf('9', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (~ (l1_struct_0 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | (m1_subset_1 @ X1 @ (k2_struct_0 @ X0))
% 0.91/1.10          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['7', '8'])).
% 0.91/1.10  thf('10', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.91/1.10          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.91/1.10             (k2_struct_0 @ X0))
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_struct_0 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['1', '9'])).
% 0.91/1.10  thf(t2_subset, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( m1_subset_1 @ A @ B ) =>
% 0.91/1.10       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.91/1.10  thf('11', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         ((r2_hidden @ X0 @ X1)
% 0.91/1.10          | (v1_xboole_0 @ X1)
% 0.91/1.10          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.91/1.10      inference('cnf', [status(esa)], [t2_subset])).
% 0.91/1.10  thf('12', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (l1_struct_0 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.91/1.10          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.91/1.10          | (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.91/1.10             (k2_struct_0 @ X0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['10', '11'])).
% 0.91/1.10  thf('13', plain,
% 0.91/1.10      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.91/1.10      inference('cnf', [status(esa)], [t2_mcart_1])).
% 0.91/1.10  thf('14', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (l1_struct_0 @ X0)
% 0.91/1.10          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.91/1.10             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['3', '4'])).
% 0.91/1.10  thf('15', plain,
% 0.91/1.10      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.91/1.10         (~ (r2_hidden @ X2 @ X3)
% 0.91/1.10          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.91/1.10          | (m1_subset_1 @ X2 @ X4))),
% 0.91/1.10      inference('cnf', [status(esa)], [t4_subset])).
% 0.91/1.10  thf('16', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.91/1.10          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['14', '15'])).
% 0.91/1.10  thf('17', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.91/1.10          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.91/1.10             (u1_struct_0 @ X0))
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['13', '16'])).
% 0.91/1.10  thf('18', plain,
% 0.91/1.10      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.91/1.10      inference('cnf', [status(esa)], [t2_mcart_1])).
% 0.91/1.10  thf('19', plain,
% 0.91/1.10      (![X11 : $i]:
% 0.91/1.10         ((m1_subset_1 @ (k2_struct_0 @ X11) @ 
% 0.91/1.10           (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.91/1.10          | ~ (l1_struct_0 @ X11))),
% 0.91/1.10      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.91/1.10  thf(d13_orders_2, axiom,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.91/1.10         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.91/1.10       ( ![B:$i]:
% 0.91/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.10           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 0.91/1.10  thf('20', plain,
% 0.91/1.10      (![X15 : $i, X16 : $i]:
% 0.91/1.10         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (u1_struct_0 @ X16)))
% 0.91/1.10          | ((k2_orders_2 @ X16 @ X15) = (a_2_1_orders_2 @ X16 @ X15))
% 0.91/1.10          | ~ (l1_orders_2 @ X16)
% 0.91/1.10          | ~ (v5_orders_2 @ X16)
% 0.91/1.10          | ~ (v4_orders_2 @ X16)
% 0.91/1.10          | ~ (v3_orders_2 @ X16)
% 0.91/1.10          | (v2_struct_0 @ X16))),
% 0.91/1.10      inference('cnf', [status(esa)], [d13_orders_2])).
% 0.91/1.10  thf('21', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (l1_struct_0 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 0.91/1.10              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['19', '20'])).
% 0.91/1.10  thf('22', plain,
% 0.91/1.10      (![X11 : $i]:
% 0.91/1.10         ((m1_subset_1 @ (k2_struct_0 @ X11) @ 
% 0.91/1.10           (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.91/1.10          | ~ (l1_struct_0 @ X11))),
% 0.91/1.10      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.91/1.10  thf(fraenkel_a_2_1_orders_2, axiom,
% 0.91/1.10    (![A:$i,B:$i,C:$i]:
% 0.91/1.10     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 0.91/1.10         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 0.91/1.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 0.91/1.10       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 0.91/1.10         ( ?[D:$i]:
% 0.91/1.10           ( ( ![E:$i]:
% 0.91/1.10               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 0.91/1.10                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 0.91/1.10             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 0.91/1.10  thf('23', plain,
% 0.91/1.10      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.91/1.10         (~ (l1_orders_2 @ X20)
% 0.91/1.10          | ~ (v5_orders_2 @ X20)
% 0.91/1.10          | ~ (v4_orders_2 @ X20)
% 0.91/1.10          | ~ (v3_orders_2 @ X20)
% 0.91/1.10          | (v2_struct_0 @ X20)
% 0.91/1.10          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.91/1.10          | ~ (m1_subset_1 @ X22 @ (u1_struct_0 @ X20))
% 0.91/1.10          | (r2_orders_2 @ X20 @ (sk_D @ X21 @ X20 @ X23) @ X22)
% 0.91/1.10          | ~ (r2_hidden @ X22 @ X21)
% 0.91/1.10          | ~ (r2_hidden @ X23 @ (a_2_1_orders_2 @ X20 @ X21)))),
% 0.91/1.10      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.91/1.10  thf('24', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.10         (~ (l1_struct_0 @ X0)
% 0.91/1.10          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.91/1.10          | ~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 0.91/1.10          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 0.91/1.10          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['22', '23'])).
% 0.91/1.10  thf('25', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.10         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.91/1.10          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 0.91/1.10          | ~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 0.91/1.10          | ~ (l1_struct_0 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['21', '24'])).
% 0.91/1.10  thf('26', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.10         (~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 0.91/1.10          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 0.91/1.10          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.91/1.10      inference('simplify', [status(thm)], ['25'])).
% 0.91/1.10  thf('27', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.91/1.10          | (r2_orders_2 @ X0 @ 
% 0.91/1.10             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.91/1.10              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.91/1.10             X1)
% 0.91/1.10          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['18', '26'])).
% 0.91/1.10  thf('28', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.91/1.10          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.91/1.10               (k2_struct_0 @ X0))
% 0.91/1.10          | (r2_orders_2 @ X0 @ 
% 0.91/1.10             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.91/1.10              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.91/1.10             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['17', '27'])).
% 0.91/1.10  thf('29', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((r2_orders_2 @ X0 @ 
% 0.91/1.10           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.91/1.10            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.91/1.10           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 0.91/1.10          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 0.91/1.10               (k2_struct_0 @ X0))
% 0.91/1.10          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0))),
% 0.91/1.10      inference('simplify', [status(thm)], ['28'])).
% 0.91/1.10  thf('30', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.91/1.10          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.91/1.10          | (r2_orders_2 @ X0 @ 
% 0.91/1.10             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.91/1.10              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.91/1.10             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['12', '29'])).
% 0.91/1.10  thf('31', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((r2_orders_2 @ X0 @ 
% 0.91/1.10           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.91/1.10            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.91/1.10           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.91/1.10          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.91/1.10      inference('simplify', [status(thm)], ['30'])).
% 0.91/1.10  thf('32', plain,
% 0.91/1.10      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.91/1.10      inference('cnf', [status(esa)], [t2_mcart_1])).
% 0.91/1.10  thf('33', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (l1_struct_0 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 0.91/1.10              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['19', '20'])).
% 0.91/1.10  thf('34', plain,
% 0.91/1.10      (![X11 : $i]:
% 0.91/1.10         ((m1_subset_1 @ (k2_struct_0 @ X11) @ 
% 0.91/1.10           (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.91/1.10          | ~ (l1_struct_0 @ X11))),
% 0.91/1.10      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.91/1.10  thf('35', plain,
% 0.91/1.10      (![X20 : $i, X21 : $i, X23 : $i]:
% 0.91/1.10         (~ (l1_orders_2 @ X20)
% 0.91/1.10          | ~ (v5_orders_2 @ X20)
% 0.91/1.10          | ~ (v4_orders_2 @ X20)
% 0.91/1.10          | ~ (v3_orders_2 @ X20)
% 0.91/1.10          | (v2_struct_0 @ X20)
% 0.91/1.10          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.91/1.10          | ((X23) = (sk_D @ X21 @ X20 @ X23))
% 0.91/1.10          | ~ (r2_hidden @ X23 @ (a_2_1_orders_2 @ X20 @ X21)))),
% 0.91/1.10      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.91/1.10  thf('36', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (~ (l1_struct_0 @ X0)
% 0.91/1.10          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.91/1.10          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['34', '35'])).
% 0.91/1.10  thf('37', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 0.91/1.10          | ~ (l1_struct_0 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['33', '36'])).
% 0.91/1.10  thf('38', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.91/1.10      inference('simplify', [status(thm)], ['37'])).
% 0.91/1.10  thf('39', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.91/1.10              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.91/1.10                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['32', '38'])).
% 0.91/1.10  thf('40', plain,
% 0.91/1.10      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.91/1.10      inference('cnf', [status(esa)], [t2_mcart_1])).
% 0.91/1.10  thf('41', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (l1_struct_0 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 0.91/1.10              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['19', '20'])).
% 0.91/1.10  thf('42', plain,
% 0.91/1.10      (![X11 : $i]:
% 0.91/1.10         ((m1_subset_1 @ (k2_struct_0 @ X11) @ 
% 0.91/1.10           (k1_zfmisc_1 @ (u1_struct_0 @ X11)))
% 0.91/1.10          | ~ (l1_struct_0 @ X11))),
% 0.91/1.10      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.91/1.10  thf('43', plain,
% 0.91/1.10      (![X20 : $i, X21 : $i, X23 : $i]:
% 0.91/1.10         (~ (l1_orders_2 @ X20)
% 0.91/1.10          | ~ (v5_orders_2 @ X20)
% 0.91/1.10          | ~ (v4_orders_2 @ X20)
% 0.91/1.10          | ~ (v3_orders_2 @ X20)
% 0.91/1.10          | (v2_struct_0 @ X20)
% 0.91/1.10          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.91/1.10          | (m1_subset_1 @ (sk_D @ X21 @ X20 @ X23) @ (u1_struct_0 @ X20))
% 0.91/1.10          | ~ (r2_hidden @ X23 @ (a_2_1_orders_2 @ X20 @ X21)))),
% 0.91/1.10      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 0.91/1.10  thf('44', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (~ (l1_struct_0 @ X0)
% 0.91/1.10          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.91/1.10          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 0.91/1.10             (u1_struct_0 @ X0))
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['42', '43'])).
% 0.91/1.10  thf('45', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 0.91/1.10             (u1_struct_0 @ X0))
% 0.91/1.10          | ~ (l1_struct_0 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['41', '44'])).
% 0.91/1.10  thf('46', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         ((m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 0.91/1.10           (u1_struct_0 @ X0))
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.91/1.10      inference('simplify', [status(thm)], ['45'])).
% 0.91/1.10  thf('47', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | (m1_subset_1 @ 
% 0.91/1.10             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.91/1.10              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.91/1.10             (u1_struct_0 @ X0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['40', '46'])).
% 0.91/1.10  thf(d10_orders_2, axiom,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( l1_orders_2 @ A ) =>
% 0.91/1.10       ( ![B:$i]:
% 0.91/1.10         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.10           ( ![C:$i]:
% 0.91/1.10             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.91/1.10               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 0.91/1.10                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 0.91/1.10  thf('48', plain,
% 0.91/1.10      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.91/1.10         (~ (m1_subset_1 @ X12 @ (u1_struct_0 @ X13))
% 0.91/1.10          | ~ (r2_orders_2 @ X13 @ X12 @ X14)
% 0.91/1.10          | ((X12) != (X14))
% 0.91/1.10          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13))
% 0.91/1.10          | ~ (l1_orders_2 @ X13))),
% 0.91/1.10      inference('cnf', [status(esa)], [d10_orders_2])).
% 0.91/1.10  thf('49', plain,
% 0.91/1.10      (![X13 : $i, X14 : $i]:
% 0.91/1.10         (~ (l1_orders_2 @ X13)
% 0.91/1.10          | ~ (r2_orders_2 @ X13 @ X14 @ X14)
% 0.91/1.10          | ~ (m1_subset_1 @ X14 @ (u1_struct_0 @ X13)))),
% 0.91/1.10      inference('simplify', [status(thm)], ['48'])).
% 0.91/1.10  thf('50', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (l1_struct_0 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.91/1.10          | ~ (r2_orders_2 @ X0 @ 
% 0.91/1.10               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.91/1.10                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.91/1.10               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.91/1.10                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 0.91/1.10          | ~ (l1_orders_2 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['47', '49'])).
% 0.91/1.10  thf('51', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (r2_orders_2 @ X0 @ 
% 0.91/1.10             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.91/1.10              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.91/1.10             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.91/1.10              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 0.91/1.10          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (l1_struct_0 @ X0))),
% 0.91/1.10      inference('simplify', [status(thm)], ['50'])).
% 0.91/1.10  thf('52', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (r2_orders_2 @ X0 @ 
% 0.91/1.10             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.91/1.10              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.91/1.10             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['39', '51'])).
% 0.91/1.10  thf('53', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.91/1.10          | ~ (l1_orders_2 @ X0)
% 0.91/1.10          | ~ (v5_orders_2 @ X0)
% 0.91/1.10          | ~ (v4_orders_2 @ X0)
% 0.91/1.10          | ~ (v3_orders_2 @ X0)
% 0.91/1.10          | (v2_struct_0 @ X0)
% 0.91/1.10          | ~ (l1_struct_0 @ X0)
% 0.91/1.10          | ~ (r2_orders_2 @ X0 @ 
% 0.91/1.10               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 0.91/1.10                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 0.91/1.11               (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 0.91/1.11      inference('simplify', [status(thm)], ['52'])).
% 0.91/1.11  thf('54', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.91/1.11          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.91/1.11          | (v2_struct_0 @ X0)
% 0.91/1.11          | ~ (v3_orders_2 @ X0)
% 0.91/1.11          | ~ (v4_orders_2 @ X0)
% 0.91/1.11          | ~ (v5_orders_2 @ X0)
% 0.91/1.11          | ~ (l1_orders_2 @ X0)
% 0.91/1.11          | ~ (l1_struct_0 @ X0)
% 0.91/1.11          | ~ (l1_struct_0 @ X0)
% 0.91/1.11          | (v2_struct_0 @ X0)
% 0.91/1.11          | ~ (v3_orders_2 @ X0)
% 0.91/1.11          | ~ (v4_orders_2 @ X0)
% 0.91/1.11          | ~ (v5_orders_2 @ X0)
% 0.91/1.11          | ~ (l1_orders_2 @ X0)
% 0.91/1.11          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['31', '53'])).
% 0.91/1.11  thf('55', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (~ (l1_struct_0 @ X0)
% 0.91/1.11          | ~ (l1_orders_2 @ X0)
% 0.91/1.11          | ~ (v5_orders_2 @ X0)
% 0.91/1.11          | ~ (v4_orders_2 @ X0)
% 0.91/1.11          | ~ (v3_orders_2 @ X0)
% 0.91/1.11          | (v2_struct_0 @ X0)
% 0.91/1.11          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.91/1.11          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 0.91/1.11      inference('simplify', [status(thm)], ['54'])).
% 0.91/1.11  thf('56', plain,
% 0.91/1.11      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('57', plain,
% 0.91/1.11      ((((k1_xboole_0) != (k1_xboole_0))
% 0.91/1.11        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.91/1.11        | (v2_struct_0 @ sk_A)
% 0.91/1.11        | ~ (v3_orders_2 @ sk_A)
% 0.91/1.11        | ~ (v4_orders_2 @ sk_A)
% 0.91/1.11        | ~ (v5_orders_2 @ sk_A)
% 0.91/1.11        | ~ (l1_orders_2 @ sk_A)
% 0.91/1.11        | ~ (l1_struct_0 @ sk_A))),
% 0.91/1.11      inference('sup-', [status(thm)], ['55', '56'])).
% 0.91/1.11  thf('58', plain, ((v3_orders_2 @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('59', plain, ((v4_orders_2 @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('60', plain, ((v5_orders_2 @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('61', plain, ((l1_orders_2 @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('62', plain, ((l1_orders_2 @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf(dt_l1_orders_2, axiom,
% 0.91/1.11    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.91/1.11  thf('63', plain,
% 0.91/1.11      (![X19 : $i]: ((l1_struct_0 @ X19) | ~ (l1_orders_2 @ X19))),
% 0.91/1.11      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.91/1.11  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 0.91/1.11      inference('sup-', [status(thm)], ['62', '63'])).
% 0.91/1.11  thf('65', plain,
% 0.91/1.11      ((((k1_xboole_0) != (k1_xboole_0))
% 0.91/1.11        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 0.91/1.11        | (v2_struct_0 @ sk_A))),
% 0.91/1.11      inference('demod', [status(thm)], ['57', '58', '59', '60', '61', '64'])).
% 0.91/1.11  thf('66', plain,
% 0.91/1.11      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 0.91/1.11      inference('simplify', [status(thm)], ['65'])).
% 0.91/1.11  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('68', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 0.91/1.11      inference('clc', [status(thm)], ['66', '67'])).
% 0.91/1.11  thf('69', plain,
% 0.91/1.11      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.91/1.11      inference('cnf', [status(esa)], [t2_mcart_1])).
% 0.91/1.11  thf('70', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         ((v2_struct_0 @ X0)
% 0.91/1.11          | ~ (v3_orders_2 @ X0)
% 0.91/1.11          | ~ (v4_orders_2 @ X0)
% 0.91/1.11          | ~ (v5_orders_2 @ X0)
% 0.91/1.11          | ~ (l1_orders_2 @ X0)
% 0.91/1.11          | ~ (l1_struct_0 @ X0)
% 0.91/1.11          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.91/1.11             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 0.91/1.11      inference('simplify', [status(thm)], ['6'])).
% 0.91/1.11  thf(t5_subset, axiom,
% 0.91/1.11    (![A:$i,B:$i,C:$i]:
% 0.91/1.11     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.91/1.11          ( v1_xboole_0 @ C ) ) ))).
% 0.91/1.11  thf('71', plain,
% 0.91/1.11      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.91/1.11         (~ (r2_hidden @ X5 @ X6)
% 0.91/1.11          | ~ (v1_xboole_0 @ X7)
% 0.91/1.11          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.91/1.11      inference('cnf', [status(esa)], [t5_subset])).
% 0.91/1.11  thf('72', plain,
% 0.91/1.11      (![X0 : $i, X1 : $i]:
% 0.91/1.11         (~ (l1_struct_0 @ X0)
% 0.91/1.11          | ~ (l1_orders_2 @ X0)
% 0.91/1.11          | ~ (v5_orders_2 @ X0)
% 0.91/1.11          | ~ (v4_orders_2 @ X0)
% 0.91/1.11          | ~ (v3_orders_2 @ X0)
% 0.91/1.11          | (v2_struct_0 @ X0)
% 0.91/1.11          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.91/1.11          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 0.91/1.11      inference('sup-', [status(thm)], ['70', '71'])).
% 0.91/1.11  thf('73', plain,
% 0.91/1.11      (![X0 : $i]:
% 0.91/1.11         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 0.91/1.11          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 0.91/1.11          | (v2_struct_0 @ X0)
% 0.91/1.11          | ~ (v3_orders_2 @ X0)
% 0.91/1.11          | ~ (v4_orders_2 @ X0)
% 0.91/1.11          | ~ (v5_orders_2 @ X0)
% 0.91/1.11          | ~ (l1_orders_2 @ X0)
% 0.91/1.11          | ~ (l1_struct_0 @ X0))),
% 0.91/1.11      inference('sup-', [status(thm)], ['69', '72'])).
% 0.91/1.11  thf('74', plain,
% 0.91/1.11      ((~ (l1_struct_0 @ sk_A)
% 0.91/1.11        | ~ (l1_orders_2 @ sk_A)
% 0.91/1.11        | ~ (v5_orders_2 @ sk_A)
% 0.91/1.11        | ~ (v4_orders_2 @ sk_A)
% 0.91/1.11        | ~ (v3_orders_2 @ sk_A)
% 0.91/1.11        | (v2_struct_0 @ sk_A)
% 0.91/1.11        | ((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0)))),
% 0.91/1.11      inference('sup-', [status(thm)], ['68', '73'])).
% 0.91/1.11  thf('75', plain, ((l1_struct_0 @ sk_A)),
% 0.91/1.11      inference('sup-', [status(thm)], ['62', '63'])).
% 0.91/1.11  thf('76', plain, ((l1_orders_2 @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('77', plain, ((v5_orders_2 @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('78', plain, ((v4_orders_2 @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('79', plain, ((v3_orders_2 @ sk_A)),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('80', plain,
% 0.91/1.11      (((v2_struct_0 @ sk_A)
% 0.91/1.11        | ((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0)))),
% 0.91/1.11      inference('demod', [status(thm)], ['74', '75', '76', '77', '78', '79'])).
% 0.91/1.11  thf('81', plain,
% 0.91/1.11      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 0.91/1.11      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.11  thf('82', plain, ((v2_struct_0 @ sk_A)),
% 0.91/1.11      inference('simplify_reflect-', [status(thm)], ['80', '81'])).
% 0.91/1.11  thf('83', plain, ($false), inference('demod', [status(thm)], ['0', '82'])).
% 0.91/1.11  
% 0.91/1.11  % SZS output end Refutation
% 0.91/1.11  
% 0.91/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
