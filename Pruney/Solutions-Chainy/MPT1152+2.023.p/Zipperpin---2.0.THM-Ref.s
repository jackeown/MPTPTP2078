%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aWgtMnP7AJ

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:45 EST 2020

% Result     : Theorem 1.03s
% Output     : Refutation 1.03s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 179 expanded)
%              Number of leaves         :   33 (  68 expanded)
%              Depth                    :   19
%              Number of atoms          : 1778 (2644 expanded)
%              Number of equality atoms :   54 (  92 expanded)
%              Maximal formula depth    :   24 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r1_orders_2_type,type,(
    r1_orders_2: $i > $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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

thf(t3_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_mcart_1])).

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
    inference(cnf,[status(esa)],[t3_mcart_1])).

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
    inference(cnf,[status(esa)],[t3_mcart_1])).

thf('19',plain,(
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

thf('20',plain,(
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

thf('23',plain,(
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
    inference(cnf,[status(esa)],[t3_mcart_1])).

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
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('35',plain,(
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
    inference(cnf,[status(esa)],[t3_mcart_1])).

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
    ! [X12: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X12 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X12 ) ) )
      | ~ ( l1_struct_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('43',plain,(
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( u1_struct_0 @ X14 ) )
      | ~ ( r2_orders_2 @ X14 @ X13 @ X15 )
      | ( X13 != X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) )
      | ~ ( l1_orders_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_orders_2])).

thf('49',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( l1_orders_2 @ X14 )
      | ~ ( r2_orders_2 @ X14 @ X15 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( u1_struct_0 @ X14 ) ) ) ),
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
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_orders_2 @ X20 ) ) ),
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
    ! [X11: $i] :
      ( ( ( k2_struct_0 @ X11 )
        = ( u1_struct_0 @ X11 ) )
      | ~ ( l1_struct_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('70',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_mcart_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('72',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( ( k2_orders_2 @ X0 @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ~ ( l1_struct_0 @ sk_A )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','76'])).

thf('78',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['62','63'])).

thf('79',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( v2_struct_0 @ sk_A )
    | ( ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['77','78','79','80','81','82'])).

thf('84',plain,(
    ( k2_orders_2 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['83','84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['0','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aWgtMnP7AJ
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:43:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 1.03/1.21  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.03/1.21  % Solved by: fo/fo7.sh
% 1.03/1.21  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.03/1.21  % done 705 iterations in 0.753s
% 1.03/1.21  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.03/1.21  % SZS output start Refutation
% 1.03/1.21  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.03/1.21  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 1.03/1.21  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.03/1.21  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.03/1.21  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.03/1.21  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 1.03/1.21  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.03/1.21  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 1.03/1.21  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 1.03/1.21  thf(sk_A_type, type, sk_A: $i).
% 1.03/1.21  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 1.03/1.21  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 1.03/1.21  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.03/1.21  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.03/1.21  thf(r1_orders_2_type, type, r1_orders_2: $i > $i > $i > $o).
% 1.03/1.21  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 1.03/1.21  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 1.03/1.21  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.03/1.21  thf(sk_B_type, type, sk_B: $i > $i).
% 1.03/1.21  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.03/1.21  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.03/1.21  thf(t46_orders_2, conjecture,
% 1.03/1.21    (![A:$i]:
% 1.03/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.03/1.21         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.03/1.21       ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ))).
% 1.03/1.21  thf(zf_stmt_0, negated_conjecture,
% 1.03/1.21    (~( ![A:$i]:
% 1.03/1.21        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.03/1.21            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.03/1.21          ( ( k2_orders_2 @ A @ ( k2_struct_0 @ A ) ) = ( k1_xboole_0 ) ) ) )),
% 1.03/1.21    inference('cnf.neg', [status(esa)], [t46_orders_2])).
% 1.03/1.21  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf(t3_mcart_1, axiom,
% 1.03/1.21    (![A:$i]:
% 1.03/1.21     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.03/1.21          ( ![B:$i]:
% 1.03/1.21            ( ~( ( r2_hidden @ B @ A ) & 
% 1.03/1.21                 ( ![C:$i,D:$i]:
% 1.03/1.21                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ B ) ) =>
% 1.03/1.21                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 1.03/1.21  thf('1', plain,
% 1.03/1.21      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 1.03/1.21      inference('cnf', [status(esa)], [t3_mcart_1])).
% 1.03/1.21  thf(d3_struct_0, axiom,
% 1.03/1.21    (![A:$i]:
% 1.03/1.21     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 1.03/1.21  thf('2', plain,
% 1.03/1.21      (![X11 : $i]:
% 1.03/1.21         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 1.03/1.21      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.21  thf(dt_k2_struct_0, axiom,
% 1.03/1.21    (![A:$i]:
% 1.03/1.21     ( ( l1_struct_0 @ A ) =>
% 1.03/1.21       ( m1_subset_1 @
% 1.03/1.21         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.03/1.21  thf('3', plain,
% 1.03/1.21      (![X12 : $i]:
% 1.03/1.21         ((m1_subset_1 @ (k2_struct_0 @ X12) @ 
% 1.03/1.21           (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.03/1.21          | ~ (l1_struct_0 @ X12))),
% 1.03/1.21      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.03/1.21  thf(dt_k2_orders_2, axiom,
% 1.03/1.21    (![A:$i,B:$i]:
% 1.03/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.03/1.21         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 1.03/1.21         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 1.03/1.21       ( m1_subset_1 @
% 1.03/1.21         ( k2_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.03/1.21  thf('4', plain,
% 1.03/1.21      (![X18 : $i, X19 : $i]:
% 1.03/1.21         (~ (l1_orders_2 @ X18)
% 1.03/1.21          | ~ (v5_orders_2 @ X18)
% 1.03/1.21          | ~ (v4_orders_2 @ X18)
% 1.03/1.21          | ~ (v3_orders_2 @ X18)
% 1.03/1.21          | (v2_struct_0 @ X18)
% 1.03/1.21          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 1.03/1.21          | (m1_subset_1 @ (k2_orders_2 @ X18 @ X19) @ 
% 1.03/1.21             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 1.03/1.21      inference('cnf', [status(esa)], [dt_k2_orders_2])).
% 1.03/1.21  thf('5', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (~ (l1_struct_0 @ X0)
% 1.03/1.21          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.03/1.21             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0))),
% 1.03/1.21      inference('sup-', [status(thm)], ['3', '4'])).
% 1.03/1.21  thf('6', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         ((m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.03/1.21           (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_struct_0 @ X0))),
% 1.03/1.21      inference('sup+', [status(thm)], ['2', '5'])).
% 1.03/1.21  thf('7', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         ((v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.03/1.21             (k1_zfmisc_1 @ (k2_struct_0 @ X0))))),
% 1.03/1.21      inference('simplify', [status(thm)], ['6'])).
% 1.03/1.21  thf(t4_subset, axiom,
% 1.03/1.21    (![A:$i,B:$i,C:$i]:
% 1.03/1.21     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.03/1.21       ( m1_subset_1 @ A @ C ) ))).
% 1.03/1.21  thf('8', plain,
% 1.03/1.21      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.03/1.21         (~ (r2_hidden @ X2 @ X3)
% 1.03/1.21          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.03/1.21          | (m1_subset_1 @ X2 @ X4))),
% 1.03/1.21      inference('cnf', [status(esa)], [t4_subset])).
% 1.03/1.21  thf('9', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i]:
% 1.03/1.21         (~ (l1_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | (m1_subset_1 @ X1 @ (k2_struct_0 @ X0))
% 1.03/1.21          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 1.03/1.21      inference('sup-', [status(thm)], ['7', '8'])).
% 1.03/1.21  thf('10', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.03/1.21          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 1.03/1.21             (k2_struct_0 @ X0))
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_struct_0 @ X0))),
% 1.03/1.21      inference('sup-', [status(thm)], ['1', '9'])).
% 1.03/1.21  thf(t2_subset, axiom,
% 1.03/1.21    (![A:$i,B:$i]:
% 1.03/1.21     ( ( m1_subset_1 @ A @ B ) =>
% 1.03/1.21       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.03/1.21  thf('11', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i]:
% 1.03/1.21         ((r2_hidden @ X0 @ X1)
% 1.03/1.21          | (v1_xboole_0 @ X1)
% 1.03/1.21          | ~ (m1_subset_1 @ X0 @ X1))),
% 1.03/1.21      inference('cnf', [status(esa)], [t2_subset])).
% 1.03/1.21  thf('12', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (~ (l1_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.03/1.21          | (v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.03/1.21          | (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 1.03/1.21             (k2_struct_0 @ X0)))),
% 1.03/1.21      inference('sup-', [status(thm)], ['10', '11'])).
% 1.03/1.21  thf('13', plain,
% 1.03/1.21      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 1.03/1.21      inference('cnf', [status(esa)], [t3_mcart_1])).
% 1.03/1.21  thf('14', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (~ (l1_struct_0 @ X0)
% 1.03/1.21          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.03/1.21             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0))),
% 1.03/1.21      inference('sup-', [status(thm)], ['3', '4'])).
% 1.03/1.21  thf('15', plain,
% 1.03/1.21      (![X2 : $i, X3 : $i, X4 : $i]:
% 1.03/1.21         (~ (r2_hidden @ X2 @ X3)
% 1.03/1.21          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 1.03/1.21          | (m1_subset_1 @ X2 @ X4))),
% 1.03/1.21      inference('cnf', [status(esa)], [t4_subset])).
% 1.03/1.21  thf('16', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i]:
% 1.03/1.21         (~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 1.03/1.21          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 1.03/1.21      inference('sup-', [status(thm)], ['14', '15'])).
% 1.03/1.21  thf('17', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.03/1.21          | (m1_subset_1 @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 1.03/1.21             (u1_struct_0 @ X0))
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0))),
% 1.03/1.21      inference('sup-', [status(thm)], ['13', '16'])).
% 1.03/1.21  thf('18', plain,
% 1.03/1.21      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 1.03/1.21      inference('cnf', [status(esa)], [t3_mcart_1])).
% 1.03/1.21  thf('19', plain,
% 1.03/1.21      (![X12 : $i]:
% 1.03/1.21         ((m1_subset_1 @ (k2_struct_0 @ X12) @ 
% 1.03/1.21           (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.03/1.21          | ~ (l1_struct_0 @ X12))),
% 1.03/1.21      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.03/1.21  thf(d13_orders_2, axiom,
% 1.03/1.21    (![A:$i]:
% 1.03/1.21     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 1.03/1.21         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 1.03/1.21       ( ![B:$i]:
% 1.03/1.21         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.03/1.21           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 1.03/1.21  thf('20', plain,
% 1.03/1.21      (![X16 : $i, X17 : $i]:
% 1.03/1.21         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (u1_struct_0 @ X17)))
% 1.03/1.21          | ((k2_orders_2 @ X17 @ X16) = (a_2_1_orders_2 @ X17 @ X16))
% 1.03/1.21          | ~ (l1_orders_2 @ X17)
% 1.03/1.21          | ~ (v5_orders_2 @ X17)
% 1.03/1.21          | ~ (v4_orders_2 @ X17)
% 1.03/1.21          | ~ (v3_orders_2 @ X17)
% 1.03/1.21          | (v2_struct_0 @ X17))),
% 1.03/1.21      inference('cnf', [status(esa)], [d13_orders_2])).
% 1.03/1.21  thf('21', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (~ (l1_struct_0 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 1.03/1.21              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 1.03/1.21      inference('sup-', [status(thm)], ['19', '20'])).
% 1.03/1.21  thf('22', plain,
% 1.03/1.21      (![X12 : $i]:
% 1.03/1.21         ((m1_subset_1 @ (k2_struct_0 @ X12) @ 
% 1.03/1.21           (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.03/1.21          | ~ (l1_struct_0 @ X12))),
% 1.03/1.21      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.03/1.21  thf(fraenkel_a_2_1_orders_2, axiom,
% 1.03/1.21    (![A:$i,B:$i,C:$i]:
% 1.03/1.21     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 1.03/1.21         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 1.03/1.21         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 1.03/1.21       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 1.03/1.21         ( ?[D:$i]:
% 1.03/1.21           ( ( ![E:$i]:
% 1.03/1.21               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 1.03/1.21                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 1.03/1.21             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 1.03/1.21  thf('23', plain,
% 1.03/1.21      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 1.03/1.21         (~ (l1_orders_2 @ X21)
% 1.03/1.21          | ~ (v5_orders_2 @ X21)
% 1.03/1.21          | ~ (v4_orders_2 @ X21)
% 1.03/1.21          | ~ (v3_orders_2 @ X21)
% 1.03/1.21          | (v2_struct_0 @ X21)
% 1.03/1.21          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.03/1.21          | ~ (m1_subset_1 @ X23 @ (u1_struct_0 @ X21))
% 1.03/1.21          | (r2_orders_2 @ X21 @ (sk_D @ X22 @ X21 @ X24) @ X23)
% 1.03/1.21          | ~ (r2_hidden @ X23 @ X22)
% 1.03/1.21          | ~ (r2_hidden @ X24 @ (a_2_1_orders_2 @ X21 @ X22)))),
% 1.03/1.21      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 1.03/1.21  thf('24', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.21         (~ (l1_struct_0 @ X0)
% 1.03/1.21          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 1.03/1.21          | ~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 1.03/1.21          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 1.03/1.21          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0))),
% 1.03/1.21      inference('sup-', [status(thm)], ['22', '23'])).
% 1.03/1.21  thf('25', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.21         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.03/1.21          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 1.03/1.21          | ~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 1.03/1.21          | ~ (l1_struct_0 @ X0))),
% 1.03/1.21      inference('sup-', [status(thm)], ['21', '24'])).
% 1.03/1.21  thf('26', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.03/1.21         (~ (r2_hidden @ X2 @ (k2_struct_0 @ X0))
% 1.03/1.21          | (r2_orders_2 @ X0 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ X2)
% 1.03/1.21          | ~ (m1_subset_1 @ X2 @ (u1_struct_0 @ X0))
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 1.03/1.21      inference('simplify', [status(thm)], ['25'])).
% 1.03/1.21  thf('27', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i]:
% 1.03/1.21         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 1.03/1.21          | (r2_orders_2 @ X0 @ 
% 1.03/1.21             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.03/1.21              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 1.03/1.21             X1)
% 1.03/1.21          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0)))),
% 1.03/1.21      inference('sup-', [status(thm)], ['18', '26'])).
% 1.03/1.21  thf('28', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.03/1.21          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 1.03/1.21               (k2_struct_0 @ X0))
% 1.03/1.21          | (r2_orders_2 @ X0 @ 
% 1.03/1.21             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.03/1.21              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 1.03/1.21             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 1.03/1.21      inference('sup-', [status(thm)], ['17', '27'])).
% 1.03/1.21  thf('29', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         ((r2_orders_2 @ X0 @ 
% 1.03/1.21           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.03/1.21            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 1.03/1.21           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 1.03/1.21          | ~ (r2_hidden @ (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))) @ 
% 1.03/1.21               (k2_struct_0 @ X0))
% 1.03/1.21          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0))),
% 1.03/1.21      inference('simplify', [status(thm)], ['28'])).
% 1.03/1.21  thf('30', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.03/1.21          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.03/1.21          | (r2_orders_2 @ X0 @ 
% 1.03/1.21             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.03/1.21              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 1.03/1.21             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 1.03/1.21      inference('sup-', [status(thm)], ['12', '29'])).
% 1.03/1.21  thf('31', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         ((r2_orders_2 @ X0 @ 
% 1.03/1.21           (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.03/1.21            (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 1.03/1.21           (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.03/1.21          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 1.03/1.21      inference('simplify', [status(thm)], ['30'])).
% 1.03/1.21  thf('32', plain,
% 1.03/1.21      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 1.03/1.21      inference('cnf', [status(esa)], [t3_mcart_1])).
% 1.03/1.21  thf('33', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (~ (l1_struct_0 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 1.03/1.21              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 1.03/1.21      inference('sup-', [status(thm)], ['19', '20'])).
% 1.03/1.21  thf('34', plain,
% 1.03/1.21      (![X12 : $i]:
% 1.03/1.21         ((m1_subset_1 @ (k2_struct_0 @ X12) @ 
% 1.03/1.21           (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.03/1.21          | ~ (l1_struct_0 @ X12))),
% 1.03/1.21      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.03/1.21  thf('35', plain,
% 1.03/1.21      (![X21 : $i, X22 : $i, X24 : $i]:
% 1.03/1.21         (~ (l1_orders_2 @ X21)
% 1.03/1.21          | ~ (v5_orders_2 @ X21)
% 1.03/1.21          | ~ (v4_orders_2 @ X21)
% 1.03/1.21          | ~ (v3_orders_2 @ X21)
% 1.03/1.21          | (v2_struct_0 @ X21)
% 1.03/1.21          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.03/1.21          | ((X24) = (sk_D @ X22 @ X21 @ X24))
% 1.03/1.21          | ~ (r2_hidden @ X24 @ (a_2_1_orders_2 @ X21 @ X22)))),
% 1.03/1.21      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 1.03/1.21  thf('36', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i]:
% 1.03/1.21         (~ (l1_struct_0 @ X0)
% 1.03/1.21          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 1.03/1.21          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0))),
% 1.03/1.21      inference('sup-', [status(thm)], ['34', '35'])).
% 1.03/1.21  thf('37', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i]:
% 1.03/1.21         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 1.03/1.21          | ~ (l1_struct_0 @ X0))),
% 1.03/1.21      inference('sup-', [status(thm)], ['33', '36'])).
% 1.03/1.21  thf('38', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i]:
% 1.03/1.21         (((X1) = (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1))
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 1.03/1.21      inference('simplify', [status(thm)], ['37'])).
% 1.03/1.21  thf('39', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | ((sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 1.03/1.21              = (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.03/1.21                 (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))))),
% 1.03/1.21      inference('sup-', [status(thm)], ['32', '38'])).
% 1.03/1.21  thf('40', plain,
% 1.03/1.21      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 1.03/1.21      inference('cnf', [status(esa)], [t3_mcart_1])).
% 1.03/1.21  thf('41', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (~ (l1_struct_0 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0))
% 1.03/1.21              = (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 1.03/1.21      inference('sup-', [status(thm)], ['19', '20'])).
% 1.03/1.21  thf('42', plain,
% 1.03/1.21      (![X12 : $i]:
% 1.03/1.21         ((m1_subset_1 @ (k2_struct_0 @ X12) @ 
% 1.03/1.21           (k1_zfmisc_1 @ (u1_struct_0 @ X12)))
% 1.03/1.21          | ~ (l1_struct_0 @ X12))),
% 1.03/1.21      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.03/1.21  thf('43', plain,
% 1.03/1.21      (![X21 : $i, X22 : $i, X24 : $i]:
% 1.03/1.21         (~ (l1_orders_2 @ X21)
% 1.03/1.21          | ~ (v5_orders_2 @ X21)
% 1.03/1.21          | ~ (v4_orders_2 @ X21)
% 1.03/1.21          | ~ (v3_orders_2 @ X21)
% 1.03/1.21          | (v2_struct_0 @ X21)
% 1.03/1.21          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (u1_struct_0 @ X21)))
% 1.03/1.21          | (m1_subset_1 @ (sk_D @ X22 @ X21 @ X24) @ (u1_struct_0 @ X21))
% 1.03/1.21          | ~ (r2_hidden @ X24 @ (a_2_1_orders_2 @ X21 @ X22)))),
% 1.03/1.21      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 1.03/1.21  thf('44', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i]:
% 1.03/1.21         (~ (l1_struct_0 @ X0)
% 1.03/1.21          | ~ (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 1.03/1.21          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 1.03/1.21             (u1_struct_0 @ X0))
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0))),
% 1.03/1.21      inference('sup-', [status(thm)], ['42', '43'])).
% 1.03/1.21  thf('45', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i]:
% 1.03/1.21         (~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | (m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 1.03/1.21             (u1_struct_0 @ X0))
% 1.03/1.21          | ~ (l1_struct_0 @ X0))),
% 1.03/1.21      inference('sup-', [status(thm)], ['41', '44'])).
% 1.03/1.21  thf('46', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i]:
% 1.03/1.21         ((m1_subset_1 @ (sk_D @ (k2_struct_0 @ X0) @ X0 @ X1) @ 
% 1.03/1.21           (u1_struct_0 @ X0))
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 1.03/1.21      inference('simplify', [status(thm)], ['45'])).
% 1.03/1.21  thf('47', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | (m1_subset_1 @ 
% 1.03/1.21             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.03/1.21              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 1.03/1.21             (u1_struct_0 @ X0)))),
% 1.03/1.21      inference('sup-', [status(thm)], ['40', '46'])).
% 1.03/1.21  thf(d10_orders_2, axiom,
% 1.03/1.21    (![A:$i]:
% 1.03/1.21     ( ( l1_orders_2 @ A ) =>
% 1.03/1.21       ( ![B:$i]:
% 1.03/1.21         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 1.03/1.21           ( ![C:$i]:
% 1.03/1.21             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 1.03/1.21               ( ( r2_orders_2 @ A @ B @ C ) <=>
% 1.03/1.21                 ( ( r1_orders_2 @ A @ B @ C ) & ( ( B ) != ( C ) ) ) ) ) ) ) ) ))).
% 1.03/1.21  thf('48', plain,
% 1.03/1.21      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.03/1.21         (~ (m1_subset_1 @ X13 @ (u1_struct_0 @ X14))
% 1.03/1.21          | ~ (r2_orders_2 @ X14 @ X13 @ X15)
% 1.03/1.21          | ((X13) != (X15))
% 1.03/1.21          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14))
% 1.03/1.21          | ~ (l1_orders_2 @ X14))),
% 1.03/1.21      inference('cnf', [status(esa)], [d10_orders_2])).
% 1.03/1.21  thf('49', plain,
% 1.03/1.21      (![X14 : $i, X15 : $i]:
% 1.03/1.21         (~ (l1_orders_2 @ X14)
% 1.03/1.21          | ~ (r2_orders_2 @ X14 @ X15 @ X15)
% 1.03/1.21          | ~ (m1_subset_1 @ X15 @ (u1_struct_0 @ X14)))),
% 1.03/1.21      inference('simplify', [status(thm)], ['48'])).
% 1.03/1.21  thf('50', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (~ (l1_struct_0 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.03/1.21          | ~ (r2_orders_2 @ X0 @ 
% 1.03/1.21               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.03/1.21                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 1.03/1.21               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.03/1.21                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 1.03/1.21          | ~ (l1_orders_2 @ X0))),
% 1.03/1.21      inference('sup-', [status(thm)], ['47', '49'])).
% 1.03/1.21  thf('51', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (~ (r2_orders_2 @ X0 @ 
% 1.03/1.21             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.03/1.21              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 1.03/1.21             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.03/1.21              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))
% 1.03/1.21          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_struct_0 @ X0))),
% 1.03/1.21      inference('simplify', [status(thm)], ['50'])).
% 1.03/1.21  thf('52', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (~ (r2_orders_2 @ X0 @ 
% 1.03/1.21             (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.03/1.21              (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 1.03/1.21             (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 1.03/1.21      inference('sup-', [status(thm)], ['39', '51'])).
% 1.03/1.21  thf('53', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | ~ (r2_orders_2 @ X0 @ 
% 1.03/1.21               (sk_D @ (k2_struct_0 @ X0) @ X0 @ 
% 1.03/1.21                (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))) @ 
% 1.03/1.21               (sk_B @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)))))),
% 1.03/1.21      inference('simplify', [status(thm)], ['52'])).
% 1.03/1.21  thf('54', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         ((v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.03/1.21          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 1.03/1.21      inference('sup-', [status(thm)], ['31', '53'])).
% 1.03/1.21  thf('55', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (~ (l1_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.03/1.21          | (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 1.03/1.21      inference('simplify', [status(thm)], ['54'])).
% 1.03/1.21  thf('56', plain,
% 1.03/1.21      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('57', plain,
% 1.03/1.21      ((((k1_xboole_0) != (k1_xboole_0))
% 1.03/1.21        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.03/1.21        | (v2_struct_0 @ sk_A)
% 1.03/1.21        | ~ (v3_orders_2 @ sk_A)
% 1.03/1.21        | ~ (v4_orders_2 @ sk_A)
% 1.03/1.21        | ~ (v5_orders_2 @ sk_A)
% 1.03/1.21        | ~ (l1_orders_2 @ sk_A)
% 1.03/1.21        | ~ (l1_struct_0 @ sk_A))),
% 1.03/1.21      inference('sup-', [status(thm)], ['55', '56'])).
% 1.03/1.21  thf('58', plain, ((v3_orders_2 @ sk_A)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('59', plain, ((v4_orders_2 @ sk_A)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('60', plain, ((v5_orders_2 @ sk_A)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('61', plain, ((l1_orders_2 @ sk_A)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('62', plain, ((l1_orders_2 @ sk_A)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf(dt_l1_orders_2, axiom,
% 1.03/1.21    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 1.03/1.21  thf('63', plain,
% 1.03/1.21      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_orders_2 @ X20))),
% 1.03/1.21      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 1.03/1.21  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 1.03/1.21      inference('sup-', [status(thm)], ['62', '63'])).
% 1.03/1.21  thf('65', plain,
% 1.03/1.21      ((((k1_xboole_0) != (k1_xboole_0))
% 1.03/1.21        | (v1_xboole_0 @ (k2_struct_0 @ sk_A))
% 1.03/1.21        | (v2_struct_0 @ sk_A))),
% 1.03/1.21      inference('demod', [status(thm)], ['57', '58', '59', '60', '61', '64'])).
% 1.03/1.21  thf('66', plain,
% 1.03/1.21      (((v2_struct_0 @ sk_A) | (v1_xboole_0 @ (k2_struct_0 @ sk_A)))),
% 1.03/1.21      inference('simplify', [status(thm)], ['65'])).
% 1.03/1.21  thf('67', plain, (~ (v2_struct_0 @ sk_A)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('68', plain, ((v1_xboole_0 @ (k2_struct_0 @ sk_A))),
% 1.03/1.21      inference('clc', [status(thm)], ['66', '67'])).
% 1.03/1.21  thf('69', plain,
% 1.03/1.21      (![X11 : $i]:
% 1.03/1.21         (((k2_struct_0 @ X11) = (u1_struct_0 @ X11)) | ~ (l1_struct_0 @ X11))),
% 1.03/1.21      inference('cnf', [status(esa)], [d3_struct_0])).
% 1.03/1.21  thf('70', plain,
% 1.03/1.21      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 1.03/1.21      inference('cnf', [status(esa)], [t3_mcart_1])).
% 1.03/1.21  thf('71', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (~ (l1_struct_0 @ X0)
% 1.03/1.21          | (m1_subset_1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) @ 
% 1.03/1.21             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0))),
% 1.03/1.21      inference('sup-', [status(thm)], ['3', '4'])).
% 1.03/1.21  thf(t5_subset, axiom,
% 1.03/1.21    (![A:$i,B:$i,C:$i]:
% 1.03/1.21     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.03/1.21          ( v1_xboole_0 @ C ) ) ))).
% 1.03/1.21  thf('72', plain,
% 1.03/1.21      (![X5 : $i, X6 : $i, X7 : $i]:
% 1.03/1.21         (~ (r2_hidden @ X5 @ X6)
% 1.03/1.21          | ~ (v1_xboole_0 @ X7)
% 1.03/1.21          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.03/1.21      inference('cnf', [status(esa)], [t5_subset])).
% 1.03/1.21  thf('73', plain,
% 1.03/1.21      (![X0 : $i, X1 : $i]:
% 1.03/1.21         (~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.03/1.21          | ~ (r2_hidden @ X1 @ (k2_orders_2 @ X0 @ (k2_struct_0 @ X0))))),
% 1.03/1.21      inference('sup-', [status(thm)], ['71', '72'])).
% 1.03/1.21  thf('74', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.03/1.21          | ~ (v1_xboole_0 @ (u1_struct_0 @ X0))
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0))),
% 1.03/1.21      inference('sup-', [status(thm)], ['70', '73'])).
% 1.03/1.21  thf('75', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (~ (v1_xboole_0 @ (k2_struct_0 @ X0))
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | ((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0)))),
% 1.03/1.21      inference('sup-', [status(thm)], ['69', '74'])).
% 1.03/1.21  thf('76', plain,
% 1.03/1.21      (![X0 : $i]:
% 1.03/1.21         (((k2_orders_2 @ X0 @ (k2_struct_0 @ X0)) = (k1_xboole_0))
% 1.03/1.21          | (v2_struct_0 @ X0)
% 1.03/1.21          | ~ (v3_orders_2 @ X0)
% 1.03/1.21          | ~ (v4_orders_2 @ X0)
% 1.03/1.21          | ~ (v5_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_orders_2 @ X0)
% 1.03/1.21          | ~ (l1_struct_0 @ X0)
% 1.03/1.21          | ~ (v1_xboole_0 @ (k2_struct_0 @ X0)))),
% 1.03/1.21      inference('simplify', [status(thm)], ['75'])).
% 1.03/1.21  thf('77', plain,
% 1.03/1.21      ((~ (l1_struct_0 @ sk_A)
% 1.03/1.21        | ~ (l1_orders_2 @ sk_A)
% 1.03/1.21        | ~ (v5_orders_2 @ sk_A)
% 1.03/1.21        | ~ (v4_orders_2 @ sk_A)
% 1.03/1.21        | ~ (v3_orders_2 @ sk_A)
% 1.03/1.21        | (v2_struct_0 @ sk_A)
% 1.03/1.21        | ((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0)))),
% 1.03/1.21      inference('sup-', [status(thm)], ['68', '76'])).
% 1.03/1.21  thf('78', plain, ((l1_struct_0 @ sk_A)),
% 1.03/1.21      inference('sup-', [status(thm)], ['62', '63'])).
% 1.03/1.21  thf('79', plain, ((l1_orders_2 @ sk_A)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('80', plain, ((v5_orders_2 @ sk_A)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('81', plain, ((v4_orders_2 @ sk_A)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('82', plain, ((v3_orders_2 @ sk_A)),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('83', plain,
% 1.03/1.21      (((v2_struct_0 @ sk_A)
% 1.03/1.21        | ((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) = (k1_xboole_0)))),
% 1.03/1.21      inference('demod', [status(thm)], ['77', '78', '79', '80', '81', '82'])).
% 1.03/1.21  thf('84', plain,
% 1.03/1.21      (((k2_orders_2 @ sk_A @ (k2_struct_0 @ sk_A)) != (k1_xboole_0))),
% 1.03/1.21      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.03/1.21  thf('85', plain, ((v2_struct_0 @ sk_A)),
% 1.03/1.21      inference('simplify_reflect-', [status(thm)], ['83', '84'])).
% 1.03/1.21  thf('86', plain, ($false), inference('demod', [status(thm)], ['0', '85'])).
% 1.03/1.21  
% 1.03/1.21  % SZS output end Refutation
% 1.03/1.21  
% 1.03/1.22  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
