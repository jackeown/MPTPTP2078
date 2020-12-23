%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ik3MKXjSBb

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:41 EST 2020

% Result     : Theorem 6.97s
% Output     : Refutation 6.97s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 109 expanded)
%              Number of leaves         :   31 (  46 expanded)
%              Depth                    :   18
%              Number of atoms          :  761 (1040 expanded)
%              Number of equality atoms :   20 (  33 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(r2_orders_2_type,type,(
    r2_orders_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(a_2_1_orders_2_type,type,(
    a_2_1_orders_2: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t45_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ( ( k2_orders_2 @ A @ ( k1_struct_0 @ A ) )
        = ( u1_struct_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ( ( k2_orders_2 @ A @ ( k1_struct_0 @ A ) )
          = ( u1_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t45_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

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
    ! [X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( ( k2_orders_2 @ X18 @ X17 )
        = ( a_2_1_orders_2 @ X18 @ X17 ) )
      | ~ ( l1_orders_2 @ X18 )
      | ~ ( v5_orders_2 @ X18 )
      | ~ ( v4_orders_2 @ X18 )
      | ~ ( v3_orders_2 @ X18 )
      | ( v2_struct_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[d13_orders_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( ( k2_orders_2 @ X0 @ k1_xboole_0 )
        = ( a_2_1_orders_2 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('8',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X8: $i,X10: $i] :
      ( ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( m1_subset_1 @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( m1_subset_1 @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

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

thf('15',plain,(
    ! [X22: $i,X23: $i,X25: $i,X26: $i] :
      ( ~ ( l1_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ( v2_struct_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( r2_hidden @ X25 @ ( a_2_1_orders_2 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X22 ) )
      | ( X25 != X26 )
      | ( r2_hidden @ ( sk_E @ X26 @ X23 @ X22 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[fraenkel_a_2_1_orders_2])).

thf('16',plain,(
    ! [X22: $i,X23: $i,X26: $i] :
      ( ( r2_hidden @ ( sk_E @ X26 @ X23 @ X22 ) @ X23 )
      | ~ ( m1_subset_1 @ X26 @ ( u1_struct_0 @ X22 ) )
      | ( r2_hidden @ X26 @ ( a_2_1_orders_2 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ( v2_struct_0 @ X22 )
      | ~ ( v3_orders_2 @ X22 )
      | ~ ( v4_orders_2 @ X22 )
      | ~ ( v5_orders_2 @ X22 )
      | ~ ( l1_orders_2 @ X22 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ X1 @ ( a_2_1_orders_2 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( r2_hidden @ ( sk_E @ X1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_E @ ( sk_C @ X1 @ ( u1_struct_0 @ X0 ) ) @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( u1_struct_0 @ X0 ) ) @ ( a_2_1_orders_2 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','17'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('19',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( u1_struct_0 @ X0 ) ) @ ( a_2_1_orders_2 @ X0 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_E @ ( sk_C @ X1 @ ( u1_struct_0 @ X0 ) ) @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( u1_struct_0 @ X0 ) ) @ ( a_2_1_orders_2 @ X0 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( a_2_1_orders_2 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( a_2_1_orders_2 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( a_2_1_orders_2 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_orders_2 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup+',[status(thm)],['5','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_orders_2 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_k2_orders_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( l1_orders_2 @ X19 )
      | ~ ( v5_orders_2 @ X19 )
      | ~ ( v4_orders_2 @ X19 )
      | ~ ( v3_orders_2 @ X19 )
      | ( v2_struct_0 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( m1_subset_1 @ ( k2_orders_2 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_orders_2])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_orders_2 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( r1_tarski @ ( k2_orders_2 @ X0 @ k1_xboole_0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_orders_2 @ X0 @ k1_xboole_0 ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_orders_2 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_orders_2 @ X0 @ k1_xboole_0 ) )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ( v2_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_orders_2 @ X0 @ k1_xboole_0 ) )
      | ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('37',plain,(
    ! [X16: $i] :
      ( ( ( k1_struct_0 @ X16 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('38',plain,(
    ( k2_orders_2 @ sk_A @ ( k1_struct_0 @ sk_A ) )
 != ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( ( k2_orders_2 @ sk_A @ k1_xboole_0 )
     != ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('41',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_orders_2 @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('42',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ( k2_orders_2 @ sk_A @ k1_xboole_0 )
 != ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,
    ( ( ( k2_orders_2 @ sk_A @ k1_xboole_0 )
     != ( k2_orders_2 @ sk_A @ k1_xboole_0 ) )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( ( k2_orders_2 @ sk_A @ k1_xboole_0 )
     != ( k2_orders_2 @ sk_A @ k1_xboole_0 ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['44','45','46','47','48'])).

thf('50',plain,(
    v2_struct_0 @ sk_A ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['0','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ik3MKXjSBb
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:11:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 6.97/7.16  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 6.97/7.16  % Solved by: fo/fo7.sh
% 6.97/7.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 6.97/7.16  % done 6536 iterations in 6.698s
% 6.97/7.16  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 6.97/7.16  % SZS output start Refutation
% 6.97/7.16  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 6.97/7.16  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 6.97/7.16  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 6.97/7.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 6.97/7.16  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 6.97/7.16  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 6.97/7.16  thf(r2_orders_2_type, type, r2_orders_2: $i > $i > $i > $o).
% 6.97/7.16  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 6.97/7.16  thf(a_2_1_orders_2_type, type, a_2_1_orders_2: $i > $i > $i).
% 6.97/7.16  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 6.97/7.16  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 6.97/7.16  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 6.97/7.16  thf(sk_A_type, type, sk_A: $i).
% 6.97/7.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 6.97/7.16  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 6.97/7.16  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 6.97/7.16  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 6.97/7.16  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 6.97/7.16  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 6.97/7.16  thf(t45_orders_2, conjecture,
% 6.97/7.16    (![A:$i]:
% 6.97/7.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 6.97/7.16         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 6.97/7.16       ( ( k2_orders_2 @ A @ ( k1_struct_0 @ A ) ) = ( u1_struct_0 @ A ) ) ))).
% 6.97/7.16  thf(zf_stmt_0, negated_conjecture,
% 6.97/7.16    (~( ![A:$i]:
% 6.97/7.16        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 6.97/7.16            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 6.97/7.16          ( ( k2_orders_2 @ A @ ( k1_struct_0 @ A ) ) = ( u1_struct_0 @ A ) ) ) )),
% 6.97/7.16    inference('cnf.neg', [status(esa)], [t45_orders_2])).
% 6.97/7.16  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 6.97/7.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.97/7.16  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 6.97/7.16  thf('1', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 6.97/7.16      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.97/7.16  thf(t3_subset, axiom,
% 6.97/7.16    (![A:$i,B:$i]:
% 6.97/7.16     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 6.97/7.16  thf('2', plain,
% 6.97/7.16      (![X8 : $i, X10 : $i]:
% 6.97/7.16         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 6.97/7.16      inference('cnf', [status(esa)], [t3_subset])).
% 6.97/7.16  thf('3', plain,
% 6.97/7.16      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 6.97/7.16      inference('sup-', [status(thm)], ['1', '2'])).
% 6.97/7.16  thf(d13_orders_2, axiom,
% 6.97/7.16    (![A:$i]:
% 6.97/7.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 6.97/7.16         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 6.97/7.16       ( ![B:$i]:
% 6.97/7.16         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 6.97/7.16           ( ( k2_orders_2 @ A @ B ) = ( a_2_1_orders_2 @ A @ B ) ) ) ) ))).
% 6.97/7.16  thf('4', plain,
% 6.97/7.16      (![X17 : $i, X18 : $i]:
% 6.97/7.16         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 6.97/7.16          | ((k2_orders_2 @ X18 @ X17) = (a_2_1_orders_2 @ X18 @ X17))
% 6.97/7.16          | ~ (l1_orders_2 @ X18)
% 6.97/7.16          | ~ (v5_orders_2 @ X18)
% 6.97/7.16          | ~ (v4_orders_2 @ X18)
% 6.97/7.16          | ~ (v3_orders_2 @ X18)
% 6.97/7.16          | (v2_struct_0 @ X18))),
% 6.97/7.16      inference('cnf', [status(esa)], [d13_orders_2])).
% 6.97/7.16  thf('5', plain,
% 6.97/7.16      (![X0 : $i]:
% 6.97/7.16         ((v2_struct_0 @ X0)
% 6.97/7.16          | ~ (v3_orders_2 @ X0)
% 6.97/7.16          | ~ (v4_orders_2 @ X0)
% 6.97/7.16          | ~ (v5_orders_2 @ X0)
% 6.97/7.16          | ~ (l1_orders_2 @ X0)
% 6.97/7.16          | ((k2_orders_2 @ X0 @ k1_xboole_0)
% 6.97/7.16              = (a_2_1_orders_2 @ X0 @ k1_xboole_0)))),
% 6.97/7.16      inference('sup-', [status(thm)], ['3', '4'])).
% 6.97/7.16  thf(d3_tarski, axiom,
% 6.97/7.16    (![A:$i,B:$i]:
% 6.97/7.16     ( ( r1_tarski @ A @ B ) <=>
% 6.97/7.16       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 6.97/7.16  thf('6', plain,
% 6.97/7.16      (![X1 : $i, X3 : $i]:
% 6.97/7.16         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 6.97/7.16      inference('cnf', [status(esa)], [d3_tarski])).
% 6.97/7.16  thf(d10_xboole_0, axiom,
% 6.97/7.16    (![A:$i,B:$i]:
% 6.97/7.16     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.97/7.16  thf('7', plain,
% 6.97/7.16      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 6.97/7.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.97/7.16  thf('8', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 6.97/7.16      inference('simplify', [status(thm)], ['7'])).
% 6.97/7.16  thf('9', plain,
% 6.97/7.16      (![X8 : $i, X10 : $i]:
% 6.97/7.16         ((m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X10)) | ~ (r1_tarski @ X8 @ X10))),
% 6.97/7.16      inference('cnf', [status(esa)], [t3_subset])).
% 6.97/7.16  thf('10', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 6.97/7.16      inference('sup-', [status(thm)], ['8', '9'])).
% 6.97/7.16  thf(t4_subset, axiom,
% 6.97/7.16    (![A:$i,B:$i,C:$i]:
% 6.97/7.16     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 6.97/7.16       ( m1_subset_1 @ A @ C ) ))).
% 6.97/7.16  thf('11', plain,
% 6.97/7.16      (![X11 : $i, X12 : $i, X13 : $i]:
% 6.97/7.16         (~ (r2_hidden @ X11 @ X12)
% 6.97/7.16          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 6.97/7.16          | (m1_subset_1 @ X11 @ X13))),
% 6.97/7.16      inference('cnf', [status(esa)], [t4_subset])).
% 6.97/7.16  thf('12', plain,
% 6.97/7.16      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 6.97/7.16      inference('sup-', [status(thm)], ['10', '11'])).
% 6.97/7.16  thf('13', plain,
% 6.97/7.16      (![X0 : $i, X1 : $i]:
% 6.97/7.16         ((r1_tarski @ X0 @ X1) | (m1_subset_1 @ (sk_C @ X1 @ X0) @ X0))),
% 6.97/7.16      inference('sup-', [status(thm)], ['6', '12'])).
% 6.97/7.16  thf('14', plain,
% 6.97/7.16      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 6.97/7.16      inference('sup-', [status(thm)], ['1', '2'])).
% 6.97/7.16  thf(fraenkel_a_2_1_orders_2, axiom,
% 6.97/7.16    (![A:$i,B:$i,C:$i]:
% 6.97/7.16     ( ( ( ~( v2_struct_0 @ B ) ) & ( v3_orders_2 @ B ) & 
% 6.97/7.16         ( v4_orders_2 @ B ) & ( v5_orders_2 @ B ) & ( l1_orders_2 @ B ) & 
% 6.97/7.16         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ B ) ) ) ) =>
% 6.97/7.16       ( ( r2_hidden @ A @ ( a_2_1_orders_2 @ B @ C ) ) <=>
% 6.97/7.16         ( ?[D:$i]:
% 6.97/7.16           ( ( ![E:$i]:
% 6.97/7.16               ( ( m1_subset_1 @ E @ ( u1_struct_0 @ B ) ) =>
% 6.97/7.16                 ( ( r2_hidden @ E @ C ) => ( r2_orders_2 @ B @ D @ E ) ) ) ) & 
% 6.97/7.16             ( ( A ) = ( D ) ) & ( m1_subset_1 @ D @ ( u1_struct_0 @ B ) ) ) ) ) ))).
% 6.97/7.16  thf('15', plain,
% 6.97/7.16      (![X22 : $i, X23 : $i, X25 : $i, X26 : $i]:
% 6.97/7.16         (~ (l1_orders_2 @ X22)
% 6.97/7.16          | ~ (v5_orders_2 @ X22)
% 6.97/7.16          | ~ (v4_orders_2 @ X22)
% 6.97/7.16          | ~ (v3_orders_2 @ X22)
% 6.97/7.16          | (v2_struct_0 @ X22)
% 6.97/7.16          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 6.97/7.16          | (r2_hidden @ X25 @ (a_2_1_orders_2 @ X22 @ X23))
% 6.97/7.16          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X22))
% 6.97/7.16          | ((X25) != (X26))
% 6.97/7.16          | (r2_hidden @ (sk_E @ X26 @ X23 @ X22) @ X23))),
% 6.97/7.16      inference('cnf', [status(esa)], [fraenkel_a_2_1_orders_2])).
% 6.97/7.16  thf('16', plain,
% 6.97/7.16      (![X22 : $i, X23 : $i, X26 : $i]:
% 6.97/7.16         ((r2_hidden @ (sk_E @ X26 @ X23 @ X22) @ X23)
% 6.97/7.16          | ~ (m1_subset_1 @ X26 @ (u1_struct_0 @ X22))
% 6.97/7.16          | (r2_hidden @ X26 @ (a_2_1_orders_2 @ X22 @ X23))
% 6.97/7.16          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 6.97/7.16          | (v2_struct_0 @ X22)
% 6.97/7.16          | ~ (v3_orders_2 @ X22)
% 6.97/7.16          | ~ (v4_orders_2 @ X22)
% 6.97/7.16          | ~ (v5_orders_2 @ X22)
% 6.97/7.16          | ~ (l1_orders_2 @ X22))),
% 6.97/7.16      inference('simplify', [status(thm)], ['15'])).
% 6.97/7.16  thf('17', plain,
% 6.97/7.16      (![X0 : $i, X1 : $i]:
% 6.97/7.16         (~ (l1_orders_2 @ X0)
% 6.97/7.16          | ~ (v5_orders_2 @ X0)
% 6.97/7.16          | ~ (v4_orders_2 @ X0)
% 6.97/7.16          | ~ (v3_orders_2 @ X0)
% 6.97/7.16          | (v2_struct_0 @ X0)
% 6.97/7.16          | (r2_hidden @ X1 @ (a_2_1_orders_2 @ X0 @ k1_xboole_0))
% 6.97/7.16          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 6.97/7.16          | (r2_hidden @ (sk_E @ X1 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 6.97/7.16      inference('sup-', [status(thm)], ['14', '16'])).
% 6.97/7.16  thf('18', plain,
% 6.97/7.16      (![X0 : $i, X1 : $i]:
% 6.97/7.16         ((r1_tarski @ (u1_struct_0 @ X0) @ X1)
% 6.97/7.16          | (r2_hidden @ 
% 6.97/7.16             (sk_E @ (sk_C @ X1 @ (u1_struct_0 @ X0)) @ k1_xboole_0 @ X0) @ 
% 6.97/7.16             k1_xboole_0)
% 6.97/7.16          | (r2_hidden @ (sk_C @ X1 @ (u1_struct_0 @ X0)) @ 
% 6.97/7.16             (a_2_1_orders_2 @ X0 @ k1_xboole_0))
% 6.97/7.16          | (v2_struct_0 @ X0)
% 6.97/7.16          | ~ (v3_orders_2 @ X0)
% 6.97/7.16          | ~ (v4_orders_2 @ X0)
% 6.97/7.16          | ~ (v5_orders_2 @ X0)
% 6.97/7.16          | ~ (l1_orders_2 @ X0))),
% 6.97/7.16      inference('sup-', [status(thm)], ['13', '17'])).
% 6.97/7.16  thf(t7_ordinal1, axiom,
% 6.97/7.16    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 6.97/7.16  thf('19', plain,
% 6.97/7.16      (![X14 : $i, X15 : $i]:
% 6.97/7.16         (~ (r2_hidden @ X14 @ X15) | ~ (r1_tarski @ X15 @ X14))),
% 6.97/7.16      inference('cnf', [status(esa)], [t7_ordinal1])).
% 6.97/7.16  thf('20', plain,
% 6.97/7.16      (![X0 : $i, X1 : $i]:
% 6.97/7.16         (~ (l1_orders_2 @ X0)
% 6.97/7.16          | ~ (v5_orders_2 @ X0)
% 6.97/7.16          | ~ (v4_orders_2 @ X0)
% 6.97/7.16          | ~ (v3_orders_2 @ X0)
% 6.97/7.16          | (v2_struct_0 @ X0)
% 6.97/7.16          | (r2_hidden @ (sk_C @ X1 @ (u1_struct_0 @ X0)) @ 
% 6.97/7.16             (a_2_1_orders_2 @ X0 @ k1_xboole_0))
% 6.97/7.16          | (r1_tarski @ (u1_struct_0 @ X0) @ X1)
% 6.97/7.16          | ~ (r1_tarski @ k1_xboole_0 @ 
% 6.97/7.16               (sk_E @ (sk_C @ X1 @ (u1_struct_0 @ X0)) @ k1_xboole_0 @ X0)))),
% 6.97/7.16      inference('sup-', [status(thm)], ['18', '19'])).
% 6.97/7.16  thf('21', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 6.97/7.16      inference('cnf', [status(esa)], [t2_xboole_1])).
% 6.97/7.16  thf('22', plain,
% 6.97/7.16      (![X0 : $i, X1 : $i]:
% 6.97/7.16         (~ (l1_orders_2 @ X0)
% 6.97/7.16          | ~ (v5_orders_2 @ X0)
% 6.97/7.16          | ~ (v4_orders_2 @ X0)
% 6.97/7.16          | ~ (v3_orders_2 @ X0)
% 6.97/7.16          | (v2_struct_0 @ X0)
% 6.97/7.16          | (r2_hidden @ (sk_C @ X1 @ (u1_struct_0 @ X0)) @ 
% 6.97/7.16             (a_2_1_orders_2 @ X0 @ k1_xboole_0))
% 6.97/7.16          | (r1_tarski @ (u1_struct_0 @ X0) @ X1))),
% 6.97/7.16      inference('demod', [status(thm)], ['20', '21'])).
% 6.97/7.16  thf('23', plain,
% 6.97/7.16      (![X1 : $i, X3 : $i]:
% 6.97/7.16         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 6.97/7.16      inference('cnf', [status(esa)], [d3_tarski])).
% 6.97/7.16  thf('24', plain,
% 6.97/7.16      (![X0 : $i]:
% 6.97/7.16         ((r1_tarski @ (u1_struct_0 @ X0) @ (a_2_1_orders_2 @ X0 @ k1_xboole_0))
% 6.97/7.16          | (v2_struct_0 @ X0)
% 6.97/7.16          | ~ (v3_orders_2 @ X0)
% 6.97/7.16          | ~ (v4_orders_2 @ X0)
% 6.97/7.16          | ~ (v5_orders_2 @ X0)
% 6.97/7.16          | ~ (l1_orders_2 @ X0)
% 6.97/7.16          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 6.97/7.16             (a_2_1_orders_2 @ X0 @ k1_xboole_0)))),
% 6.97/7.16      inference('sup-', [status(thm)], ['22', '23'])).
% 6.97/7.16  thf('25', plain,
% 6.97/7.16      (![X0 : $i]:
% 6.97/7.16         (~ (l1_orders_2 @ X0)
% 6.97/7.16          | ~ (v5_orders_2 @ X0)
% 6.97/7.16          | ~ (v4_orders_2 @ X0)
% 6.97/7.16          | ~ (v3_orders_2 @ X0)
% 6.97/7.16          | (v2_struct_0 @ X0)
% 6.97/7.16          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 6.97/7.16             (a_2_1_orders_2 @ X0 @ k1_xboole_0)))),
% 6.97/7.16      inference('simplify', [status(thm)], ['24'])).
% 6.97/7.16  thf('26', plain,
% 6.97/7.16      (![X0 : $i]:
% 6.97/7.16         ((r1_tarski @ (u1_struct_0 @ X0) @ (k2_orders_2 @ X0 @ k1_xboole_0))
% 6.97/7.16          | ~ (l1_orders_2 @ X0)
% 6.97/7.16          | ~ (v5_orders_2 @ X0)
% 6.97/7.16          | ~ (v4_orders_2 @ X0)
% 6.97/7.16          | ~ (v3_orders_2 @ X0)
% 6.97/7.16          | (v2_struct_0 @ X0)
% 6.97/7.16          | (v2_struct_0 @ X0)
% 6.97/7.16          | ~ (v3_orders_2 @ X0)
% 6.97/7.16          | ~ (v4_orders_2 @ X0)
% 6.97/7.16          | ~ (v5_orders_2 @ X0)
% 6.97/7.16          | ~ (l1_orders_2 @ X0))),
% 6.97/7.16      inference('sup+', [status(thm)], ['5', '25'])).
% 6.97/7.16  thf('27', plain,
% 6.97/7.16      (![X0 : $i]:
% 6.97/7.16         ((v2_struct_0 @ X0)
% 6.97/7.16          | ~ (v3_orders_2 @ X0)
% 6.97/7.16          | ~ (v4_orders_2 @ X0)
% 6.97/7.16          | ~ (v5_orders_2 @ X0)
% 6.97/7.16          | ~ (l1_orders_2 @ X0)
% 6.97/7.16          | (r1_tarski @ (u1_struct_0 @ X0) @ (k2_orders_2 @ X0 @ k1_xboole_0)))),
% 6.97/7.16      inference('simplify', [status(thm)], ['26'])).
% 6.97/7.16  thf('28', plain,
% 6.97/7.16      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 6.97/7.16      inference('sup-', [status(thm)], ['1', '2'])).
% 6.97/7.16  thf(dt_k2_orders_2, axiom,
% 6.97/7.16    (![A:$i,B:$i]:
% 6.97/7.16     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 6.97/7.16         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) & 
% 6.97/7.16         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 6.97/7.16       ( m1_subset_1 @
% 6.97/7.16         ( k2_orders_2 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 6.97/7.16  thf('29', plain,
% 6.97/7.16      (![X19 : $i, X20 : $i]:
% 6.97/7.16         (~ (l1_orders_2 @ X19)
% 6.97/7.16          | ~ (v5_orders_2 @ X19)
% 6.97/7.16          | ~ (v4_orders_2 @ X19)
% 6.97/7.16          | ~ (v3_orders_2 @ X19)
% 6.97/7.16          | (v2_struct_0 @ X19)
% 6.97/7.16          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 6.97/7.16          | (m1_subset_1 @ (k2_orders_2 @ X19 @ X20) @ 
% 6.97/7.16             (k1_zfmisc_1 @ (u1_struct_0 @ X19))))),
% 6.97/7.16      inference('cnf', [status(esa)], [dt_k2_orders_2])).
% 6.97/7.16  thf('30', plain,
% 6.97/7.16      (![X0 : $i]:
% 6.97/7.16         ((m1_subset_1 @ (k2_orders_2 @ X0 @ k1_xboole_0) @ 
% 6.97/7.16           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 6.97/7.16          | (v2_struct_0 @ X0)
% 6.97/7.16          | ~ (v3_orders_2 @ X0)
% 6.97/7.16          | ~ (v4_orders_2 @ X0)
% 6.97/7.16          | ~ (v5_orders_2 @ X0)
% 6.97/7.16          | ~ (l1_orders_2 @ X0))),
% 6.97/7.16      inference('sup-', [status(thm)], ['28', '29'])).
% 6.97/7.16  thf('31', plain,
% 6.97/7.16      (![X8 : $i, X9 : $i]:
% 6.97/7.16         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 6.97/7.16      inference('cnf', [status(esa)], [t3_subset])).
% 6.97/7.16  thf('32', plain,
% 6.97/7.16      (![X0 : $i]:
% 6.97/7.16         (~ (l1_orders_2 @ X0)
% 6.97/7.16          | ~ (v5_orders_2 @ X0)
% 6.97/7.16          | ~ (v4_orders_2 @ X0)
% 6.97/7.16          | ~ (v3_orders_2 @ X0)
% 6.97/7.16          | (v2_struct_0 @ X0)
% 6.97/7.16          | (r1_tarski @ (k2_orders_2 @ X0 @ k1_xboole_0) @ (u1_struct_0 @ X0)))),
% 6.97/7.16      inference('sup-', [status(thm)], ['30', '31'])).
% 6.97/7.16  thf('33', plain,
% 6.97/7.16      (![X4 : $i, X6 : $i]:
% 6.97/7.16         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 6.97/7.16      inference('cnf', [status(esa)], [d10_xboole_0])).
% 6.97/7.16  thf('34', plain,
% 6.97/7.16      (![X0 : $i]:
% 6.97/7.16         ((v2_struct_0 @ X0)
% 6.97/7.16          | ~ (v3_orders_2 @ X0)
% 6.97/7.16          | ~ (v4_orders_2 @ X0)
% 6.97/7.16          | ~ (v5_orders_2 @ X0)
% 6.97/7.16          | ~ (l1_orders_2 @ X0)
% 6.97/7.16          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 6.97/7.16               (k2_orders_2 @ X0 @ k1_xboole_0))
% 6.97/7.16          | ((u1_struct_0 @ X0) = (k2_orders_2 @ X0 @ k1_xboole_0)))),
% 6.97/7.16      inference('sup-', [status(thm)], ['32', '33'])).
% 6.97/7.16  thf('35', plain,
% 6.97/7.16      (![X0 : $i]:
% 6.97/7.16         (~ (l1_orders_2 @ X0)
% 6.97/7.16          | ~ (v5_orders_2 @ X0)
% 6.97/7.16          | ~ (v4_orders_2 @ X0)
% 6.97/7.16          | ~ (v3_orders_2 @ X0)
% 6.97/7.16          | (v2_struct_0 @ X0)
% 6.97/7.16          | ((u1_struct_0 @ X0) = (k2_orders_2 @ X0 @ k1_xboole_0))
% 6.97/7.16          | ~ (l1_orders_2 @ X0)
% 6.97/7.16          | ~ (v5_orders_2 @ X0)
% 6.97/7.16          | ~ (v4_orders_2 @ X0)
% 6.97/7.16          | ~ (v3_orders_2 @ X0)
% 6.97/7.16          | (v2_struct_0 @ X0))),
% 6.97/7.16      inference('sup-', [status(thm)], ['27', '34'])).
% 6.97/7.16  thf('36', plain,
% 6.97/7.16      (![X0 : $i]:
% 6.97/7.16         (((u1_struct_0 @ X0) = (k2_orders_2 @ X0 @ k1_xboole_0))
% 6.97/7.16          | (v2_struct_0 @ X0)
% 6.97/7.16          | ~ (v3_orders_2 @ X0)
% 6.97/7.16          | ~ (v4_orders_2 @ X0)
% 6.97/7.16          | ~ (v5_orders_2 @ X0)
% 6.97/7.16          | ~ (l1_orders_2 @ X0))),
% 6.97/7.16      inference('simplify', [status(thm)], ['35'])).
% 6.97/7.16  thf(d2_struct_0, axiom,
% 6.97/7.16    (![A:$i]:
% 6.97/7.16     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 6.97/7.16  thf('37', plain,
% 6.97/7.16      (![X16 : $i]:
% 6.97/7.16         (((k1_struct_0 @ X16) = (k1_xboole_0)) | ~ (l1_struct_0 @ X16))),
% 6.97/7.16      inference('cnf', [status(esa)], [d2_struct_0])).
% 6.97/7.16  thf('38', plain,
% 6.97/7.16      (((k2_orders_2 @ sk_A @ (k1_struct_0 @ sk_A)) != (u1_struct_0 @ sk_A))),
% 6.97/7.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.97/7.16  thf('39', plain,
% 6.97/7.16      ((((k2_orders_2 @ sk_A @ k1_xboole_0) != (u1_struct_0 @ sk_A))
% 6.97/7.16        | ~ (l1_struct_0 @ sk_A))),
% 6.97/7.16      inference('sup-', [status(thm)], ['37', '38'])).
% 6.97/7.16  thf('40', plain, ((l1_orders_2 @ sk_A)),
% 6.97/7.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.97/7.16  thf(dt_l1_orders_2, axiom,
% 6.97/7.16    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 6.97/7.16  thf('41', plain,
% 6.97/7.16      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_orders_2 @ X21))),
% 6.97/7.16      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 6.97/7.16  thf('42', plain, ((l1_struct_0 @ sk_A)),
% 6.97/7.16      inference('sup-', [status(thm)], ['40', '41'])).
% 6.97/7.16  thf('43', plain,
% 6.97/7.16      (((k2_orders_2 @ sk_A @ k1_xboole_0) != (u1_struct_0 @ sk_A))),
% 6.97/7.16      inference('demod', [status(thm)], ['39', '42'])).
% 6.97/7.16  thf('44', plain,
% 6.97/7.16      ((((k2_orders_2 @ sk_A @ k1_xboole_0)
% 6.97/7.16          != (k2_orders_2 @ sk_A @ k1_xboole_0))
% 6.97/7.16        | ~ (l1_orders_2 @ sk_A)
% 6.97/7.16        | ~ (v5_orders_2 @ sk_A)
% 6.97/7.16        | ~ (v4_orders_2 @ sk_A)
% 6.97/7.16        | ~ (v3_orders_2 @ sk_A)
% 6.97/7.16        | (v2_struct_0 @ sk_A))),
% 6.97/7.16      inference('sup-', [status(thm)], ['36', '43'])).
% 6.97/7.16  thf('45', plain, ((l1_orders_2 @ sk_A)),
% 6.97/7.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.97/7.16  thf('46', plain, ((v5_orders_2 @ sk_A)),
% 6.97/7.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.97/7.16  thf('47', plain, ((v4_orders_2 @ sk_A)),
% 6.97/7.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.97/7.16  thf('48', plain, ((v3_orders_2 @ sk_A)),
% 6.97/7.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 6.97/7.16  thf('49', plain,
% 6.97/7.16      ((((k2_orders_2 @ sk_A @ k1_xboole_0)
% 6.97/7.16          != (k2_orders_2 @ sk_A @ k1_xboole_0))
% 6.97/7.16        | (v2_struct_0 @ sk_A))),
% 6.97/7.16      inference('demod', [status(thm)], ['44', '45', '46', '47', '48'])).
% 6.97/7.16  thf('50', plain, ((v2_struct_0 @ sk_A)),
% 6.97/7.16      inference('simplify', [status(thm)], ['49'])).
% 6.97/7.16  thf('51', plain, ($false), inference('demod', [status(thm)], ['0', '50'])).
% 6.97/7.16  
% 6.97/7.16  % SZS output end Refutation
% 6.97/7.16  
% 6.97/7.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
