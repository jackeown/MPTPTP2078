%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0373+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3xYybksZ6h

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:54 EST 2020

% Result     : Theorem 3.00s
% Output     : Refutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :   44 (  50 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  189 ( 251 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_8_type,type,(
    sk_B_8: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t55_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ A ) )
     => ( ( A != k1_xboole_0 )
       => ( m1_subset_1 @ ( k1_tarski @ B @ ( k1_zfmisc_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ ( B @ A ) )
       => ( ( A != k1_xboole_0 )
         => ( m1_subset_1 @ ( k1_tarski @ B @ ( k1_zfmisc_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t55_subset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ sk_B_8 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ ( sk_B_8 @ sk_A_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ ( B @ A ) )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ ( B @ A ) )
        <=> ( r2_hidden @ ( B @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X1469: $i,X1470: $i] :
      ( ~ ( m1_subset_1 @ ( X1469 @ X1470 ) )
      | ( r2_hidden @ ( X1469 @ X1470 ) )
      | ( v1_xboole_0 @ X1470 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_A_2 )
    | ( r2_hidden @ ( sk_B_8 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('4',plain,(
    ! [X392: $i,X393: $i] :
      ( ~ ( v1_xboole_0 @ X392 )
      | ~ ( v1_xboole_0 @ X393 )
      | ( X392 = X393 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('5',plain,(
    sk_A_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('6',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('7',plain,(
    sk_A_2 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( X0 != o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A_2 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A_2 ) ),
    inference(simplify,[status(thm)],['8'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('11',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('12',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v1_xboole_0 @ sk_A_2 ) ),
    inference('simplify_reflect+',[status(thm)],['9','12'])).

thf('14',plain,(
    r2_hidden @ ( sk_B_8 @ sk_A_2 ) ),
    inference(clc,[status(thm)],['3','13'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('15',plain,(
    ! [X1021: $i,X1023: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1021 @ X1023 ) )
      | ~ ( r2_hidden @ ( X1021 @ X1023 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('16',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_8 @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ( r1_tarski @ ( C @ A ) ) ) ) )).

thf('17',plain,(
    ! [X961: $i,X962: $i,X963: $i] :
      ( ~ ( r1_tarski @ ( X961 @ X962 ) )
      | ( r2_hidden @ ( X961 @ X963 ) )
      | ( X963
       != ( k1_zfmisc_1 @ X962 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('18',plain,(
    ! [X961: $i,X962: $i] :
      ( ( r2_hidden @ ( X961 @ ( k1_zfmisc_1 @ X962 ) ) )
      | ~ ( r1_tarski @ ( X961 @ X962 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    r2_hidden @ ( k1_tarski @ sk_B_8 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X1469: $i,X1470: $i] :
      ( ~ ( r2_hidden @ ( X1469 @ X1470 ) )
      | ( m1_subset_1 @ ( X1469 @ X1470 ) )
      | ( v1_xboole_0 @ X1470 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( X10 @ X11 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,(
    ! [X1469: $i,X1470: $i] :
      ( ( m1_subset_1 @ ( X1469 @ X1470 ) )
      | ~ ( r2_hidden @ ( X1469 @ X1470 ) ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B_8 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['0','23'])).

%------------------------------------------------------------------------------
