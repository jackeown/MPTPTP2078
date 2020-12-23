%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0381+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.44oFD2XIHT

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:54 EST 2020

% Result     : Theorem 6.13s
% Output     : Refutation 6.13s
% Verified   : 
% Statistics : Number of formulae       :   26 (  28 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :  119 ( 135 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_8_type,type,(
    sk_B_8: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t63_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ( m1_subset_1 @ ( k1_tarski @ A @ ( k1_zfmisc_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ ( A @ B ) )
       => ( m1_subset_1 @ ( k1_tarski @ A @ ( k1_zfmisc_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t63_subset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k1_tarski @ sk_A_2 @ ( k1_zfmisc_1 @ sk_B_8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ ( sk_A_2 @ sk_B_8 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('2',plain,(
    ! [X1021: $i,X1023: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1021 @ X1023 ) )
      | ~ ( r2_hidden @ ( X1021 @ X1023 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('3',plain,(
    r1_tarski @ ( k1_tarski @ sk_A_2 @ sk_B_8 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ( r1_tarski @ ( C @ A ) ) ) ) )).

thf('4',plain,(
    ! [X961: $i,X962: $i,X963: $i] :
      ( ~ ( r1_tarski @ ( X961 @ X962 ) )
      | ( r2_hidden @ ( X961 @ X963 ) )
      | ( X963
       != ( k1_zfmisc_1 @ X962 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('5',plain,(
    ! [X961: $i,X962: $i] :
      ( ( r2_hidden @ ( X961 @ ( k1_zfmisc_1 @ X962 ) ) )
      | ~ ( r1_tarski @ ( X961 @ X962 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    r2_hidden @ ( k1_tarski @ sk_A_2 @ ( k1_zfmisc_1 @ sk_B_8 ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ ( B @ A ) )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ ( B @ A ) )
        <=> ( r2_hidden @ ( B @ A ) ) ) ) ) )).

thf('7',plain,(
    ! [X1483: $i,X1484: $i] :
      ( ~ ( r2_hidden @ ( X1483 @ X1484 ) )
      | ( m1_subset_1 @ ( X1483 @ X1484 ) )
      | ( v1_xboole_0 @ X1484 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( X10 @ X11 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X1483: $i,X1484: $i] :
      ( ( m1_subset_1 @ ( X1483 @ X1484 ) )
      | ~ ( r2_hidden @ ( X1483 @ X1484 ) ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_A_2 @ ( k1_zfmisc_1 @ sk_B_8 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    $false ),
    inference(demod,[status(thm)],['0','10'])).

%------------------------------------------------------------------------------
