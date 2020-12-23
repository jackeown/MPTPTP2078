%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0368+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.su6InMbz5C

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:54 EST 2020

% Result     : Theorem 3.61s
% Output     : Refutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :   41 (  66 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :   12
%              Number of atoms          :  207 ( 436 expanded)
%              Number of equality atoms :    8 (  22 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_4_type,type,(
    sk_C_4: $i > $i > $i )).

thf(sk_B_8_type,type,(
    sk_B_8: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t49_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ( ! [C: $i] :
            ( ( m1_subset_1 @ ( C @ A ) )
           => ( r2_hidden @ ( C @ B ) ) )
       => ( A = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
       => ( ! [C: $i] :
              ( ( m1_subset_1 @ ( C @ A ) )
             => ( r2_hidden @ ( C @ B ) ) )
         => ( A = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_subset_1])).

thf('0',plain,(
    m1_subset_1 @ ( sk_B_8 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ ( B @ A ) )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ ( B @ A ) )
        <=> ( r2_hidden @ ( B @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X1469: $i,X1470: $i] :
      ( ~ ( m1_subset_1 @ ( X1469 @ X1470 ) )
      | ( r2_hidden @ ( X1469 @ X1470 ) )
      | ( v1_xboole_0 @ X1470 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A_2 ) )
    | ( r2_hidden @ ( sk_B_8 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('3',plain,(
    ! [X1499: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X1499 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('4',plain,(
    r2_hidden @ ( sk_B_8 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(clc,[status(thm)],['2','3'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ B ) )
        <=> ( r1_tarski @ ( C @ A ) ) ) ) )).

thf('5',plain,(
    ! [X962: $i,X963: $i,X964: $i] :
      ( ~ ( r2_hidden @ ( X964 @ X963 ) )
      | ( r1_tarski @ ( X964 @ X962 ) )
      | ( X963
       != ( k1_zfmisc_1 @ X962 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('6',plain,(
    ! [X962: $i,X964: $i] :
      ( ( r1_tarski @ ( X964 @ X962 ) )
      | ~ ( r2_hidden @ ( X964 @ ( k1_zfmisc_1 @ X962 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ ( sk_B_8 @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ ( A @ B ) )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( A != B ) ) ) )).

thf('8',plain,(
    ! [X40: $i,X42: $i] :
      ( ( r2_xboole_0 @ ( X40 @ X42 ) )
      | ( X40 = X42 )
      | ~ ( r1_tarski @ ( X40 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('9',plain,
    ( ( sk_B_8 = sk_A_2 )
    | ( r2_xboole_0 @ ( sk_B_8 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    sk_A_2 != sk_B_8 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_xboole_0 @ ( sk_B_8 @ sk_A_2 ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ ( A @ B ) )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ ( C @ B ) )
              & ~ ( r2_hidden @ ( C @ A ) ) ) ) )).

thf('12',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( r2_xboole_0 @ ( X75 @ X76 ) )
      | ( r2_hidden @ ( sk_C_4 @ ( X76 @ X75 ) @ X76 ) ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('13',plain,(
    r2_hidden @ ( sk_C_4 @ ( sk_A_2 @ sk_B_8 ) @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
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

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( X10 @ X11 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X1469: $i,X1470: $i] :
      ( ( m1_subset_1 @ ( X1469 @ X1470 ) )
      | ~ ( r2_hidden @ ( X1469 @ X1470 ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ ( sk_C_4 @ ( sk_A_2 @ sk_B_8 ) @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X1602: $i] :
      ( ( r2_hidden @ ( X1602 @ sk_B_8 ) )
      | ~ ( m1_subset_1 @ ( X1602 @ sk_A_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    r2_hidden @ ( sk_C_4 @ ( sk_A_2 @ sk_B_8 ) @ sk_B_8 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X75: $i,X76: $i] :
      ( ~ ( r2_xboole_0 @ ( X75 @ X76 ) )
      | ~ ( r2_hidden @ ( sk_C_4 @ ( X76 @ X75 ) @ X75 ) ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('21',plain,(
    ~ ( r2_xboole_0 @ ( sk_B_8 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_xboole_0 @ ( sk_B_8 @ sk_A_2 ) ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['21','22'])).

%------------------------------------------------------------------------------
