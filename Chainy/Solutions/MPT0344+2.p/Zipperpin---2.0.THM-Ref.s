%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0344+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.L2rkBqHORF

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:53 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   50 (  65 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :   11
%              Number of atoms          :  228 ( 352 expanded)
%              Number of equality atoms :   16 (  30 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_8_type,type,(
    sk_B_8: $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('0',plain,(
    ! [X77: $i] :
      ( ( X77 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    ! [X77: $i] :
      ( ( X77 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t10_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ! [C: $i] :
              ( ( m1_subset_1 @ ( C @ A ) )
             => ~ ( r2_hidden @ ( C @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
       => ~ ( ( B != k1_xboole_0 )
            & ! [C: $i] :
                ( ( m1_subset_1 @ ( C @ A ) )
               => ~ ( r2_hidden @ ( C @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_subset_1])).

thf('3',plain,(
    ! [X1470: $i] :
      ( ~ ( r2_hidden @ ( X1470 @ sk_B_8 ) )
      | ~ ( m1_subset_1 @ ( X1470 @ sk_A_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( sk_B_8 = o_0_0_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_B_1 @ sk_B_8 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    sk_B_8 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('7',plain,(
    sk_B_8 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( m1_subset_1 @ ( sk_B_1 @ sk_B_8 @ sk_A_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X77: $i] :
      ( ( X77 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X1457: $i,X1458: $i] :
      ( ~ ( m1_subset_1 @ ( X1457 @ X1458 ) )
      | ( r2_hidden @ ( X1457 @ X1458 ) )
      | ( v1_xboole_0 @ X1458 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A_2 ) )
    | ( r2_hidden @ ( sk_B_8 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X1464: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X1464 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('14',plain,(
    r2_hidden @ ( sk_B_8 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ ( A @ B ) )
     => ( r1_tarski @ ( A @ ( k3_tarski @ B ) ) ) ) )).

thf('15',plain,(
    ! [X1058: $i,X1059: $i] :
      ( ( r1_tarski @ ( X1058 @ ( k3_tarski @ X1059 ) ) )
      | ~ ( r2_hidden @ ( X1058 @ X1059 ) ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('16',plain,(
    r1_tarski @ ( sk_B_8 @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('17',plain,(
    ! [X1447: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X1447 ) )
      = X1447 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('18',plain,(
    r1_tarski @ ( sk_B_8 @ sk_A_2 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( r2_hidden @ ( C @ B ) ) ) ) )).

thf('19',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( X13 @ X14 ) )
      | ( r2_hidden @ ( X13 @ X15 ) )
      | ~ ( r1_tarski @ ( X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( X0 @ sk_A_2 ) )
      | ~ ( r2_hidden @ ( X0 @ sk_B_8 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_B_8 = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_B_8 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['9','20'])).

thf('22',plain,(
    sk_B_8 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf('23',plain,(
    r2_hidden @ ( sk_B_1 @ sk_B_8 @ sk_A_2 ) ),
    inference('simplify_reflect-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X1457: $i,X1458: $i] :
      ( ~ ( r2_hidden @ ( X1457 @ X1458 ) )
      | ( m1_subset_1 @ ( X1457 @ X1458 ) )
      | ( v1_xboole_0 @ X1458 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('25',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( X10 @ X11 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('26',plain,(
    ! [X1457: $i,X1458: $i] :
      ( ( m1_subset_1 @ ( X1457 @ X1458 ) )
      | ~ ( r2_hidden @ ( X1457 @ X1458 ) ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ ( sk_B_1 @ sk_B_8 @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['8','27'])).

%------------------------------------------------------------------------------
