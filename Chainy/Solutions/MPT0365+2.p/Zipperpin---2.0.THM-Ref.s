%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0365+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.NxjH6Y7N1X

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:54 EST 2020

% Result     : Theorem 39.21s
% Output     : Refutation 39.21s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 203 expanded)
%              Number of leaves         :   40 (  81 expanded)
%              Depth                    :   10
%              Number of atoms          :  880 (1614 expanded)
%              Number of equality atoms :  100 ( 166 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_20_type,type,(
    sk_C_20: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_8_type,type,(
    sk_B_8: $i )).

thf(t46_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( ( r1_xboole_0 @ ( B @ C ) )
              & ( r1_xboole_0 @ ( k3_subset_1 @ ( A @ B ) @ ( k3_subset_1 @ ( A @ C ) ) ) ) )
           => ( B
              = ( k3_subset_1 @ ( A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ A ) ) )
           => ( ( ( r1_xboole_0 @ ( B @ C ) )
                & ( r1_xboole_0 @ ( k3_subset_1 @ ( A @ B ) @ ( k3_subset_1 @ ( A @ C ) ) ) ) )
             => ( B
                = ( k3_subset_1 @ ( A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_subset_1])).

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

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('8',plain,(
    ! [X210: $i,X211: $i] :
      ( ( ( k3_xboole_0 @ ( X210 @ X211 ) )
        = X210 )
      | ~ ( r1_tarski @ ( X210 @ X211 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('9',plain,
    ( ( k3_xboole_0 @ ( sk_B_8 @ sk_A_2 ) )
    = sk_B_8 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r1_xboole_0 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('12',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('13',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k3_xboole_0 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['10','13'])).

thf(l98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ ( k3_xboole_0 @ ( A @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X99: $i,X100: $i] :
      ( ( k5_xboole_0 @ ( X99 @ X100 ) )
      = ( k4_xboole_0 @ ( k2_xboole_0 @ ( X99 @ X100 ) @ ( k3_xboole_0 @ ( X99 @ X100 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l98_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ ( A @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('16',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ! [X99: $i,X100: $i] :
      ( ( k5_xboole_0 @ ( X99 @ X100 ) )
      = ( k6_subset_1 @ ( k2_xboole_0 @ ( X99 @ X100 ) @ ( k3_xboole_0 @ ( X99 @ X100 ) ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k5_xboole_0 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) )
    = ( k6_subset_1 @ ( k2_xboole_0 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) @ o_0_0_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['14','17'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('19',plain,(
    ! [X244: $i] :
      ( ( k4_xboole_0 @ ( X244 @ k1_xboole_0 ) )
      = X244 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('20',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('21',plain,(
    ! [X244: $i] :
      ( ( k4_xboole_0 @ ( X244 @ o_0_0_xboole_0 ) )
      = X244 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('23',plain,(
    ! [X244: $i] :
      ( ( k6_subset_1 @ ( X244 @ o_0_0_xboole_0 ) )
      = X244 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k5_xboole_0 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) )
    = ( k2_xboole_0 @ ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) ) ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    m1_subset_1 @ ( sk_B_8 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k3_subset_1 @ ( A @ B ) )
        = ( k4_xboole_0 @ ( A @ B ) ) ) ) )).

thf('26',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k4_xboole_0 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('27',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('28',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k6_subset_1 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) )
    = ( k6_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    m1_subset_1 @ ( sk_C_20 @ ( k1_zfmisc_1 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X1474: $i,X1475: $i] :
      ( ( ( k3_subset_1 @ ( X1474 @ X1475 ) )
        = ( k6_subset_1 @ ( X1474 @ X1475 ) ) )
      | ~ ( m1_subset_1 @ ( X1475 @ ( k1_zfmisc_1 @ X1474 ) ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('32',plain,
    ( ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) )
    = ( k6_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( k3_subset_1 @ ( sk_A_2 @ sk_B_8 ) )
    = ( k6_subset_1 @ ( sk_A_2 @ sk_B_8 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('34',plain,
    ( ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) )
    = ( k6_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(l36_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( A @ C ) ) ) ) ) )).

thf('35',plain,(
    ! [X91: $i,X92: $i,X93: $i] :
      ( ( k4_xboole_0 @ ( X91 @ ( k3_xboole_0 @ ( X92 @ X93 ) ) ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X91 @ X92 ) @ ( k4_xboole_0 @ ( X91 @ X93 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[l36_xboole_1])).

thf('36',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('37',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('38',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('39',plain,(
    ! [X91: $i,X92: $i,X93: $i] :
      ( ( k6_subset_1 @ ( X91 @ ( k3_xboole_0 @ ( X92 @ X93 ) ) ) )
      = ( k2_xboole_0 @ ( k6_subset_1 @ ( X91 @ X92 ) @ ( k6_subset_1 @ ( X91 @ X93 ) ) ) ) ) ),
    inference(demod,[status(thm)],['35','36','37','38'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k6_subset_1 @ ( X2 @ X0 ) @ ( k6_subset_1 @ ( X2 @ X1 ) ) ) )
      = ( k6_subset_1 @ ( X2 @ ( k3_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('43',plain,(
    r1_xboole_0 @ ( sk_B_8 @ sk_C_20 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('45',plain,
    ( ( k3_xboole_0 @ ( sk_B_8 @ sk_C_20 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X244: $i] :
      ( ( k6_subset_1 @ ( X244 @ o_0_0_xboole_0 ) )
      = X244 ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('47',plain,
    ( ( k5_xboole_0 @ ( k6_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ ( k6_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ) )
    = sk_A_2 ),
    inference(demod,[status(thm)],['24','29','32','33','34','41','42','45','46'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ ( A @ A ) )
      = k1_xboole_0 ) )).

thf('48',plain,(
    ! [X402: $i] :
      ( ( k5_xboole_0 @ ( X402 @ X402 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('49',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('50',plain,(
    ! [X402: $i] :
      ( ( k5_xboole_0 @ ( X402 @ X402 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ ( A @ B ) @ C ) )
      = ( k5_xboole_0 @ ( A @ ( k5_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('51',plain,(
    ! [X399: $i,X400: $i,X401: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ ( X399 @ X400 ) @ X401 ) )
      = ( k5_xboole_0 @ ( X399 @ ( k5_xboole_0 @ ( X400 @ X401 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = ( k5_xboole_0 @ ( X1 @ ( k5_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('53',plain,(
    ! [X302: $i] :
      ( ( k5_xboole_0 @ ( X302 @ k1_xboole_0 ) )
      = X302 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('54',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('55',plain,(
    ! [X302: $i] :
      ( ( k5_xboole_0 @ ( X302 @ o_0_0_xboole_0 ) )
      = X302 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k5_xboole_0 @ ( B @ A ) ) ) )).

thf('56',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( X9 @ X8 ) )
      = ( k5_xboole_0 @ ( X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ ( X1 @ ( k5_xboole_0 @ ( X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['52','57'])).

thf('59',plain,
    ( ( k6_subset_1 @ ( sk_A_2 @ sk_C_20 ) )
    = ( k5_xboole_0 @ ( k6_subset_1 @ ( sk_A_2 @ sk_B_8 ) @ sk_A_2 ) ) ),
    inference('sup+',[status(thm)],['47','58'])).

thf('60',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( X9 @ X8 ) )
      = ( k5_xboole_0 @ ( X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('61',plain,(
    ! [X235: $i,X236: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( X235 @ X236 ) @ X235 ) ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('62',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('63',plain,(
    ! [X235: $i,X236: $i] :
      ( r1_tarski @ ( k6_subset_1 @ ( X235 @ X236 ) @ X235 ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('64',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('65',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('66',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('68',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k6_subset_1 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ ( X0 @ X1 ) @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','68'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ) )).

thf('70',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k5_xboole_0 @ ( X35 @ X36 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X35 @ X36 ) @ ( k4_xboole_0 @ ( X36 @ X35 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('71',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('72',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('73',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k5_xboole_0 @ ( X35 @ X36 ) )
      = ( k2_xboole_0 @ ( k6_subset_1 @ ( X35 @ X36 ) @ ( k6_subset_1 @ ( X36 @ X35 ) ) ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( k6_subset_1 @ ( X1 @ X0 ) @ X1 ) )
      = ( k2_xboole_0 @ ( o_0_0_xboole_0 @ ( k6_subset_1 @ ( X1 @ ( k6_subset_1 @ ( X1 @ X0 ) ) ) ) ) ) ) ),
    inference('sup+',[status(thm)],['69','73'])).

thf('75',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( X9 @ X8 ) )
      = ( k5_xboole_0 @ ( X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('76',plain,(
    ! [X183: $i] :
      ( ( k2_xboole_0 @ ( X183 @ k1_xboole_0 ) )
      = X183 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('77',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('78',plain,(
    ! [X183: $i] :
      ( ( k2_xboole_0 @ ( X183 @ o_0_0_xboole_0 ) )
      = X183 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ ( o_0_0_xboole_0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ ( X1 @ ( k6_subset_1 @ ( X1 @ X0 ) ) ) )
      = ( k6_subset_1 @ ( X1 @ ( k6_subset_1 @ ( X1 @ X0 ) ) ) ) ) ),
    inference(demod,[status(thm)],['74','75','80'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k4_xboole_0 @ ( A @ B ) ) ) )
      = ( k3_xboole_0 @ ( A @ B ) ) ) )).

thf('82',plain,(
    ! [X266: $i,X267: $i] :
      ( ( k4_xboole_0 @ ( X266 @ ( k4_xboole_0 @ ( X266 @ X267 ) ) ) )
      = ( k3_xboole_0 @ ( X266 @ X267 ) ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('83',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('84',plain,(
    ! [X1521: $i,X1522: $i] :
      ( ( k6_subset_1 @ ( X1521 @ X1522 ) )
      = ( k4_xboole_0 @ ( X1521 @ X1522 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('85',plain,(
    ! [X266: $i,X267: $i] :
      ( ( k6_subset_1 @ ( X266 @ ( k6_subset_1 @ ( X266 @ X267 ) ) ) )
      = ( k3_xboole_0 @ ( X266 @ X267 ) ) ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('87',plain,
    ( ( k6_subset_1 @ ( sk_A_2 @ sk_C_20 ) )
    = ( k3_xboole_0 @ ( sk_B_8 @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['59','60','81','85','86'])).

thf('88',plain,
    ( ( k6_subset_1 @ ( sk_A_2 @ sk_C_20 ) )
    = sk_B_8 ),
    inference('sup+',[status(thm)],['9','87'])).

thf('89',plain,(
    sk_B_8
 != ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( k3_subset_1 @ ( sk_A_2 @ sk_C_20 ) )
    = ( k6_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('91',plain,(
    sk_B_8
 != ( k6_subset_1 @ ( sk_A_2 @ sk_C_20 ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['88','91'])).

%------------------------------------------------------------------------------
