%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0271+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.uzqSVdfRXm

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:52 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 108 expanded)
%              Number of leaves         :   13 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  346 ( 754 expanded)
%              Number of equality atoms :   47 ( 103 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t68_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A @ B ) )
        = k1_xboole_0 )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A @ B ) )
          = k1_xboole_0 )
      <=> ( r2_hidden @ ( A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t68_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
   <= ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,
    ( ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
     != o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
     != o_0_0_xboole_0 )
    | ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = o_0_0_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = o_0_0_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A @ B ) )
        = k1_xboole_0 )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('10',plain,(
    ! [X1014: $i,X1015: $i] :
      ( ( r2_hidden @ ( X1014 @ X1015 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1014 @ X1015 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('11',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('12',plain,(
    ! [X1014: $i,X1015: $i] :
      ( ( r2_hidden @ ( X1014 @ X1015 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1014 @ X1015 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
   <= ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
     != o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = o_0_0_xboole_0 ) ),
    inference(split,[status(esa)],['8'])).

thf('19',plain,(
    r2_hidden @ ( sk_A_2 @ sk_B_2 ) ),
    inference('sat_resolution*',[status(thm)],['5','17','18'])).

thf('20',plain,(
    r2_hidden @ ( sk_A_2 @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['1','19'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('21',plain,(
    ! [X993: $i,X995: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X993 @ X995 ) )
      | ~ ( r2_hidden @ ( X993 @ X995 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('22',plain,(
    r1_tarski @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('23',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('24',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('25',plain,(
    ! [X88: $i,X90: $i] :
      ( ( ( k4_xboole_0 @ ( X88 @ X90 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X88 @ X90 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['15'])).

thf('28',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('29',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
     != o_0_0_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('32',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = o_0_0_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
     != o_0_0_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
     != o_0_0_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('34',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
       != o_0_0_xboole_0 )
      & ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
     != k1_xboole_0 )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = o_0_0_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['5','17','35'])).

thf('37',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
 != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['29','36'])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['26','37'])).

%------------------------------------------------------------------------------
