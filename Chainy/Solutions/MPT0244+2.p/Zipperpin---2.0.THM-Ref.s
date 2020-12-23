%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0244+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hroS3Bl4Cc

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:51 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   53 ( 162 expanded)
%              Number of leaves         :   11 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  298 (1134 expanded)
%              Number of equality atoms :   49 ( 199 expanded)
%              Maximal formula depth    :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t39_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ ( k1_tarski @ B ) ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( A @ ( k1_tarski @ B ) ) )
      <=> ( ( A = k1_xboole_0 )
          | ( A
            = ( k1_tarski @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t39_zfmisc_1])).

thf('0',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
    | ( sk_A_2 = k1_xboole_0 )
    | ( r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
   <= ( r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( sk_A_2 != k1_xboole_0 )
    | ~ ( r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
   <= ~ ( r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
    | ( sk_A_2 = k1_xboole_0 )
    | ( r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
    | ( sk_A_2 = o_0_0_xboole_0 )
    | ( r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_A_2 != k1_xboole_0 )
   <= ( sk_A_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,
    ( ( sk_A_2 != o_0_0_xboole_0 )
   <= ( sk_A_2 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_A_2 != k1_xboole_0 )
    | ~ ( r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ A ) ) )).

thf('11',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( k1_xboole_0 @ X216 ) ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('12',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('13',plain,(
    ! [X216: $i] :
      ( r1_tarski @ ( o_0_0_xboole_0 @ X216 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,
    ( ( sk_A_2 = k1_xboole_0 )
   <= ( sk_A_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( sk_A_2 = o_0_0_xboole_0 )
   <= ( sk_A_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
   <= ~ ( r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('18',plain,
    ( ~ ( r1_tarski @ ( o_0_0_xboole_0 @ ( k1_tarski @ sk_B_2 ) ) )
   <= ( ~ ( r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
      & ( sk_A_2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
    | ( sk_A_2 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    sk_A_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['10','19'])).

thf('21',plain,(
    sk_A_2 != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['9','20'])).

thf('22',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
    | ( r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['6','21'])).

thf('23',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
   <= ~ ( r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(split,[status(esa)],['2'])).

thf('24',plain,
    ( ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) )
   <= ~ ( r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ ( A @ B ) )
        & ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('25',plain,(
    ! [X78: $i,X79: $i] :
      ( ( r1_tarski @ ( X78 @ X79 ) )
      | ( X78 != X79 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X79: $i] :
      ( r1_tarski @ ( X79 @ X79 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['3','24','26'])).

thf('28',plain,(
    r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['27'])).

thf('29',plain,(
    r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(simpl_trail,[status(thm)],['1','28'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ ( k1_tarski @ B ) ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('30',plain,(
    ! [X1018: $i,X1019: $i] :
      ( ( X1019
        = ( k1_tarski @ X1018 ) )
      | ( X1019 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X1019 @ ( k1_tarski @ X1018 ) ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('31',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('32',plain,(
    ! [X1018: $i,X1019: $i] :
      ( ( X1019
        = ( k1_tarski @ X1018 ) )
      | ( X1019 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X1019 @ ( k1_tarski @ X1018 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_A_2 = o_0_0_xboole_0 )
    | ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ( sk_A_2
     != ( k1_tarski @ sk_B_2 ) )
    | ~ ( r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_A_2
     != ( k1_tarski @ sk_B_2 ) )
   <= ( sk_A_2
     != ( k1_tarski @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['34'])).

thf('36',plain,
    ( ( sk_A_2
     != ( k1_tarski @ sk_B_2 ) )
    | ~ ( r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference(split,[status(esa)],['34'])).

thf('37',plain,(
    sk_A_2
 != ( k1_tarski @ sk_B_2 ) ),
    inference('sat_resolution*',[status(thm)],['27','36'])).

thf('38',plain,(
    sk_A_2
 != ( k1_tarski @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['35','37'])).

thf('39',plain,(
    sk_A_2 != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['9','20'])).

thf('40',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['33','38','39'])).

%------------------------------------------------------------------------------
