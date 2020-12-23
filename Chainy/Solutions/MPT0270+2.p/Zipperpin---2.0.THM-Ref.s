%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0270+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lOKPpEFqRm

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:52 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :   28 (  60 expanded)
%              Number of leaves         :    7 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :  197 ( 522 expanded)
%              Number of equality atoms :   20 (  53 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A @ B ) )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ ( A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A @ B ) )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ ( A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = ( k1_tarski @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
   <= ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = ( k1_tarski @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
   <= ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = ( k1_tarski @ sk_A_2 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = ( k1_tarski @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf(l33_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A @ B ) )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ ( A @ B ) ) ) )).

thf('6',plain,(
    ! [X1011: $i,X1012: $i] :
      ( ~ ( r2_hidden @ ( X1011 @ X1012 ) )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X1011 @ X1012 ) )
       != ( k1_tarski @ X1011 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('7',plain,
    ( ( ( ( k1_tarski @ sk_A_2 )
       != ( k1_tarski @ sk_A_2 ) )
      | ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = ( k1_tarski @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
      = ( k1_tarski @ sk_A_2 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
     != ( k1_tarski @ sk_A_2 ) )
    | ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['4','8'])).

thf('10',plain,(
    ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','9'])).

thf('11',plain,(
    ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf('12',plain,(
    ! [X1011: $i,X1013: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1011 @ X1013 ) )
        = ( k1_tarski @ X1011 ) )
      | ( r2_hidden @ ( X1011 @ X1013 ) ) ) ),
    inference(cnf,[status(esa)],[l33_zfmisc_1])).

thf('13',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
     != ( k1_tarski @ sk_A_2 ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
     != ( k1_tarski @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('14',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
     != ( k1_tarski @ sk_A_2 ) )
    | ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('15',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
 != ( k1_tarski @ sk_A_2 ) ),
    inference('sat_resolution*',[status(thm)],['2','9','14'])).

thf('16',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
 != ( k1_tarski @ sk_A_2 ) ),
    inference(simpl_trail,[status(thm)],['13','15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_A_2 )
     != ( k1_tarski @ sk_A_2 ) )
    | ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,(
    r2_hidden @ ( sk_A_2 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['11','18'])).

%------------------------------------------------------------------------------
