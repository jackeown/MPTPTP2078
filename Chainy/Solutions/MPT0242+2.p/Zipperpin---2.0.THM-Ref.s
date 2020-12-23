%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0242+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cHJRipp5Fu

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   23 (  38 expanded)
%              Number of leaves         :    7 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :  120 ( 225 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t37_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
      <=> ( r2_hidden @ ( A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( r1_tarski @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
   <= ( r1_tarski @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['2'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('4',plain,(
    ! [X993: $i,X994: $i] :
      ( ( r2_hidden @ ( X993 @ X994 ) )
      | ~ ( r1_tarski @ ( k1_tarski @ X993 @ X994 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('5',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
   <= ( r1_tarski @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
   <= ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ~ ( r1_tarski @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( r1_tarski @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('9',plain,
    ( ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
   <= ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('10',plain,(
    ! [X993: $i,X995: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X993 @ X995 ) )
      | ~ ( r2_hidden @ ( X993 @ X995 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('11',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
   <= ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( r1_tarski @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) )
   <= ~ ( r1_tarski @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,
    ( ~ ( r2_hidden @ ( sk_A_2 @ sk_B_2 ) )
    | ( r1_tarski @ ( k1_tarski @ sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','7','8','13'])).

%------------------------------------------------------------------------------
