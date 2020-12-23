%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0318+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nlELHyEh9R

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:53 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   45 (  79 expanded)
%              Number of leaves         :   12 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  297 ( 542 expanded)
%              Number of equality atoms :   67 ( 123 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t130_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( A != k1_xboole_0 )
     => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B @ A ) )
         != k1_xboole_0 )
        & ( ( k2_zfmisc_1 @ ( A @ ( k1_tarski @ B ) ) )
         != k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( A != k1_xboole_0 )
       => ( ( ( k2_zfmisc_1 @ ( k1_tarski @ B @ A ) )
           != k1_xboole_0 )
          & ( ( k2_zfmisc_1 @ ( A @ ( k1_tarski @ B ) ) )
           != k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t130_zfmisc_1])).

thf('0',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_A_2 ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_zfmisc_1 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X1089: $i,X1090: $i] :
      ( ( X1089 = k1_xboole_0 )
      | ( X1090 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( X1090 @ X1089 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    ! [X1089: $i,X1090: $i] :
      ( ( X1089 = o_0_0_xboole_0 )
      | ( X1090 = o_0_0_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( X1090 @ X1089 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['2','3','4','5'])).

thf('7',plain,
    ( ( ( k1_xboole_0 != o_0_0_xboole_0 )
      | ( sk_A_2 = o_0_0_xboole_0 )
      | ( ( k1_tarski @ sk_B_2 )
        = o_0_0_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,
    ( ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( sk_A_2 = o_0_0_xboole_0 )
      | ( ( k1_tarski @ sk_B_2 )
        = o_0_0_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( ( k1_tarski @ sk_B_2 )
        = o_0_0_xboole_0 )
      | ( sk_A_2 = o_0_0_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    sk_A_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('13',plain,(
    sk_A_2 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ A ) )
      = A ) )).

thf('14',plain,(
    ! [X43: $i] :
      ( ( k2_xboole_0 @ ( X43 @ X43 ) )
      = X43 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A @ B ) )
     != k1_xboole_0 ) )).

thf('15',plain,(
    ! [X1252: $i,X1253: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1252 @ X1253 ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('16',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('17',plain,(
    ! [X1252: $i,X1253: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1252 @ X1253 ) )
     != o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( $false
   <= ( ( k2_zfmisc_1 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
      = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['10','13','18'])).

thf('20',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_A_2 ) )
      = k1_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_A_2 ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('21',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('22',plain,
    ( ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_A_2 ) )
      = o_0_0_xboole_0 )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_A_2 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1089: $i,X1090: $i] :
      ( ( X1089 = o_0_0_xboole_0 )
      | ( X1090 = o_0_0_xboole_0 )
      | ( ( k2_zfmisc_1 @ ( X1090 @ X1089 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['2','3','4','5'])).

thf('24',plain,
    ( ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
      | ( ( k1_tarski @ sk_B_2 )
        = o_0_0_xboole_0 )
      | ( sk_A_2 = o_0_0_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_A_2 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( sk_A_2 = o_0_0_xboole_0 )
      | ( ( k1_tarski @ sk_B_2 )
        = o_0_0_xboole_0 ) )
   <= ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_A_2 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('27',plain,(
    sk_A_2 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['11','12'])).

thf('28',plain,(
    ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_A_2 ) )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['25','26','27'])).

thf('29',plain,
    ( ( ( k2_zfmisc_1 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
      = k1_xboole_0 )
    | ( ( k2_zfmisc_1 @ ( k1_tarski @ sk_B_2 @ sk_A_2 ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('30',plain,
    ( ( k2_zfmisc_1 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['28','29'])).

thf('31',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['19','30'])).

%------------------------------------------------------------------------------
