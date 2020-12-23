%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0269+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nrm08tSE7b

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:52 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   56 (  78 expanded)
%              Number of leaves         :   18 (  30 expanded)
%              Depth                    :   17
%              Number of atoms          :  299 ( 455 expanded)
%              Number of equality atoms :   45 (  83 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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

thf(t66_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( ( k4_xboole_0 @ ( A @ ( k1_tarski @ B ) ) )
          = k1_xboole_0 )
        & ( A != k1_xboole_0 )
        & ( A
         != ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( ( k4_xboole_0 @ ( A @ ( k1_tarski @ B ) ) )
            = k1_xboole_0 )
          & ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_zfmisc_1])).

thf('3',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('6',plain,(
    ! [X88: $i,X89: $i] :
      ( ( r1_tarski @ ( X88 @ X89 ) )
      | ( ( k4_xboole_0 @ ( X88 @ X89 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,(
    ! [X88: $i,X89: $i] :
      ( ( r1_tarski @ ( X88 @ X89 ) )
      | ( ( k4_xboole_0 @ ( X88 @ X89 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    r1_tarski @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( r2_hidden @ ( C @ B ) ) ) ) )).

thf('11',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( X13 @ X14 ) )
      | ( r2_hidden @ ( X13 @ X15 ) )
      | ~ ( r1_tarski @ ( X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( X0 @ ( k1_tarski @ sk_B_2 ) ) )
      | ~ ( r2_hidden @ ( X0 @ sk_A_2 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( sk_A_2 = o_0_0_xboole_0 )
    | ( r2_hidden @ ( sk_B_1 @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['2','12'])).

thf('14',plain,(
    sk_A_2 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,(
    sk_A_2 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ ( sk_B_1 @ sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','16'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ B ) )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('18',plain,(
    ! [X993: $i,X995: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X993 @ X995 ) )
      | ~ ( r2_hidden @ ( X993 @ X995 ) ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('19',plain,(
    r1_tarski @ ( k1_tarski @ ( sk_B_1 @ sk_A_2 ) @ ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A @ ( k1_tarski @ B ) ) )
     => ( A = B ) ) )).

thf('20',plain,(
    ! [X1066: $i,X1067: $i] :
      ( ( X1067 = X1066 )
      | ~ ( r1_tarski @ ( k1_tarski @ X1067 @ ( k1_tarski @ X1066 ) ) ) ) ),
    inference(cnf,[status(esa)],[t24_zfmisc_1])).

thf('21',plain,
    ( ( sk_B_1 @ sk_A_2 )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X77: $i] :
      ( ( X77 = o_0_0_xboole_0 )
      | ( r2_hidden @ ( sk_B_1 @ X77 @ X77 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_B_2 @ sk_A_2 ) )
    | ( sk_A_2 = o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    sk_A_2 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['14','15'])).

thf('25',plain,(
    r2_hidden @ ( sk_B_2 @ sk_A_2 ) ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

thf(l35_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A @ B ) )
        = k1_xboole_0 )
    <=> ( r2_hidden @ ( A @ B ) ) ) )).

thf('26',plain,(
    ! [X1014: $i,X1016: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1014 @ X1016 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( X1014 @ X1016 ) ) ) ),
    inference(cnf,[status(esa)],[l35_zfmisc_1])).

thf('27',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('28',plain,(
    ! [X1014: $i,X1016: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1014 @ X1016 ) )
        = o_0_0_xboole_0 )
      | ~ ( r2_hidden @ ( X1014 @ X1016 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_B_2 @ sk_A_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['25','28'])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = ( k4_xboole_0 @ ( B @ A ) ) )
     => ( A = B ) ) )).

thf('30',plain,(
    ! [X223: $i,X224: $i] :
      ( ( X224 = X223 )
      | ( ( k4_xboole_0 @ ( X224 @ X223 ) )
       != ( k4_xboole_0 @ ( X223 @ X224 ) ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('31',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
     != o_0_0_xboole_0 )
    | ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ ( k1_tarski @ sk_B_2 ) ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf('33',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( sk_A_2
      = ( k1_tarski @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( sk_A_2
    = ( k1_tarski @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    sk_A_2
 != ( k1_tarski @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['34','35'])).

%------------------------------------------------------------------------------
