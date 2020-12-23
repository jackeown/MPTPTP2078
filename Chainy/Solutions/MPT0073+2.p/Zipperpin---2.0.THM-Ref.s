%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0073+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jrPzv3Cqev

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  97 expanded)
%              Number of leaves         :   10 (  29 expanded)
%              Depth                    :   12
%              Number of atoms          :  208 ( 607 expanded)
%              Number of equality atoms :   38 ( 112 expanded)
%              Maximal formula depth    :    9 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t66_xboole_1,conjecture,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ ( A @ A ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ A ) )
          & ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( ( A != k1_xboole_0 )
            & ( r1_xboole_0 @ ( A @ A ) ) )
        & ~ ( ~ ( r1_xboole_0 @ ( A @ A ) )
            & ( A = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t66_xboole_1])).

thf('0',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ sk_A_2 ) )
    | ( sk_A_2 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ sk_A_2 ) )
    | ( sk_A_2 = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ sk_A_2 ) )
   <= ( r1_xboole_0 @ ( sk_A_2 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ sk_A_2 ) )
    | ( sk_A_2 = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ sk_A_2 ) )
    | ( sk_A_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ ( A @ k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X255: $i] :
      ( r1_xboole_0 @ ( X255 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('7',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('8',plain,(
    ! [X255: $i] :
      ( r1_xboole_0 @ ( X255 @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_A_2 = k1_xboole_0 )
   <= ( sk_A_2 = k1_xboole_0 ) ),
    inference(split,[status(esa)],['4'])).

thf('10',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('11',plain,
    ( ( sk_A_2 = o_0_0_xboole_0 )
   <= ( sk_A_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( sk_A_2 != k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_A_2 ) )
   <= ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ~ ( r1_xboole_0 @ ( sk_A_2 @ o_0_0_xboole_0 ) )
   <= ( ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_A_2 ) )
      & ( sk_A_2 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,
    ( ( sk_A_2 = o_0_0_xboole_0 )
   <= ( sk_A_2 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('16',plain,
    ( ~ ( r1_xboole_0 @ ( o_0_0_xboole_0 @ o_0_0_xboole_0 ) )
   <= ( ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_A_2 ) )
      & ( sk_A_2 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( sk_A_2 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( sk_A_2 @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['8','16'])).

thf('18',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_A_2 ) ),
    inference('sat_resolution*',[status(thm)],['5','17'])).

thf('19',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_A_2 ) ),
    inference(simpl_trail,[status(thm)],['3','18'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('20',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('21',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('22',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k3_xboole_0 @ ( sk_A_2 @ sk_A_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['19','22'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ A ) )
      = A ) )).

thf('24',plain,(
    ! [X44: $i] :
      ( ( k3_xboole_0 @ ( X44 @ X44 ) )
      = X44 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('25',plain,(
    sk_A_2 = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( sk_A_2 != k1_xboole_0 )
   <= ( sk_A_2 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('27',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('28',plain,
    ( ( sk_A_2 != o_0_0_xboole_0 )
   <= ( sk_A_2 != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_A_2 != k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_A_2 ) ) ),
    inference(split,[status(esa)],['12'])).

thf('30',plain,(
    sk_A_2 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['5','17','29'])).

thf('31',plain,(
    sk_A_2 != o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['28','30'])).

thf('32',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['25','31'])).

%------------------------------------------------------------------------------
