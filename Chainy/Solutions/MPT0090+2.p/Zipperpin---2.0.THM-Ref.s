%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0090+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.1ygh4gYhHa

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:44 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   40 (  71 expanded)
%              Number of leaves         :   13 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  206 ( 443 expanded)
%              Number of equality atoms :   28 (  57 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t83_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k4_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_xboole_0 @ ( A @ B ) )
      <=> ( ( k4_xboole_0 @ ( A @ B ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t83_xboole_1])).

thf('0',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
      = sk_A_2 )
    | ( r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
   <= ( r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
     != sk_A_2 )
    | ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
     != sk_A_2 )
    | ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
      = sk_A_2 )
   <= ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
      = sk_A_2 ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ B ) ) )).

thf('5',plain,(
    ! [X297: $i,X298: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ ( X297 @ X298 ) @ X298 ) ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('6',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
   <= ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
      = sk_A_2 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
   <= ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['2'])).

thf('8',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    | ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
     != sk_A_2 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    | ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
      = sk_A_2 ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ),
    inference('sat_resolution*',[status(thm)],['3','8','9'])).

thf('11',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('12',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('13',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('14',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['11','14'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k3_xboole_0 @ ( A @ B ) ) ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('16',plain,(
    ! [X203: $i,X204: $i] :
      ( ( k4_xboole_0 @ ( X203 @ ( k3_xboole_0 @ ( X203 @ X204 ) ) ) )
      = ( k4_xboole_0 @ ( X203 @ X204 ) ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('17',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ o_0_0_xboole_0 ) )
    = ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('18',plain,(
    ! [X183: $i] :
      ( ( k4_xboole_0 @ ( X183 @ k1_xboole_0 ) )
      = X183 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('20',plain,(
    ! [X183: $i] :
      ( ( k4_xboole_0 @ ( X183 @ o_0_0_xboole_0 ) )
      = X183 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( sk_A_2
    = ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
     != sk_A_2 )
   <= ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
     != sk_A_2 ) ),
    inference(split,[status(esa)],['2'])).

thf('23',plain,(
    ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
 != sk_A_2 ),
    inference('sat_resolution*',[status(thm)],['3','8'])).

thf('24',plain,(
    ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
 != sk_A_2 ),
    inference(simpl_trail,[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['21','24'])).

%------------------------------------------------------------------------------
