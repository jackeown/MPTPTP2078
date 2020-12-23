%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0044+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VJr6f5kIWv

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  79 expanded)
%              Number of leaves         :    9 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  208 ( 506 expanded)
%              Number of equality atoms :   31 (  74 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(t37_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( A @ B ) )
          = k1_xboole_0 )
      <=> ( r1_tarski @ ( A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_xboole_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) )
    | ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) )
   <= ~ ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) )
    | ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) )
    | ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) )
   <= ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('5',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('6',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('7',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
      = o_0_0_xboole_0 )
   <= ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('11',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
     != o_0_0_xboole_0 )
   <= ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
       != k1_xboole_0 )
      & ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ~ ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sat_resolution*',[status(thm)],['2','13'])).

thf('15',plain,(
    ~ ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(simpl_trail,[status(thm)],['1','14'])).

thf('16',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('17',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('18',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
      = o_0_0_xboole_0 )
   <= ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
      = k1_xboole_0 )
    | ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(split,[status(esa)],['3'])).

thf('20',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','13','19'])).

thf('21',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X85: $i,X86: $i] :
      ( ( r1_tarski @ ( X85 @ X86 ) )
      | ( ( k4_xboole_0 @ ( X85 @ X86 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('23',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('24',plain,(
    ! [X85: $i,X86: $i] :
      ( ( r1_tarski @ ( X85 @ X86 ) )
      | ( ( k4_xboole_0 @ ( X85 @ X86 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    $false ),
    inference(demod,[status(thm)],['15','26'])).

%------------------------------------------------------------------------------
