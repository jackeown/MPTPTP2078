%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0078+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CLPxBOHIBY

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:44 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   43 (  60 expanded)
%              Number of leaves         :   15 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :  222 ( 377 expanded)
%              Number of equality atoms :   33 (  56 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t71_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( ( k2_xboole_0 @ ( A @ B ) )
          = ( k2_xboole_0 @ ( C @ B ) ) )
        & ( r1_xboole_0 @ ( A @ B ) )
        & ( r1_xboole_0 @ ( C @ B ) ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( ( k2_xboole_0 @ ( A @ B ) )
            = ( k2_xboole_0 @ ( C @ B ) ) )
          & ( r1_xboole_0 @ ( A @ B ) )
          & ( r1_xboole_0 @ ( C @ B ) ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t71_xboole_1])).

thf('0',plain,(
    r1_xboole_0 @ ( sk_C_5 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,
    ( ( k3_xboole_0 @ ( sk_C_5 @ sk_B_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k3_xboole_0 @ ( A @ B ) ) ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('5',plain,(
    ! [X203: $i,X204: $i] :
      ( ( k4_xboole_0 @ ( X203 @ ( k3_xboole_0 @ ( X203 @ X204 ) ) ) )
      = ( k4_xboole_0 @ ( X203 @ X204 ) ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('6',plain,
    ( ( k4_xboole_0 @ ( sk_C_5 @ o_0_0_xboole_0 ) )
    = ( k4_xboole_0 @ ( sk_C_5 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('7',plain,(
    ! [X183: $i] :
      ( ( k4_xboole_0 @ ( X183 @ k1_xboole_0 ) )
      = X183 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('8',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('9',plain,(
    ! [X183: $i] :
      ( ( k4_xboole_0 @ ( X183 @ o_0_0_xboole_0 ) )
      = X183 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( sk_C_5
    = ( k4_xboole_0 @ ( sk_C_5 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,
    ( ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = ( k2_xboole_0 @ ( sk_C_5 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('12',plain,(
    ! [X185: $i,X186: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( X185 @ X186 ) @ X186 ) )
      = ( k4_xboole_0 @ ( X185 @ X186 ) ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('13',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_B_2 ) )
    = ( k4_xboole_0 @ ( sk_C_5 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X185: $i,X186: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( X185 @ X186 ) @ X186 ) )
      = ( k4_xboole_0 @ ( X185 @ X186 ) ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('15',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = ( k4_xboole_0 @ ( sk_C_5 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('18',plain,
    ( ( k3_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X203: $i,X204: $i] :
      ( ( k4_xboole_0 @ ( X203 @ ( k3_xboole_0 @ ( X203 @ X204 ) ) ) )
      = ( k4_xboole_0 @ ( X203 @ X204 ) ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('20',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ o_0_0_xboole_0 ) )
    = ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X183: $i] :
      ( ( k4_xboole_0 @ ( X183 @ o_0_0_xboole_0 ) )
      = X183 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('22',plain,
    ( sk_A_2
    = ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( sk_A_2
    = ( k4_xboole_0 @ ( sk_C_5 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['15','22'])).

thf('24',plain,(
    sk_A_2 = sk_C_5 ),
    inference('sup+',[status(thm)],['10','23'])).

thf('25',plain,(
    sk_A_2 != sk_C_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

%------------------------------------------------------------------------------
