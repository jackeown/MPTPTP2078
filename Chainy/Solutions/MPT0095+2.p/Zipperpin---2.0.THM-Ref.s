%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0095+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xDLhGqExnP

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:45 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :   31 (  59 expanded)
%              Number of leaves         :   11 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :  174 ( 395 expanded)
%              Number of equality atoms :   19 (  41 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t88_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ B ) )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_xboole_0 @ ( A @ B ) )
       => ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ B ) )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t88_xboole_1])).

thf('0',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k4_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('1',plain,(
    ! [X311: $i,X312: $i] :
      ( ( ( k4_xboole_0 @ ( X311 @ X312 ) )
        = X311 )
      | ~ ( r1_xboole_0 @ ( X311 @ X312 ) ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = sk_A_2 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ ( k4_xboole_0 @ ( B @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k5_xboole_0 @ ( X35 @ X36 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X35 @ X36 ) @ ( k4_xboole_0 @ ( X36 @ X35 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[d6_xboole_0])).

thf('4',plain,
    ( ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = ( k2_xboole_0 @ ( sk_A_2 @ ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( r1_xboole_0 @ ( B @ A ) ) ) )).

thf('6',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( X47 @ X48 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('7',plain,(
    r1_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X311: $i,X312: $i] :
      ( ( ( k4_xboole_0 @ ( X311 @ X312 ) )
        = X311 )
      | ~ ( r1_xboole_0 @ ( X311 @ X312 ) ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('9',plain,
    ( ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ B ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('11',plain,(
    ! [X185: $i,X186: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( X185 @ X186 ) @ X186 ) )
      = ( k4_xboole_0 @ ( X185 @ X186 ) ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_B_2 ) )
    = ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = sk_A_2 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_B_2 ) )
    = sk_A_2 ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ( k4_xboole_0 @ ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_B_2 ) )
 != sk_A_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = ( k2_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('17',plain,(
    ( k4_xboole_0 @ ( k5_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_B_2 ) )
 != sk_A_2 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['14','17'])).

%------------------------------------------------------------------------------
