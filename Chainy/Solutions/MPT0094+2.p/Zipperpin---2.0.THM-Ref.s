%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0094+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2qpfYB6pcy

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:45 EST 2020

% Result     : Theorem 10.58s
% Output     : Refutation 10.58s
% Verified   : 
% Statistics : Number of formulae       :   25 (  28 expanded)
%              Number of leaves         :   11 (  13 expanded)
%              Depth                    :    7
%              Number of atoms          :  159 ( 194 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(t87_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( C @ A ) @ B ) )
        = ( k4_xboole_0 @ ( k2_xboole_0 @ ( C @ B ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_xboole_0 @ ( A @ B ) )
       => ( ( k2_xboole_0 @ ( k4_xboole_0 @ ( C @ A ) @ B ) )
          = ( k4_xboole_0 @ ( k2_xboole_0 @ ( C @ B ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_xboole_1])).

thf('0',plain,(
    ( k2_xboole_0 @ ( k4_xboole_0 @ ( sk_C_5 @ sk_A_2 ) @ sk_B_2 ) )
 != ( k4_xboole_0 @ ( k2_xboole_0 @ ( sk_C_5 @ sk_B_2 ) @ sk_A_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('3',plain,(
    ( k2_xboole_0 @ ( sk_B_2 @ ( k4_xboole_0 @ ( sk_C_5 @ sk_A_2 ) ) ) )
 != ( k4_xboole_0 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) @ sk_A_2 ) ) ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
     => ( r1_xboole_0 @ ( B @ A ) ) ) )).

thf('5',plain,(
    ! [X47: $i,X48: $i] :
      ( ( r1_xboole_0 @ ( X47 @ X48 ) )
      | ~ ( r1_xboole_0 @ ( X48 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('6',plain,(
    r1_xboole_0 @ ( sk_B_2 @ sk_A_2 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k4_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('7',plain,(
    ! [X311: $i,X312: $i] :
      ( ( ( k4_xboole_0 @ ( X311 @ X312 ) )
        = X311 )
      | ~ ( r1_xboole_0 @ ( X311 @ X312 ) ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('8',plain,
    ( ( k4_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
    = sk_B_2 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t42_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( A @ B ) @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( A @ C ) @ ( k4_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X190: $i,X191: $i,X192: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( X190 @ X192 ) @ X191 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ ( X190 @ X191 ) @ ( k4_xboole_0 @ ( X192 @ X191 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t42_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( sk_B_2 @ X0 ) @ sk_A_2 ) )
      = ( k2_xboole_0 @ ( sk_B_2 @ ( k4_xboole_0 @ ( X0 @ sk_A_2 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ( k2_xboole_0 @ ( sk_B_2 @ ( k4_xboole_0 @ ( sk_C_5 @ sk_A_2 ) ) ) )
 != ( k2_xboole_0 @ ( sk_B_2 @ ( k4_xboole_0 @ ( sk_C_5 @ sk_A_2 ) ) ) ) ),
    inference(demod,[status(thm)],['3','10'])).

thf('12',plain,(
    $false ),
    inference(simplify,[status(thm)],['11'])).

%------------------------------------------------------------------------------
