%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0080+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Yes7G5hohy

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:44 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   45 (  56 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :  225 ( 305 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t73_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) )
        & ( r1_xboole_0 @ ( A @ C ) ) )
     => ( r1_tarski @ ( A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( r1_tarski @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) )
          & ( r1_xboole_0 @ ( A @ C ) ) )
       => ( r1_tarski @ ( A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t73_xboole_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('2',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ ( k2_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( A @ B ) @ C ) )
      = ( k4_xboole_0 @ ( A @ ( k2_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X187: $i,X188: $i,X189: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( X187 @ X188 ) @ X189 ) )
      = ( k4_xboole_0 @ ( X187 @ ( k2_xboole_0 @ ( X188 @ X189 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_C_5 ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X85: $i,X86: $i] :
      ( ( r1_tarski @ ( X85 @ X86 ) )
      | ( ( k4_xboole_0 @ ( X85 @ X86 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    ! [X85: $i,X86: $i] :
      ( ( r1_tarski @ ( X85 @ X86 ) )
      | ( ( k4_xboole_0 @ ( X85 @ X86 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r1_tarski @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_C_5 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    r1_tarski @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_C_5 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t68_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ~ ( ( r1_tarski @ ( C @ A ) )
          & ( r1_tarski @ ( C @ B ) )
          & ( r1_xboole_0 @ ( A @ B ) ) ) ) )).

thf('14',plain,(
    ! [X261: $i,X262: $i,X263: $i] :
      ( ~ ( r1_xboole_0 @ ( X261 @ X262 ) )
      | ( v1_xboole_0 @ X263 )
      | ~ ( r1_tarski @ ( X263 @ X261 ) )
      | ~ ( r1_tarski @ ( X263 @ X262 ) ) ) ),
    inference(cnf,[status(esa)],[t68_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( X0 @ sk_C_5 ) )
      | ~ ( r1_tarski @ ( X0 @ sk_A_2 ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) )
    | ~ ( r1_tarski @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) @ sk_A_2 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('17',plain,(
    ! [X174: $i,X175: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( X174 @ X175 ) @ X174 ) ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('18',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('19',plain,(
    ! [X46: $i] :
      ( ( X46 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('20',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('21',plain,(
    ! [X46: $i] :
      ( ( X46 = o_0_0_xboole_0 )
      | ~ ( v1_xboole_0 @ X46 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ sk_B_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X85: $i,X86: $i] :
      ( ( r1_tarski @ ( X85 @ X86 ) )
      | ( ( k4_xboole_0 @ ( X85 @ X86 ) )
       != o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('24',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r1_tarski @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r1_tarski @ ( sk_A_2 @ sk_B_2 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
