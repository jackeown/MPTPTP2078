%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0084+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rzWm8trhXB

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:44 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   66 (  73 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :   10
%              Number of atoms          :  361 ( 418 expanded)
%              Number of equality atoms :   33 (  36 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_2_type,type,(
    sk_A_2: $i )).

thf(t77_xboole_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
        & ( r1_tarski @ ( A @ C ) )
        & ( r1_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
          & ( r1_tarski @ ( A @ C ) )
          & ( r1_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t77_xboole_1])).

thf('0',plain,(
    ~ ( r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ ( A @ B ) )
    <=> ( ( k3_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('3',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('4',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_xboole_0 @ ( X37 @ X38 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_xboole_0 @ ( X37 @ X38 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k3_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( A @ ( k3_xboole_0 @ ( A @ B ) ) ) )
      = ( k4_xboole_0 @ ( A @ B ) ) ) )).

thf('6',plain,(
    ! [X203: $i,X204: $i] :
      ( ( k4_xboole_0 @ ( X203 @ ( k3_xboole_0 @ ( X203 @ X204 ) ) ) )
      = ( k4_xboole_0 @ ( X203 @ X204 ) ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ ( sk_A_2 @ o_0_0_xboole_0 ) )
    = ( k4_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ ( A @ k1_xboole_0 ) )
      = A ) )).

thf('8',plain,(
    ! [X183: $i] :
      ( ( k4_xboole_0 @ ( X183 @ k1_xboole_0 ) )
      = X183 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    ! [X183: $i] :
      ( ( k4_xboole_0 @ ( X183 @ o_0_0_xboole_0 ) )
      = X183 ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( sk_A_2
    = ( k4_xboole_0 @ ( sk_A_2 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) ) ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( A @ B ) @ A ) ) )).

thf('12',plain,(
    ! [X114: $i,X115: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ ( X114 @ X115 ) @ X114 ) ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( r1_tarski @ ( A @ B ) ) ) )).

thf('13',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,(
    ! [X85: $i,X87: $i] :
      ( ( ( k4_xboole_0 @ ( X85 @ X87 ) )
        = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X85 @ X87 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ ( X0 @ X1 ) @ X0 ) )
      = o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t49_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( A @ ( k4_xboole_0 @ ( B @ C ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ C ) ) ) )).

thf('17',plain,(
    ! [X207: $i,X208: $i,X209: $i] :
      ( ( k3_xboole_0 @ ( X207 @ ( k4_xboole_0 @ ( X208 @ X209 ) ) ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ ( X207 @ X208 ) @ X209 ) ) ) ),
    inference(cnf,[status(esa)],[t49_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( X0 @ ( k4_xboole_0 @ ( X1 @ X0 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( sk_B_2 @ sk_C_5 ) @ sk_A_2 ) )
    = o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['11','18'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ C ) )
      = ( k3_xboole_0 @ ( A @ ( k3_xboole_0 @ ( B @ C ) ) ) ) ) )).

thf('20',plain,(
    ! [X111: $i,X112: $i,X113: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ ( X111 @ X112 ) @ X113 ) )
      = ( k3_xboole_0 @ ( X111 @ ( k3_xboole_0 @ ( X112 @ X113 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('21',plain,(
    r1_tarski @ ( sk_A_2 @ sk_C_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k3_xboole_0 @ ( A @ B ) )
        = A ) ) )).

thf('22',plain,(
    ! [X149: $i,X150: $i] :
      ( ( ( k3_xboole_0 @ ( X149 @ X150 ) )
        = X149 )
      | ~ ( r1_tarski @ ( X149 @ X150 ) ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('23',plain,
    ( ( k3_xboole_0 @ ( sk_A_2 @ sk_C_5 ) )
    = sk_A_2 ),
    inference('sup-',[status(thm)],['21','22'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( A @ B ) )
      = ( k3_xboole_0 @ ( B @ A ) ) ) )).

thf('24',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('25',plain,
    ( ( k3_xboole_0 @ ( sk_C_5 @ sk_A_2 ) )
    = sk_A_2 ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k3_xboole_0 @ ( sk_B_2 @ sk_A_2 ) )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['19','20','25'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ ( C @ B ) )
              & ( r2_hidden @ ( C @ A ) ) )
          & ( r1_xboole_0 @ ( A @ B ) ) )
      & ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ ( C @ A ) )
                & ( r2_hidden @ ( C @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X58: $i,X59: $i] :
      ( ( r1_xboole_0 @ ( X58 @ X59 ) )
      | ( r2_hidden @ ( sk_C_2 @ ( X59 @ X58 ) @ X58 ) ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( X10 @ X11 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ ( X7 @ X6 ) )
      = ( k3_xboole_0 @ ( X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t75_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( r1_xboole_0 @ ( A @ B ) )
        & ( r1_xboole_0 @ ( k3_xboole_0 @ ( A @ B ) @ B ) ) ) )).

thf('31',plain,(
    ! [X286: $i,X287: $i] :
      ( ( r1_xboole_0 @ ( X286 @ X287 ) )
      | ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( X286 @ X287 ) @ X287 ) ) ) ),
    inference(cnf,[status(esa)],[t75_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ ( X1 @ X0 ) @ X1 ) )
      | ( r1_xboole_0 @ ( X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k3_xboole_0 @ ( X0 @ X1 ) ) )
      | ( r1_xboole_0 @ ( X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ( r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('35',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('36',plain,(
    r1_xboole_0 @ ( sk_A_2 @ sk_B_2 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['0','36'])).

%------------------------------------------------------------------------------
