%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0732+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iOUGGumsGJ

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:00 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :   26 (  32 expanded)
%              Number of leaves         :   11 (  14 expanded)
%              Depth                    :    7
%              Number of atoms          :  120 ( 186 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_60_type,type,(
    sk_C_60: $i )).

thf(sk_B_31_type,type,(
    sk_B_31: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_ordinal1_type,type,(
    v1_ordinal1: $i > $o )).

thf(sk_A_12_type,type,(
    sk_A_12: $i )).

thf(t19_ordinal1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_ordinal1 @ C )
     => ( ( ( r2_hidden @ ( A @ B ) )
          & ( r2_hidden @ ( B @ C ) ) )
       => ( r2_hidden @ ( A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_ordinal1 @ C )
       => ( ( ( r2_hidden @ ( A @ B ) )
            & ( r2_hidden @ ( B @ C ) ) )
         => ( r2_hidden @ ( A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t19_ordinal1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( sk_A_12 @ sk_C_60 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ ( sk_B_31 @ sk_C_60 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_ordinal1,axiom,(
    ! [A: $i] :
      ( ( v1_ordinal1 @ A )
    <=> ! [B: $i] :
          ( ( r2_hidden @ ( B @ A ) )
         => ( r1_tarski @ ( B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X3065: $i,X3066: $i] :
      ( ~ ( r2_hidden @ ( X3065 @ X3066 ) )
      | ( r1_tarski @ ( X3065 @ X3066 ) )
      | ~ ( v1_ordinal1 @ X3066 ) ) ),
    inference(cnf,[status(esa)],[d2_ordinal1])).

thf('3',plain,
    ( ~ ( v1_ordinal1 @ sk_C_60 )
    | ( r1_tarski @ ( sk_B_31 @ sk_C_60 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_ordinal1 @ sk_C_60 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r1_tarski @ ( sk_B_31 @ sk_C_60 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_xboole_0 @ ( A @ B ) )
        = B ) ) )).

thf('6',plain,(
    ! [X161: $i,X162: $i] :
      ( ( ( k2_xboole_0 @ ( X162 @ X161 ) )
        = X161 )
      | ~ ( r1_tarski @ ( X162 @ X161 ) ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ ( sk_B_31 @ sk_C_60 ) )
    = sk_C_60 ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    r2_hidden @ ( sk_A_12 @ sk_B_31 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( r2_hidden @ ( D @ A ) )
            | ( r2_hidden @ ( D @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( X17 @ X20 ) )
      | ( r2_hidden @ ( X17 @ X19 ) )
      | ( X19
       != ( k2_xboole_0 @ ( X20 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('10',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r2_hidden @ ( X17 @ ( k2_xboole_0 @ ( X20 @ X18 ) ) ) )
      | ~ ( r2_hidden @ ( X17 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_A_12 @ ( k2_xboole_0 @ ( sk_B_31 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_A_12 @ sk_C_60 ) ),
    inference('sup+',[status(thm)],['7','11'])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['0','12'])).

%------------------------------------------------------------------------------
