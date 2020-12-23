%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0598+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JE7I47oFhc

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:57 EST 2020

% Result     : Theorem 10.81s
% Output     : Refutation 10.81s
% Verified   : 
% Statistics : Number of formulae       :   31 (  37 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    8
%              Number of atoms          :  149 ( 221 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_34_type,type,(
    sk_C_34: $i )).

thf(sk_B_15_type,type,(
    sk_B_15: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_5_type,type,(
    sk_A_5: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t202_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ ( B @ A ) ) )
     => ! [C: $i] :
          ( ( r2_hidden @ ( C @ ( k2_relat_1 @ B ) ) )
         => ( r2_hidden @ ( C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v5_relat_1 @ ( B @ A ) ) )
       => ! [C: $i] :
            ( ( r2_hidden @ ( C @ ( k2_relat_1 @ B ) ) )
           => ( r2_hidden @ ( C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t202_relat_1])).

thf('0',plain,(
    ~ ( r2_hidden @ ( sk_C_34 @ sk_A_5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v5_relat_1 @ ( sk_B_15 @ sk_A_5 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ ( B @ A ) )
      <=> ( r1_tarski @ ( k2_relat_1 @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X2076: $i,X2077: $i] :
      ( ~ ( v5_relat_1 @ ( X2076 @ X2077 ) )
      | ( r1_tarski @ ( k2_relat_1 @ X2076 @ X2077 ) )
      | ~ ( v1_relat_1 @ X2076 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('3',plain,
    ( ~ ( v1_relat_1 @ sk_B_15 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_B_15 @ sk_A_5 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B_15 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B_15 @ sk_A_5 ) ),
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
    ( ( k2_xboole_0 @ ( k2_relat_1 @ sk_B_15 @ sk_A_5 ) )
    = sk_A_5 ),
    inference('sup-',[status(thm)],['5','6'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( A @ B ) )
      = ( k2_xboole_0 @ ( B @ A ) ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ ( X5 @ X4 ) )
      = ( k2_xboole_0 @ ( X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('9',plain,
    ( ( k2_xboole_0 @ ( sk_A_5 @ ( k2_relat_1 @ sk_B_15 ) ) )
    = sk_A_5 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( sk_C_34 @ ( k2_relat_1 @ sk_B_15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ ( A @ B ) ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ ( D @ C ) )
        <=> ( ( r2_hidden @ ( D @ A ) )
            | ( r2_hidden @ ( D @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( X17 @ X18 ) )
      | ( r2_hidden @ ( X17 @ X19 ) )
      | ( X19
       != ( k2_xboole_0 @ ( X20 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('12',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r2_hidden @ ( X17 @ ( k2_xboole_0 @ ( X20 @ X18 ) ) ) )
      | ~ ( r2_hidden @ ( X17 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_C_34 @ ( k2_xboole_0 @ ( X0 @ ( k2_relat_1 @ sk_B_15 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    r2_hidden @ ( sk_C_34 @ sk_A_5 ) ),
    inference('sup+',[status(thm)],['9','13'])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['0','14'])).

%------------------------------------------------------------------------------
