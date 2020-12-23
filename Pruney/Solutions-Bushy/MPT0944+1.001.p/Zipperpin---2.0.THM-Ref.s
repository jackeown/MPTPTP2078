%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0944+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LdkHIquPIV

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:45 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   27 (  31 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  104 ( 136 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X3 ) )
      | ~ ( v3_ordinal1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t9_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ B @ A )
         => ( v2_wellord1 @ ( k1_wellord2 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( r1_tarski @ B @ A )
           => ( v2_wellord1 @ ( k1_wellord2 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_wellord2])).

thf('1',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X5 ) @ X4 )
        = ( k1_wellord2 @ X4 ) )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('3',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_A ) @ sk_B )
    = ( k1_wellord2 @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t32_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v2_wellord1 @ B )
       => ( v2_wellord1 @ ( k2_wellord1 @ B @ A ) ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v2_wellord1 @ X1 )
      | ( v2_wellord1 @ ( k2_wellord1 @ X1 @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t32_wellord1])).

thf('5',plain,
    ( ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('7',plain,
    ( ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['10','11'])).


%------------------------------------------------------------------------------
