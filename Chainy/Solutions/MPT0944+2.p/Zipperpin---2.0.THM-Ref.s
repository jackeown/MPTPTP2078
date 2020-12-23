%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0944+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0soCXrlz6C

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:04 EST 2020

% Result     : Theorem 52.20s
% Output     : Refutation 52.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  31 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :  104 ( 136 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_16_type,type,(
    sk_A_16: $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_82_type,type,(
    sk_B_82: $i )).

thf(t7_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('0',plain,(
    ! [X4456: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X4456 ) )
      | ~ ( v3_ordinal1 @ X4456 ) ) ),
    inference(cnf,[status(esa)],[t7_wellord2])).

thf(t9_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ ( B @ A ) )
         => ( v2_wellord1 @ ( k1_wellord2 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ! [B: $i] :
            ( ( r1_tarski @ ( B @ A ) )
           => ( v2_wellord1 @ ( k1_wellord2 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_wellord2])).

thf('1',plain,(
    r1_tarski @ ( sk_B_82 @ sk_A_16 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B @ A ) )
        = ( k1_wellord2 @ A ) ) ) )).

thf('2',plain,(
    ! [X4457: $i,X4458: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X4458 @ X4457 ) )
        = ( k1_wellord2 @ X4457 ) )
      | ~ ( r1_tarski @ ( X4457 @ X4458 ) ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('3',plain,
    ( ( k2_wellord1 @ ( k1_wellord2 @ sk_A_16 @ sk_B_82 ) )
    = ( k1_wellord2 @ sk_B_82 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t32_wellord1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v2_wellord1 @ B )
       => ( v2_wellord1 @ ( k2_wellord1 @ ( B @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X3424: $i,X3425: $i] :
      ( ~ ( v2_wellord1 @ X3424 )
      | ( v2_wellord1 @ ( k2_wellord1 @ ( X3424 @ X3425 ) ) )
      | ~ ( v1_relat_1 @ X3424 ) ) ),
    inference(cnf,[status(esa)],[t32_wellord1])).

thf('5',plain,
    ( ( v2_wellord1 @ ( k1_wellord2 @ sk_B_82 ) )
    | ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A_16 ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A_16 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('6',plain,(
    ! [X4443: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X4443 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('7',plain,
    ( ( v2_wellord1 @ ( k1_wellord2 @ sk_B_82 ) )
    | ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A_16 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_B_82 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A_16 ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v3_ordinal1 @ sk_A_16 ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf('11',plain,(
    v3_ordinal1 @ sk_A_16 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    $false ),
    inference(demod,[status(thm)],['10','11'])).

%------------------------------------------------------------------------------
