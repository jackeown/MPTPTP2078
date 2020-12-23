%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0545+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4jrvUfTLBj

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:56 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :   20 (  24 expanded)
%              Number of leaves         :   10 (  12 expanded)
%              Depth                    :    6
%              Number of atoms          :   83 ( 123 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_14_type,type,(
    sk_B_14: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_5_type,type,(
    sk_A_5: $i )).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ ( B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('0',plain,(
    ! [X2253: $i,X2254: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( X2253 @ X2254 ) @ ( k2_relat_1 @ X2253 ) ) )
      | ~ ( v1_relat_1 @ X2253 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ ( A @ ( k1_relat_1 @ A ) ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X2257: $i] :
      ( ( ( k9_relat_1 @ ( X2257 @ ( k1_relat_1 @ X2257 ) ) )
        = ( k2_relat_1 @ X2257 ) )
      | ~ ( v1_relat_1 @ X2257 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t147_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ ( B @ A ) @ ( k9_relat_1 @ ( B @ ( k1_relat_1 @ B ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( r1_tarski @ ( k9_relat_1 @ ( B @ A ) @ ( k9_relat_1 @ ( B @ ( k1_relat_1 @ B ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t147_relat_1])).

thf('2',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ ( sk_B_14 @ sk_A_5 ) @ ( k9_relat_1 @ ( sk_B_14 @ ( k1_relat_1 @ sk_B_14 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ ( sk_B_14 @ sk_A_5 ) @ ( k2_relat_1 @ sk_B_14 ) ) )
    | ~ ( v1_relat_1 @ sk_B_14 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_B_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ ( sk_B_14 @ sk_A_5 ) @ ( k2_relat_1 @ sk_B_14 ) ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_relat_1 @ sk_B_14 ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf('7',plain,(
    v1_relat_1 @ sk_B_14 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    $false ),
    inference(demod,[status(thm)],['6','7'])).

%------------------------------------------------------------------------------
