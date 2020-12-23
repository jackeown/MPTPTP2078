%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0957+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.N1m2W8HwRE

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:04 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :  105 ( 108 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_16_type,type,(
    sk_A_16: $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r8_relat_2_type,type,(
    r8_relat_2: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t30_wellord2,conjecture,(
    ! [A: $i] :
      ( r8_relat_2 @ ( k1_wellord2 @ A @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r8_relat_2 @ ( k1_wellord2 @ A @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t30_wellord2])).

thf('0',plain,(
    ~ ( r8_relat_2 @ ( k1_wellord2 @ sk_A_16 @ sk_A_16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( B
          = ( k1_wellord2 @ A ) )
      <=> ( ( ( k3_relat_1 @ B )
            = A )
          & ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ ( C @ A ) )
                & ( r2_hidden @ ( D @ A ) ) )
             => ( ( r2_hidden @ ( k4_tarski @ ( C @ D ) @ B ) )
              <=> ( r1_tarski @ ( C @ D ) ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X4428: $i,X4429: $i] :
      ( ( X4429
       != ( k1_wellord2 @ X4428 ) )
      | ( ( k3_relat_1 @ X4429 )
        = X4428 )
      | ~ ( v1_relat_1 @ X4429 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord2])).

thf('2',plain,(
    ! [X4428: $i] :
      ( ~ ( v1_relat_1 @ ( k1_wellord2 @ X4428 ) )
      | ( ( k3_relat_1 @ ( k1_wellord2 @ X4428 ) )
        = X4428 ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('3',plain,(
    ! [X4449: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X4449 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('4',plain,(
    ! [X4428: $i] :
      ( ( k3_relat_1 @ ( k1_wellord2 @ X4428 ) )
      = X4428 ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d16_relat_2,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v8_relat_2 @ A )
      <=> ( r8_relat_2 @ ( A @ ( k3_relat_1 @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X3262: $i] :
      ( ~ ( v8_relat_2 @ X3262 )
      | ( r8_relat_2 @ ( X3262 @ ( k3_relat_1 @ X3262 ) ) )
      | ~ ( v1_relat_1 @ X3262 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_2])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r8_relat_2 @ ( k1_wellord2 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v8_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X4449: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X4449 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf(t3_wellord2,axiom,(
    ! [A: $i] :
      ( v8_relat_2 @ ( k1_wellord2 @ A ) ) )).

thf('8',plain,(
    ! [X4618: $i] :
      ( v8_relat_2 @ ( k1_wellord2 @ X4618 ) ) ),
    inference(cnf,[status(esa)],[t3_wellord2])).

thf('9',plain,(
    ! [X0: $i] :
      ( r8_relat_2 @ ( k1_wellord2 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    $false ),
    inference(demod,[status(thm)],['0','9'])).

%------------------------------------------------------------------------------
