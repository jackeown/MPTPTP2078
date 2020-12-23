%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0942+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dZfXA8GHfX

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:45 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   35 (  39 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    8
%              Number of atoms          :  124 ( 144 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(t4_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v6_relat_2 @ ( k1_wellord2 @ A ) ) ) )).

thf('0',plain,(
    ! [X4: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X4 ) )
      | ~ ( v3_ordinal1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_wellord2])).

thf(t6_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v1_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( v1_wellord1 @ ( k1_wellord2 @ X6 ) )
      | ~ ( v3_ordinal1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t6_wellord2])).

thf(d4_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( v2_wellord1 @ A )
      <=> ( ( v1_relat_2 @ A )
          & ( v8_relat_2 @ A )
          & ( v4_relat_2 @ A )
          & ( v6_relat_2 @ A )
          & ( v1_wellord1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( v4_relat_2 @ X0 )
      | ~ ( v6_relat_2 @ X0 )
      | ~ ( v1_wellord1 @ X0 )
      | ( v2_wellord1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf(t7_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_wellord2])).

thf('3',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v6_relat_2 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v4_relat_2 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v8_relat_2 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v1_relat_2 @ ( k1_wellord2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('5',plain,(
    ! [X1: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf(t5_wellord2,axiom,(
    ! [A: $i] :
      ( v4_relat_2 @ ( k1_wellord2 @ A ) ) )).

thf('6',plain,(
    ! [X5: $i] :
      ( v4_relat_2 @ ( k1_wellord2 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t5_wellord2])).

thf(t3_wellord2,axiom,(
    ! [A: $i] :
      ( v8_relat_2 @ ( k1_wellord2 @ A ) ) )).

thf('7',plain,(
    ! [X3: $i] :
      ( v8_relat_2 @ ( k1_wellord2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_wellord2])).

thf(t2_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_2 @ ( k1_wellord2 @ A ) ) )).

thf('8',plain,(
    ! [X2: $i] :
      ( v1_relat_2 @ ( k1_wellord2 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_wellord2])).

thf('9',plain,
    ( ~ ( v1_wellord1 @ ( k1_wellord2 @ sk_A ) )
    | ~ ( v6_relat_2 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,
    ( ~ ( v3_ordinal1 @ sk_A )
    | ~ ( v6_relat_2 @ ( k1_wellord2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf('11',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ~ ( v6_relat_2 @ ( k1_wellord2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v3_ordinal1 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','12'])).

thf('14',plain,(
    v3_ordinal1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    $false ),
    inference(demod,[status(thm)],['13','14'])).


%------------------------------------------------------------------------------
