%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0942+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QhuqQTdK8a

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:04 EST 2020

% Result     : Theorem 28.84s
% Output     : Refutation 28.84s
% Verified   : 
% Statistics : Number of formulae       :   34 (  36 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :  130 ( 140 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_2_type,type,(
    v4_relat_2: $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(v3_ordinal1_type,type,(
    v3_ordinal1: $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(sk_A_16_type,type,(
    sk_A_16: $i )).

thf(v2_wellord1_type,type,(
    v2_wellord1: $i > $o )).

thf(v6_relat_2_type,type,(
    v6_relat_2: $i > $o )).

thf(v1_wellord1_type,type,(
    v1_wellord1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(t6_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v1_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf('0',plain,(
    ! [X4455: $i] :
      ( ( v1_wellord1 @ ( k1_wellord2 @ X4455 ) )
      | ~ ( v3_ordinal1 @ X4455 ) ) ),
    inference(cnf,[status(esa)],[t6_wellord2])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('1',plain,(
    ! [X4443: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X4443 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

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
    ! [X3281: $i] :
      ( ~ ( v1_relat_2 @ X3281 )
      | ~ ( v8_relat_2 @ X3281 )
      | ~ ( v4_relat_2 @ X3281 )
      | ~ ( v6_relat_2 @ X3281 )
      | ~ ( v1_wellord1 @ X3281 )
      | ( v2_wellord1 @ X3281 )
      | ~ ( v1_relat_1 @ X3281 ) ) ),
    inference(cnf,[status(esa)],[d4_wellord1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_wellord1 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v4_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v8_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t5_wellord2,axiom,(
    ! [A: $i] :
      ( v4_relat_2 @ ( k1_wellord2 @ A ) ) )).

thf('4',plain,(
    ! [X4454: $i] :
      ( v4_relat_2 @ ( k1_wellord2 @ X4454 ) ) ),
    inference(cnf,[status(esa)],[t5_wellord2])).

thf(t3_wellord2,axiom,(
    ! [A: $i] :
      ( v8_relat_2 @ ( k1_wellord2 @ A ) ) )).

thf('5',plain,(
    ! [X4452: $i] :
      ( v8_relat_2 @ ( k1_wellord2 @ X4452 ) ) ),
    inference(cnf,[status(esa)],[t3_wellord2])).

thf(t2_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_2 @ ( k1_wellord2 @ A ) ) )).

thf('6',plain,(
    ! [X4451: $i] :
      ( v1_relat_2 @ ( k1_wellord2 @ X4451 ) ) ),
    inference(cnf,[status(esa)],[t2_wellord2])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v1_wellord1 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v6_relat_2 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v3_ordinal1 @ X0 )
      | ~ ( v6_relat_2 @ ( k1_wellord2 @ X0 ) )
      | ( v2_wellord1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf(t4_wellord2,axiom,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v6_relat_2 @ ( k1_wellord2 @ A ) ) ) )).

thf('9',plain,(
    ! [X4453: $i] :
      ( ( v6_relat_2 @ ( k1_wellord2 @ X4453 ) )
      | ~ ( v3_ordinal1 @ X4453 ) ) ),
    inference(cnf,[status(esa)],[t4_wellord2])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_wellord1 @ ( k1_wellord2 @ X0 ) )
      | ~ ( v3_ordinal1 @ X0 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(t7_wellord2,conjecture,(
    ! [A: $i] :
      ( ( v3_ordinal1 @ A )
     => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v3_ordinal1 @ A )
       => ( v2_wellord1 @ ( k1_wellord2 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_wellord2])).

thf('11',plain,(
    ~ ( v2_wellord1 @ ( k1_wellord2 @ sk_A_16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ~ ( v3_ordinal1 @ sk_A_16 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v3_ordinal1 @ sk_A_16 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    $false ),
    inference(demod,[status(thm)],['12','13'])).

%------------------------------------------------------------------------------
