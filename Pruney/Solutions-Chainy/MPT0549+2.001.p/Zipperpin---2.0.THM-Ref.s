%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tnQogTfkUm

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 493 expanded)
%              Number of leaves         :   31 ( 159 expanded)
%              Depth                    :   25
%              Number of atoms          :  766 (3361 expanded)
%              Number of equality atoms :   69 ( 387 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(t151_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 )
        <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t151_relat_1])).

thf('0',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 )
      | ( ( k7_relat_1 @ X21 @ X22 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('6',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('7',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 )
      | ( ( k7_relat_1 @ X21 @ X22 )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( ~ ( v1_relat_1 @ sk_B )
      | ( ( k7_relat_1 @ sk_B @ sk_A )
        = o_0_0_xboole_0 ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k7_relat_1 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) )
        = ( k9_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('12',plain,
    ( ( ( ( k2_relat_1 @ o_0_0_xboole_0 )
        = ( k9_relat_1 @ sk_B @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_B ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('13',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('16',plain,
    ( ( k2_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( o_0_0_xboole_0
      = ( k9_relat_1 @ sk_B @ sk_A ) )
   <= ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['12','16','17'])).

thf('19',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( o_0_0_xboole_0 != k1_xboole_0 )
   <= ( ( ( k9_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('22',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
   <= ( ( ( k9_relat_1 @ sk_B @ sk_A )
       != k1_xboole_0 )
      & ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','23'])).

thf('25',plain,(
    ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','24'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('26',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('27',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X18: $i] :
      ( ( ( k9_relat_1 @ X18 @ ( k1_relat_1 @ X18 ) )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('29',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf('30',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('31',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = o_0_0_xboole_0 )
   <= ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( ( k9_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('33',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','23','32'])).

thf('34',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) )
        = ( k9_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X16 @ X17 ) @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['34','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) @ X0 ) @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['28','42'])).

thf('44',plain,
    ( ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ o_0_0_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','43'])).

thf('45',plain,
    ( ( k9_relat_1 @ sk_B @ sk_A )
    = o_0_0_xboole_0 ),
    inference(simpl_trail,[status(thm)],['31','33'])).

thf('46',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('47',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X19 @ X20 ) )
        = ( k9_relat_1 @ X19 @ X20 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('48',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_xboole_0 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['45','51'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('53',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('54',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('55',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('56',plain,
    ( ( k6_relat_1 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['53','54','55'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('57',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('58',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['56','57'])).

thf(t137_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ) )).

thf('59',plain,(
    ! [X15: $i] :
      ( ( ( k8_relat_1 @ k1_xboole_0 @ X15 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t137_relat_1])).

thf('60',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('61',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('62',plain,(
    ! [X15: $i] :
      ( ( ( k8_relat_1 @ o_0_0_xboole_0 @ X15 )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( k8_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0 )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['58','62'])).

thf(t117_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ) )).

thf('64',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ ( k8_relat_1 @ X11 @ X12 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t117_relat_1])).

thf('65',plain,
    ( ( r1_tarski @ o_0_0_xboole_0 @ o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ o_0_0_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ o_0_0_xboole_0 ),
    inference('sup+',[status(thm)],['56','57'])).

thf('67',plain,(
    r1_tarski @ o_0_0_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['65','66'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('69',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('71',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['67','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['52','73','74'])).

thf('76',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) ) @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['44','75'])).

thf(t125_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k8_relat_1 @ A @ B )
          = B ) ) ) )).

thf('77',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ X14 )
      | ( ( k8_relat_1 @ X14 @ X13 )
        = X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t125_relat_1])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    | ( ( k8_relat_1 @ o_0_0_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) )
      = ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['52','73','74'])).

thf('80',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('81',plain,(
    ! [X15: $i] :
      ( ( ( k8_relat_1 @ o_0_0_xboole_0 @ X15 )
        = o_0_0_xboole_0 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k8_relat_1 @ o_0_0_xboole_0 @ X0 )
        = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( k8_relat_1 @ o_0_0_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    | ( o_0_0_xboole_0
      = ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['78','83'])).

thf('85',plain,
    ( ~ ( v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) )
    | ( o_0_0_xboole_0
      = ( k7_relat_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['26','84'])).

thf('86',plain,(
    v1_xboole_0 @ ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['52','73','74'])).

thf('87',plain,
    ( o_0_0_xboole_0
    = ( k7_relat_1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X21 @ X22 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('89',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('90',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k7_relat_1 @ X21 @ X22 )
       != o_0_0_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['87','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ( o_0_0_xboole_0 != o_0_0_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['25','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tnQogTfkUm
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:18:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 253 iterations in 0.098s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.55  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.55  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.55  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(t151_relat_1, conjecture,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.55         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i]:
% 0.20/0.55        ( ( v1_relat_1 @ B ) =>
% 0.20/0.55          ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.55            ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t151_relat_1])).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.20/0.55        | ((k9_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain,
% 0.20/0.55      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.20/0.55         <= (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.20/0.55       ~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.20/0.55        | ((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.20/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.55      inference('split', [status(esa)], ['3'])).
% 0.20/0.55  thf(t95_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.55         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.55  thf('5', plain,
% 0.20/0.55      (![X21 : $i, X22 : $i]:
% 0.20/0.55         (~ (r1_xboole_0 @ (k1_relat_1 @ X21) @ X22)
% 0.20/0.55          | ((k7_relat_1 @ X21 @ X22) = (k1_xboole_0))
% 0.20/0.55          | ~ (v1_relat_1 @ X21))),
% 0.20/0.55      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.20/0.55  thf(d2_xboole_0, axiom, (( k1_xboole_0 ) = ( o_0_0_xboole_0 ))).
% 0.20/0.55  thf('6', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (![X21 : $i, X22 : $i]:
% 0.20/0.55         (~ (r1_xboole_0 @ (k1_relat_1 @ X21) @ X22)
% 0.20/0.55          | ((k7_relat_1 @ X21 @ X22) = (o_0_0_xboole_0))
% 0.20/0.55          | ~ (v1_relat_1 @ X21))),
% 0.20/0.55      inference('demod', [status(thm)], ['5', '6'])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (((~ (v1_relat_1 @ sk_B)
% 0.20/0.55         | ((k7_relat_1 @ sk_B @ sk_A) = (o_0_0_xboole_0))))
% 0.20/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['4', '7'])).
% 0.20/0.55  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      ((((k7_relat_1 @ sk_B @ sk_A) = (o_0_0_xboole_0)))
% 0.20/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.55  thf(t148_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X19 : $i, X20 : $i]:
% 0.20/0.55         (((k2_relat_1 @ (k7_relat_1 @ X19 @ X20)) = (k9_relat_1 @ X19 @ X20))
% 0.20/0.55          | ~ (v1_relat_1 @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (((((k2_relat_1 @ o_0_0_xboole_0) = (k9_relat_1 @ sk_B @ sk_A))
% 0.20/0.55         | ~ (v1_relat_1 @ sk_B)))
% 0.20/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['10', '11'])).
% 0.20/0.55  thf(t60_relat_1, axiom,
% 0.20/0.55    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.20/0.55     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.55  thf('13', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.20/0.55  thf('14', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.55  thf('15', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.55  thf('16', plain, (((k2_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.55      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.20/0.55  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      ((((o_0_0_xboole_0) = (k9_relat_1 @ sk_B @ sk_A)))
% 0.20/0.55         <= (((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '16', '17'])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      ((((k9_relat_1 @ sk_B @ sk_A) != (k1_xboole_0)))
% 0.20/0.55         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.20/0.55      inference('split', [status(esa)], ['0'])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      ((((o_0_0_xboole_0) != (k1_xboole_0)))
% 0.20/0.55         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.20/0.55             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.55  thf('21', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      ((((o_0_0_xboole_0) != (o_0_0_xboole_0)))
% 0.20/0.55         <= (~ (((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) & 
% 0.20/0.55             ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.20/0.55      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.55       ~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.55      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.55  thf('24', plain, (~ ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['2', '23'])).
% 0.20/0.55  thf('25', plain, (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['1', '24'])).
% 0.20/0.55  thf(cc1_relat_1, axiom,
% 0.20/0.55    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.20/0.55  thf('26', plain, (![X3 : $i]: ((v1_relat_1 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.55  thf('27', plain, (![X3 : $i]: ((v1_relat_1 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.55      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.55  thf(t146_relat_1, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) =>
% 0.20/0.55       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (![X18 : $i]:
% 0.20/0.55         (((k9_relat_1 @ X18 @ (k1_relat_1 @ X18)) = (k2_relat_1 @ X18))
% 0.20/0.55          | ~ (v1_relat_1 @ X18))),
% 0.20/0.55      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))
% 0.20/0.55         <= ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.20/0.55      inference('split', [status(esa)], ['3'])).
% 0.20/0.55  thf('30', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      ((((k9_relat_1 @ sk_B @ sk_A) = (o_0_0_xboole_0)))
% 0.20/0.55         <= ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))))),
% 0.20/0.55      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))) | 
% 0.20/0.55       ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.55      inference('split', [status(esa)], ['3'])).
% 0.20/0.55  thf('33', plain, ((((k9_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 0.20/0.55      inference('sat_resolution*', [status(thm)], ['2', '23', '32'])).
% 0.20/0.55  thf('34', plain, (((k9_relat_1 @ sk_B @ sk_A) = (o_0_0_xboole_0))),
% 0.20/0.55      inference('simpl_trail', [status(thm)], ['31', '33'])).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (![X19 : $i, X20 : $i]:
% 0.20/0.55         (((k2_relat_1 @ (k7_relat_1 @ X19 @ X20)) = (k9_relat_1 @ X19 @ X20))
% 0.20/0.55          | ~ (v1_relat_1 @ X19))),
% 0.20/0.55      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.55  thf(t144_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      (![X16 : $i, X17 : $i]:
% 0.20/0.55         ((r1_tarski @ (k9_relat_1 @ X16 @ X17) @ (k2_relat_1 @ X16))
% 0.20/0.55          | ~ (v1_relat_1 @ X16))),
% 0.20/0.55      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.20/0.55  thf('37', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.20/0.55           (k9_relat_1 @ X1 @ X0))
% 0.20/0.55          | ~ (v1_relat_1 @ X1)
% 0.20/0.55          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.20/0.55      inference('sup+', [status(thm)], ['35', '36'])).
% 0.20/0.55  thf(dt_k7_relat_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.20/0.55  thf('38', plain,
% 0.20/0.55      (![X5 : $i, X6 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.55         (~ (v1_relat_1 @ X1)
% 0.20/0.55          | (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2) @ 
% 0.20/0.55             (k9_relat_1 @ X1 @ X0)))),
% 0.20/0.55      inference('clc', [status(thm)], ['37', '38'])).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         ((r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ 
% 0.20/0.56           o_0_0_xboole_0)
% 0.20/0.56          | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.56      inference('sup+', [status(thm)], ['34', '39'])).
% 0.20/0.56  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('42', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (r1_tarski @ (k9_relat_1 @ (k7_relat_1 @ sk_B @ sk_A) @ X0) @ 
% 0.20/0.56          o_0_0_xboole_0)),
% 0.20/0.56      inference('demod', [status(thm)], ['40', '41'])).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      (((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ o_0_0_xboole_0)
% 0.20/0.56        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.56      inference('sup+', [status(thm)], ['28', '42'])).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      ((~ (v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.20/0.56        | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ 
% 0.20/0.56           o_0_0_xboole_0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['27', '43'])).
% 0.20/0.56  thf('45', plain, (((k9_relat_1 @ sk_B @ sk_A) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('simpl_trail', [status(thm)], ['31', '33'])).
% 0.20/0.56  thf('46', plain,
% 0.20/0.56      (![X5 : $i, X6 : $i]:
% 0.20/0.56         (~ (v1_relat_1 @ X5) | (v1_relat_1 @ (k7_relat_1 @ X5 @ X6)))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.20/0.56  thf('47', plain,
% 0.20/0.56      (![X19 : $i, X20 : $i]:
% 0.20/0.56         (((k2_relat_1 @ (k7_relat_1 @ X19 @ X20)) = (k9_relat_1 @ X19 @ X20))
% 0.20/0.56          | ~ (v1_relat_1 @ X19))),
% 0.20/0.56      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.56  thf(fc9_relat_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.20/0.56       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.20/0.56  thf('48', plain,
% 0.20/0.56      (![X9 : $i]:
% 0.20/0.56         (~ (v1_xboole_0 @ (k2_relat_1 @ X9))
% 0.20/0.56          | ~ (v1_relat_1 @ X9)
% 0.20/0.56          | (v1_xboole_0 @ X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.20/0.56  thf('49', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.20/0.56          | ~ (v1_relat_1 @ X1)
% 0.20/0.56          | (v1_xboole_0 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.56          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.56  thf('50', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (v1_relat_1 @ X1)
% 0.20/0.56          | (v1_xboole_0 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.56          | ~ (v1_relat_1 @ X1)
% 0.20/0.56          | ~ (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['46', '49'])).
% 0.20/0.56  thf('51', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i]:
% 0.20/0.56         (~ (v1_xboole_0 @ (k9_relat_1 @ X1 @ X0))
% 0.20/0.56          | (v1_xboole_0 @ (k7_relat_1 @ X1 @ X0))
% 0.20/0.56          | ~ (v1_relat_1 @ X1))),
% 0.20/0.56      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.56  thf('52', plain,
% 0.20/0.56      ((~ (v1_xboole_0 @ o_0_0_xboole_0)
% 0.20/0.56        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.56        | (v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['45', '51'])).
% 0.20/0.56  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.56  thf('53', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.56  thf('54', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.56  thf('55', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.56  thf('56', plain, (((k6_relat_1 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.20/0.56  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.56  thf('57', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 0.20/0.56      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.56  thf('58', plain, ((v1_relat_1 @ o_0_0_xboole_0)),
% 0.20/0.56      inference('sup+', [status(thm)], ['56', '57'])).
% 0.20/0.56  thf(t137_relat_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ A ) =>
% 0.20/0.56       ( ( k8_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.56  thf('59', plain,
% 0.20/0.56      (![X15 : $i]:
% 0.20/0.56         (((k8_relat_1 @ k1_xboole_0 @ X15) = (k1_xboole_0))
% 0.20/0.56          | ~ (v1_relat_1 @ X15))),
% 0.20/0.56      inference('cnf', [status(esa)], [t137_relat_1])).
% 0.20/0.56  thf('60', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.56  thf('61', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.56  thf('62', plain,
% 0.20/0.56      (![X15 : $i]:
% 0.20/0.56         (((k8_relat_1 @ o_0_0_xboole_0 @ X15) = (o_0_0_xboole_0))
% 0.20/0.56          | ~ (v1_relat_1 @ X15))),
% 0.20/0.56      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.20/0.56  thf('63', plain,
% 0.20/0.56      (((k8_relat_1 @ o_0_0_xboole_0 @ o_0_0_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['58', '62'])).
% 0.20/0.56  thf(t117_relat_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k8_relat_1 @ A @ B ) @ B ) ))).
% 0.20/0.56  thf('64', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i]:
% 0.20/0.56         ((r1_tarski @ (k8_relat_1 @ X11 @ X12) @ X12) | ~ (v1_relat_1 @ X12))),
% 0.20/0.56      inference('cnf', [status(esa)], [t117_relat_1])).
% 0.20/0.56  thf('65', plain,
% 0.20/0.56      (((r1_tarski @ o_0_0_xboole_0 @ o_0_0_xboole_0)
% 0.20/0.56        | ~ (v1_relat_1 @ o_0_0_xboole_0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['63', '64'])).
% 0.20/0.56  thf('66', plain, ((v1_relat_1 @ o_0_0_xboole_0)),
% 0.20/0.56      inference('sup+', [status(thm)], ['56', '57'])).
% 0.20/0.56  thf('67', plain, ((r1_tarski @ o_0_0_xboole_0 @ o_0_0_xboole_0)),
% 0.20/0.56      inference('demod', [status(thm)], ['65', '66'])).
% 0.20/0.56  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.56  thf('68', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.20/0.56      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.56  thf('69', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.56  thf('70', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ o_0_0_xboole_0)),
% 0.20/0.56      inference('demod', [status(thm)], ['68', '69'])).
% 0.20/0.56  thf(t69_xboole_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.56       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.20/0.56  thf('71', plain,
% 0.20/0.56      (![X1 : $i, X2 : $i]:
% 0.20/0.56         (~ (r1_xboole_0 @ X1 @ X2)
% 0.20/0.56          | ~ (r1_tarski @ X1 @ X2)
% 0.20/0.56          | (v1_xboole_0 @ X1))),
% 0.20/0.56      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.20/0.56  thf('72', plain,
% 0.20/0.56      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ o_0_0_xboole_0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['70', '71'])).
% 0.20/0.56  thf('73', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.20/0.56      inference('sup-', [status(thm)], ['67', '72'])).
% 0.20/0.56  thf('74', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('75', plain, ((v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['52', '73', '74'])).
% 0.20/0.56  thf('76', plain,
% 0.20/0.56      ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_B @ sk_A)) @ o_0_0_xboole_0)),
% 0.20/0.56      inference('demod', [status(thm)], ['44', '75'])).
% 0.20/0.56  thf(t125_relat_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ B ) =>
% 0.20/0.56       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.56         ( ( k8_relat_1 @ A @ B ) = ( B ) ) ) ))).
% 0.20/0.56  thf('77', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i]:
% 0.20/0.56         (~ (r1_tarski @ (k2_relat_1 @ X13) @ X14)
% 0.20/0.56          | ((k8_relat_1 @ X14 @ X13) = (X13))
% 0.20/0.56          | ~ (v1_relat_1 @ X13))),
% 0.20/0.56      inference('cnf', [status(esa)], [t125_relat_1])).
% 0.20/0.56  thf('78', plain,
% 0.20/0.56      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.20/0.56        | ((k8_relat_1 @ o_0_0_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.20/0.56            = (k7_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['76', '77'])).
% 0.20/0.56  thf('79', plain, ((v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['52', '73', '74'])).
% 0.20/0.56  thf('80', plain, (![X3 : $i]: ((v1_relat_1 @ X3) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.56      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.20/0.56  thf('81', plain,
% 0.20/0.56      (![X15 : $i]:
% 0.20/0.56         (((k8_relat_1 @ o_0_0_xboole_0 @ X15) = (o_0_0_xboole_0))
% 0.20/0.56          | ~ (v1_relat_1 @ X15))),
% 0.20/0.56      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.20/0.56  thf('82', plain,
% 0.20/0.56      (![X0 : $i]:
% 0.20/0.56         (~ (v1_xboole_0 @ X0)
% 0.20/0.56          | ((k8_relat_1 @ o_0_0_xboole_0 @ X0) = (o_0_0_xboole_0)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['80', '81'])).
% 0.20/0.56  thf('83', plain,
% 0.20/0.56      (((k8_relat_1 @ o_0_0_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.20/0.56         = (o_0_0_xboole_0))),
% 0.20/0.56      inference('sup-', [status(thm)], ['79', '82'])).
% 0.20/0.56  thf('84', plain,
% 0.20/0.56      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.20/0.56        | ((o_0_0_xboole_0) = (k7_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['78', '83'])).
% 0.20/0.56  thf('85', plain,
% 0.20/0.56      ((~ (v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))
% 0.20/0.56        | ((o_0_0_xboole_0) = (k7_relat_1 @ sk_B @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['26', '84'])).
% 0.20/0.56  thf('86', plain, ((v1_xboole_0 @ (k7_relat_1 @ sk_B @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['52', '73', '74'])).
% 0.20/0.56  thf('87', plain, (((o_0_0_xboole_0) = (k7_relat_1 @ sk_B @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['85', '86'])).
% 0.20/0.56  thf('88', plain,
% 0.20/0.56      (![X21 : $i, X22 : $i]:
% 0.20/0.56         (((k7_relat_1 @ X21 @ X22) != (k1_xboole_0))
% 0.20/0.56          | (r1_xboole_0 @ (k1_relat_1 @ X21) @ X22)
% 0.20/0.56          | ~ (v1_relat_1 @ X21))),
% 0.20/0.56      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.20/0.56  thf('89', plain, (((k1_xboole_0) = (o_0_0_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_xboole_0])).
% 0.20/0.56  thf('90', plain,
% 0.20/0.56      (![X21 : $i, X22 : $i]:
% 0.20/0.56         (((k7_relat_1 @ X21 @ X22) != (o_0_0_xboole_0))
% 0.20/0.56          | (r1_xboole_0 @ (k1_relat_1 @ X21) @ X22)
% 0.20/0.56          | ~ (v1_relat_1 @ X21))),
% 0.20/0.56      inference('demod', [status(thm)], ['88', '89'])).
% 0.20/0.56  thf('91', plain,
% 0.20/0.56      ((((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.20/0.56        | ~ (v1_relat_1 @ sk_B)
% 0.20/0.56        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['87', '90'])).
% 0.20/0.56  thf('92', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('93', plain,
% 0.20/0.56      ((((o_0_0_xboole_0) != (o_0_0_xboole_0))
% 0.20/0.56        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['91', '92'])).
% 0.20/0.56  thf('94', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.20/0.56      inference('simplify', [status(thm)], ['93'])).
% 0.20/0.56  thf('95', plain, ($false), inference('demod', [status(thm)], ['25', '94'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
