%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m2oXsajpJ3

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:44 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 179 expanded)
%              Number of leaves         :   30 (  68 expanded)
%              Depth                    :   17
%              Number of atoms          :  648 (1187 expanded)
%              Number of equality atoms :   53 ( 108 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X44 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t47_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) )
           => ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) )
              = ( k2_relat_1 @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X49: $i,X50: $i] :
      ( ~ ( v1_relat_1 @ X49 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X49 @ X50 ) )
        = ( k2_relat_1 @ X50 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X50 ) @ ( k2_relat_1 @ X49 ) )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
    <=> ! [B: $i] :
          ~ ( ( r2_hidden @ B @ A )
            & ! [C: $i,D: $i] :
                ( B
               != ( k4_tarski @ C @ D ) ) ) ) )).

thf('5',plain,(
    ! [X40: $i] :
      ( ( v1_relat_1 @ X40 )
      | ( r2_hidden @ ( sk_B @ X40 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[d1_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('8',plain,(
    ! [X4: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X4 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('9',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('10',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X36 @ X37 ) )
      = ( k3_xboole_0 @ X36 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_setfam_1 @ ( k2_tarski @ X0 @ X3 ) ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('13',plain,(
    ! [X6: $i] :
      ( r1_xboole_0 @ X6 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('14',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4','15','16'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X46: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X46 ) )
      | ~ ( v1_relat_1 @ X46 )
      | ( v1_xboole_0 @ X46 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','21'])).

thf('23',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','14'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('27',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('30',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['33','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_relat_1 @ X44 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X43 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('38',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('39',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v1_relat_1 @ X47 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X48 @ X47 ) )
        = ( k1_relat_1 @ X48 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X48 ) @ ( k1_relat_1 @ X47 ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','14'])).

thf('43',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41','42','43'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X45: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X45 ) )
      | ~ ( v1_relat_1 @ X45 )
      | ( v1_xboole_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','48'])).

thf('50',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['5','14'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_xboole_0 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ( X7 = X8 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('55',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('60',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('64',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['30'])).

thf('66',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['36','66'])).

thf('68',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['68','69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.m2oXsajpJ3
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:51:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 187 iterations in 0.128s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.39/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i > $i).
% 0.39/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.39/0.58  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.39/0.58  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.58  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.58  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.39/0.58  thf(dt_k5_relat_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.39/0.58       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      (![X43 : $i, X44 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X43)
% 0.39/0.58          | ~ (v1_relat_1 @ X44)
% 0.39/0.58          | (v1_relat_1 @ (k5_relat_1 @ X43 @ X44)))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.39/0.58  thf(t60_relat_1, axiom,
% 0.39/0.58    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.39/0.58     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.39/0.58  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.39/0.58  thf(t47_relat_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( v1_relat_1 @ B ) =>
% 0.39/0.58           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.39/0.58             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (![X49 : $i, X50 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X49)
% 0.39/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X49 @ X50)) = (k2_relat_1 @ X50))
% 0.39/0.58          | ~ (r1_tarski @ (k1_relat_1 @ X50) @ (k2_relat_1 @ X49))
% 0.39/0.58          | ~ (v1_relat_1 @ X50))),
% 0.39/0.58      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.39/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.39/0.58          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.39/0.58              = (k2_relat_1 @ k1_xboole_0))
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.39/0.58  thf('4', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.39/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.58  thf(d1_relat_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ A ) <=>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ~( ( r2_hidden @ B @ A ) & 
% 0.39/0.58              ( ![C:$i,D:$i]: ( ( B ) != ( k4_tarski @ C @ D ) ) ) ) ) ) ))).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (![X40 : $i]: ((v1_relat_1 @ X40) | (r2_hidden @ (sk_B @ X40) @ X40))),
% 0.39/0.58      inference('cnf', [status(esa)], [d1_relat_1])).
% 0.39/0.58  thf(t2_boole, axiom,
% 0.39/0.58    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.39/0.58  thf('6', plain,
% 0.39/0.58      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.58      inference('cnf', [status(esa)], [t2_boole])).
% 0.39/0.58  thf(t12_setfam_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      (![X36 : $i, X37 : $i]:
% 0.39/0.58         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.39/0.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      (![X4 : $i]:
% 0.39/0.58         ((k1_setfam_1 @ (k2_tarski @ X4 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.39/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.39/0.58  thf(t4_xboole_0, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.58            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.58       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.39/0.58            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.39/0.58          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.39/0.58      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (![X36 : $i, X37 : $i]:
% 0.39/0.58         ((k1_setfam_1 @ (k2_tarski @ X36 @ X37)) = (k3_xboole_0 @ X36 @ X37))),
% 0.39/0.58      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X2 @ (k1_setfam_1 @ (k2_tarski @ X0 @ X3)))
% 0.39/0.58          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.39/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['8', '11'])).
% 0.39/0.58  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.39/0.58  thf('13', plain, (![X6 : $i]: (r1_xboole_0 @ X6 @ k1_xboole_0)),
% 0.39/0.58      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.39/0.58  thf('14', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.39/0.58      inference('demod', [status(thm)], ['12', '13'])).
% 0.39/0.58  thf('15', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.39/0.58      inference('sup-', [status(thm)], ['5', '14'])).
% 0.39/0.58  thf('16', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.39/0.58  thf('17', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('demod', [status(thm)], ['3', '4', '15', '16'])).
% 0.39/0.58  thf(fc9_relat_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.39/0.58       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      (![X46 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ (k2_relat_1 @ X46))
% 0.39/0.58          | ~ (v1_relat_1 @ X46)
% 0.39/0.58          | (v1_xboole_0 @ X46))),
% 0.39/0.58      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.39/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.39/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.39/0.58  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.58  thf('21', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.39/0.58          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.39/0.58      inference('demod', [status(thm)], ['19', '20'])).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ k1_xboole_0)
% 0.39/0.58          | ~ (v1_relat_1 @ X0)
% 0.39/0.58          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['0', '21'])).
% 0.39/0.58  thf('23', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.39/0.58      inference('sup-', [status(thm)], ['5', '14'])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X0)
% 0.39/0.58          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('demod', [status(thm)], ['22', '23'])).
% 0.39/0.58  thf('25', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('simplify', [status(thm)], ['24'])).
% 0.39/0.58  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.58  thf(t8_boole, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.39/0.58  thf('27', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X8) | ((X7) = (X8)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t8_boole])).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i]:
% 0.39/0.58         (~ (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X8) | ((X7) = (X8)))),
% 0.39/0.58      inference('cnf', [status(esa)], [t8_boole])).
% 0.39/0.58  thf(t62_relat_1, conjecture,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ A ) =>
% 0.39/0.58       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.39/0.58         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i]:
% 0.39/0.58        ( ( v1_relat_1 @ A ) =>
% 0.39/0.58          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.39/0.58            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.39/0.58  thf('30', plain,
% 0.39/0.58      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.39/0.58        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.39/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.39/0.58      inference('split', [status(esa)], ['30'])).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      ((![X0 : $i]:
% 0.39/0.58          (((X0) != (k1_xboole_0))
% 0.39/0.58           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 0.39/0.58           | ~ (v1_xboole_0 @ X0)))
% 0.39/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['29', '31'])).
% 0.39/0.58  thf('33', plain,
% 0.39/0.58      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.58         | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))))
% 0.39/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.39/0.58      inference('simplify', [status(thm)], ['32'])).
% 0.39/0.58  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      ((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0)))
% 0.39/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.39/0.58      inference('simplify_reflect+', [status(thm)], ['33', '34'])).
% 0.39/0.58  thf('36', plain,
% 0.39/0.58      ((![X0 : $i]:
% 0.39/0.58          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0)))
% 0.39/0.58         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['28', '35'])).
% 0.39/0.58  thf('37', plain,
% 0.39/0.58      (![X43 : $i, X44 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X43)
% 0.39/0.58          | ~ (v1_relat_1 @ X44)
% 0.39/0.58          | (v1_relat_1 @ (k5_relat_1 @ X43 @ X44)))),
% 0.39/0.58      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.39/0.58  thf('38', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.39/0.58  thf(t46_relat_1, axiom,
% 0.39/0.58    (![A:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ A ) =>
% 0.39/0.58       ( ![B:$i]:
% 0.39/0.58         ( ( v1_relat_1 @ B ) =>
% 0.39/0.58           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.39/0.58             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.39/0.58  thf('39', plain,
% 0.39/0.58      (![X47 : $i, X48 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X47)
% 0.39/0.58          | ((k1_relat_1 @ (k5_relat_1 @ X48 @ X47)) = (k1_relat_1 @ X48))
% 0.39/0.58          | ~ (r1_tarski @ (k2_relat_1 @ X48) @ (k1_relat_1 @ X47))
% 0.39/0.58          | ~ (v1_relat_1 @ X48))),
% 0.39/0.58      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.39/0.58  thf('40', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.39/0.58          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.39/0.58          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.39/0.58              = (k1_relat_1 @ k1_xboole_0))
% 0.39/0.58          | ~ (v1_relat_1 @ X0))),
% 0.39/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.39/0.58  thf('41', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 0.39/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.39/0.58  thf('42', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.39/0.58      inference('sup-', [status(thm)], ['5', '14'])).
% 0.39/0.59  thf('43', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.39/0.59      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.39/0.59  thf('44', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.39/0.59          | ~ (v1_relat_1 @ X0))),
% 0.39/0.59      inference('demod', [status(thm)], ['40', '41', '42', '43'])).
% 0.39/0.59  thf(fc8_relat_1, axiom,
% 0.39/0.59    (![A:$i]:
% 0.39/0.59     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.39/0.59       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.39/0.59  thf('45', plain,
% 0.39/0.59      (![X45 : $i]:
% 0.39/0.59         (~ (v1_xboole_0 @ (k1_relat_1 @ X45))
% 0.39/0.59          | ~ (v1_relat_1 @ X45)
% 0.39/0.59          | (v1_xboole_0 @ X45))),
% 0.39/0.59      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.39/0.59  thf('46', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.39/0.59          | ~ (v1_relat_1 @ X0)
% 0.39/0.59          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.39/0.59          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.39/0.59      inference('sup-', [status(thm)], ['44', '45'])).
% 0.39/0.59  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.59  thf('48', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X0)
% 0.39/0.59          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.39/0.59          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.39/0.59      inference('demod', [status(thm)], ['46', '47'])).
% 0.39/0.59  thf('49', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X0)
% 0.39/0.59          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.39/0.59          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.39/0.59          | ~ (v1_relat_1 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['37', '48'])).
% 0.39/0.59  thf('50', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.39/0.59      inference('sup-', [status(thm)], ['5', '14'])).
% 0.39/0.59  thf('51', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v1_relat_1 @ X0)
% 0.39/0.59          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.39/0.59          | ~ (v1_relat_1 @ X0))),
% 0.39/0.59      inference('demod', [status(thm)], ['49', '50'])).
% 0.39/0.59  thf('52', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.39/0.59      inference('simplify', [status(thm)], ['51'])).
% 0.39/0.59  thf('53', plain,
% 0.39/0.59      (![X7 : $i, X8 : $i]:
% 0.39/0.59         (~ (v1_xboole_0 @ X7) | ~ (v1_xboole_0 @ X8) | ((X7) = (X8)))),
% 0.39/0.59      inference('cnf', [status(esa)], [t8_boole])).
% 0.39/0.59  thf('54', plain,
% 0.39/0.59      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['26', '27'])).
% 0.39/0.59  thf('55', plain,
% 0.39/0.59      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.39/0.59         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('split', [status(esa)], ['30'])).
% 0.39/0.59  thf('56', plain,
% 0.39/0.59      ((![X0 : $i]:
% 0.39/0.59          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.39/0.59         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['54', '55'])).
% 0.39/0.59  thf('57', plain,
% 0.39/0.59      ((![X0 : $i, X1 : $i]:
% 0.39/0.59          (((X0) != (k1_xboole_0))
% 0.39/0.59           | ~ (v1_xboole_0 @ X0)
% 0.39/0.59           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.39/0.59           | ~ (v1_xboole_0 @ X1)))
% 0.39/0.59         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['53', '56'])).
% 0.39/0.59  thf('58', plain,
% 0.39/0.59      ((![X1 : $i]:
% 0.39/0.59          (~ (v1_xboole_0 @ X1)
% 0.39/0.59           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.39/0.59           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.39/0.59         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('simplify', [status(thm)], ['57'])).
% 0.39/0.59  thf('59', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.59  thf('60', plain,
% 0.39/0.59      ((![X1 : $i]:
% 0.39/0.59          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.39/0.59         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('simplify_reflect+', [status(thm)], ['58', '59'])).
% 0.39/0.59  thf('61', plain,
% 0.39/0.59      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.39/0.59         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.39/0.59      inference('sup-', [status(thm)], ['52', '60'])).
% 0.39/0.59  thf('62', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('63', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.59  thf('64', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.39/0.59      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.39/0.59  thf('65', plain,
% 0.39/0.59      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.39/0.59       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.39/0.59      inference('split', [status(esa)], ['30'])).
% 0.39/0.59  thf('66', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.39/0.59      inference('sat_resolution*', [status(thm)], ['64', '65'])).
% 0.39/0.59  thf('67', plain,
% 0.39/0.59      (![X0 : $i]:
% 0.39/0.59         (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.39/0.59      inference('simpl_trail', [status(thm)], ['36', '66'])).
% 0.39/0.59  thf('68', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.39/0.59      inference('sup-', [status(thm)], ['25', '67'])).
% 0.39/0.59  thf('69', plain, ((v1_relat_1 @ sk_A)),
% 0.39/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.59  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.59      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.59  thf('71', plain, ($false),
% 0.39/0.59      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.39/0.59  
% 0.39/0.59  % SZS output end Refutation
% 0.39/0.59  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
