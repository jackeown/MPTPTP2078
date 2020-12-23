%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K85GteyPjp

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:26 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 131 expanded)
%              Number of leaves         :   23 (  46 expanded)
%              Depth                    :   18
%              Number of atoms          :  615 ( 846 expanded)
%              Number of equality atoms :   39 (  65 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('2',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('3',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X20 @ X19 ) ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X16: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 )
      | ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ( X10 = X11 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ( X10 = X11 ) ) ),
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

thf('28',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['31','32'])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('38',plain,(
    ! [X12: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('39',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X18 @ X17 ) ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','41'])).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X15: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X15 ) )
      | ~ ( v1_relat_1 @ X15 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','52'])).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ( X10 = X11 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('57',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('61',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('66',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['35','66'])).

thf('68',plain,(
    ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['67'])).

thf('69',plain,(
    ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K85GteyPjp
% 0.16/0.38  % Computer   : n012.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 16:29:22 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.39  % Running in FO mode
% 0.24/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.56  % Solved by: fo/fo7.sh
% 0.24/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.56  % done 112 iterations in 0.064s
% 0.24/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.56  % SZS output start Refutation
% 0.24/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.56  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.24/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.24/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.56  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.24/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.56  thf(cc1_relat_1, axiom,
% 0.24/0.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.24/0.56  thf('0', plain, (![X12 : $i]: ((v1_relat_1 @ X12) | ~ (v1_xboole_0 @ X12))),
% 0.24/0.56      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.24/0.56  thf(dt_k5_relat_1, axiom,
% 0.24/0.56    (![A:$i,B:$i]:
% 0.24/0.56     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.24/0.56       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.24/0.56  thf('1', plain,
% 0.24/0.56      (![X13 : $i, X14 : $i]:
% 0.24/0.56         (~ (v1_relat_1 @ X13)
% 0.24/0.56          | ~ (v1_relat_1 @ X14)
% 0.24/0.56          | (v1_relat_1 @ (k5_relat_1 @ X13 @ X14)))),
% 0.24/0.56      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.24/0.56  thf('2', plain, (![X12 : $i]: ((v1_relat_1 @ X12) | ~ (v1_xboole_0 @ X12))),
% 0.24/0.56      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.24/0.56  thf(t60_relat_1, axiom,
% 0.24/0.56    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.24/0.56     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.24/0.56  thf('3', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.24/0.56  thf(t45_relat_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( v1_relat_1 @ A ) =>
% 0.24/0.56       ( ![B:$i]:
% 0.24/0.56         ( ( v1_relat_1 @ B ) =>
% 0.24/0.56           ( r1_tarski @
% 0.24/0.56             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.24/0.56  thf('4', plain,
% 0.24/0.56      (![X19 : $i, X20 : $i]:
% 0.24/0.56         (~ (v1_relat_1 @ X19)
% 0.24/0.56          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X20 @ X19)) @ 
% 0.24/0.56             (k2_relat_1 @ X19))
% 0.24/0.56          | ~ (v1_relat_1 @ X20))),
% 0.24/0.56      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.24/0.56  thf('5', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.24/0.56           k1_xboole_0)
% 0.24/0.56          | ~ (v1_relat_1 @ X0)
% 0.24/0.56          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.24/0.56      inference('sup+', [status(thm)], ['3', '4'])).
% 0.24/0.56  thf('6', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.24/0.56          | ~ (v1_relat_1 @ X0)
% 0.24/0.56          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.24/0.56             k1_xboole_0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['2', '5'])).
% 0.24/0.56  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.24/0.56  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.56  thf('8', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (~ (v1_relat_1 @ X0)
% 0.24/0.56          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.24/0.56             k1_xboole_0))),
% 0.24/0.56      inference('demod', [status(thm)], ['6', '7'])).
% 0.24/0.56  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.56  thf(d3_tarski, axiom,
% 0.24/0.56    (![A:$i,B:$i]:
% 0.24/0.56     ( ( r1_tarski @ A @ B ) <=>
% 0.24/0.56       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.24/0.56  thf('10', plain,
% 0.24/0.56      (![X4 : $i, X6 : $i]:
% 0.24/0.56         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.24/0.56      inference('cnf', [status(esa)], [d3_tarski])).
% 0.24/0.56  thf(d1_xboole_0, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.24/0.56  thf('11', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.24/0.56      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.24/0.56  thf('12', plain,
% 0.24/0.56      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.24/0.56  thf('13', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.24/0.56      inference('sup-', [status(thm)], ['9', '12'])).
% 0.24/0.56  thf(d10_xboole_0, axiom,
% 0.24/0.56    (![A:$i,B:$i]:
% 0.24/0.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.24/0.56  thf('14', plain,
% 0.24/0.56      (![X7 : $i, X9 : $i]:
% 0.24/0.56         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.24/0.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.24/0.56  thf('15', plain,
% 0.24/0.56      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.24/0.56  thf('16', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (~ (v1_relat_1 @ X0)
% 0.24/0.56          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['8', '15'])).
% 0.24/0.56  thf(fc9_relat_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.24/0.56       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.24/0.56  thf('17', plain,
% 0.24/0.56      (![X16 : $i]:
% 0.24/0.56         (~ (v1_xboole_0 @ (k2_relat_1 @ X16))
% 0.24/0.56          | ~ (v1_relat_1 @ X16)
% 0.24/0.56          | (v1_xboole_0 @ X16))),
% 0.24/0.56      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.24/0.56  thf('18', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.24/0.56          | ~ (v1_relat_1 @ X0)
% 0.24/0.56          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.24/0.56          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['16', '17'])).
% 0.24/0.56  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.56  thf('20', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (~ (v1_relat_1 @ X0)
% 0.24/0.56          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.24/0.56          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.24/0.56      inference('demod', [status(thm)], ['18', '19'])).
% 0.24/0.56  thf('21', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (~ (v1_relat_1 @ k1_xboole_0)
% 0.24/0.56          | ~ (v1_relat_1 @ X0)
% 0.24/0.56          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.24/0.56          | ~ (v1_relat_1 @ X0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['1', '20'])).
% 0.24/0.56  thf('22', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.24/0.56          | ~ (v1_relat_1 @ X0)
% 0.24/0.56          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.24/0.56      inference('simplify', [status(thm)], ['21'])).
% 0.24/0.56  thf('23', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.24/0.56          | ~ (v1_relat_1 @ X0)
% 0.24/0.56          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['0', '22'])).
% 0.24/0.56  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.56  thf('25', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.24/0.56      inference('demod', [status(thm)], ['23', '24'])).
% 0.24/0.56  thf(t8_boole, axiom,
% 0.24/0.56    (![A:$i,B:$i]:
% 0.24/0.56     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.24/0.56  thf('26', plain,
% 0.24/0.56      (![X10 : $i, X11 : $i]:
% 0.24/0.56         (~ (v1_xboole_0 @ X10) | ~ (v1_xboole_0 @ X11) | ((X10) = (X11)))),
% 0.24/0.56      inference('cnf', [status(esa)], [t8_boole])).
% 0.24/0.56  thf('27', plain,
% 0.24/0.56      (![X10 : $i, X11 : $i]:
% 0.24/0.56         (~ (v1_xboole_0 @ X10) | ~ (v1_xboole_0 @ X11) | ((X10) = (X11)))),
% 0.24/0.56      inference('cnf', [status(esa)], [t8_boole])).
% 0.24/0.56  thf(t62_relat_1, conjecture,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( v1_relat_1 @ A ) =>
% 0.24/0.56       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.24/0.56         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.24/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.56    (~( ![A:$i]:
% 0.24/0.56        ( ( v1_relat_1 @ A ) =>
% 0.24/0.56          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.24/0.56            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.24/0.56    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.24/0.56  thf('28', plain,
% 0.24/0.56      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.24/0.56        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('29', plain,
% 0.24/0.56      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.24/0.56         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.24/0.56      inference('split', [status(esa)], ['28'])).
% 0.24/0.56  thf('30', plain,
% 0.24/0.56      ((![X0 : $i]:
% 0.24/0.56          (((X0) != (k1_xboole_0))
% 0.24/0.56           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 0.24/0.56           | ~ (v1_xboole_0 @ X0)))
% 0.24/0.56         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['27', '29'])).
% 0.24/0.56  thf('31', plain,
% 0.24/0.56      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.24/0.56         | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))))
% 0.24/0.56         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.24/0.56      inference('simplify', [status(thm)], ['30'])).
% 0.24/0.56  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.56  thf('33', plain,
% 0.24/0.56      ((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0)))
% 0.24/0.56         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.24/0.56      inference('simplify_reflect+', [status(thm)], ['31', '32'])).
% 0.24/0.56  thf('34', plain,
% 0.24/0.56      ((![X0 : $i]:
% 0.24/0.56          (~ (v1_xboole_0 @ X0)
% 0.24/0.56           | ~ (v1_xboole_0 @ X0)
% 0.24/0.56           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))))
% 0.24/0.56         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['26', '33'])).
% 0.24/0.56  thf('35', plain,
% 0.24/0.56      ((![X0 : $i]:
% 0.24/0.56          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 0.24/0.56           | ~ (v1_xboole_0 @ X0)))
% 0.24/0.56         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.24/0.56      inference('simplify', [status(thm)], ['34'])).
% 0.24/0.56  thf('36', plain, (![X12 : $i]: ((v1_relat_1 @ X12) | ~ (v1_xboole_0 @ X12))),
% 0.24/0.56      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.24/0.56  thf('37', plain,
% 0.24/0.56      (![X13 : $i, X14 : $i]:
% 0.24/0.56         (~ (v1_relat_1 @ X13)
% 0.24/0.56          | ~ (v1_relat_1 @ X14)
% 0.24/0.56          | (v1_relat_1 @ (k5_relat_1 @ X13 @ X14)))),
% 0.24/0.56      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.24/0.56  thf('38', plain, (![X12 : $i]: ((v1_relat_1 @ X12) | ~ (v1_xboole_0 @ X12))),
% 0.24/0.56      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.24/0.56  thf('39', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.24/0.56  thf(t44_relat_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( v1_relat_1 @ A ) =>
% 0.24/0.56       ( ![B:$i]:
% 0.24/0.56         ( ( v1_relat_1 @ B ) =>
% 0.24/0.56           ( r1_tarski @
% 0.24/0.56             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.24/0.56  thf('40', plain,
% 0.24/0.56      (![X17 : $i, X18 : $i]:
% 0.24/0.56         (~ (v1_relat_1 @ X17)
% 0.24/0.56          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X18 @ X17)) @ 
% 0.24/0.56             (k1_relat_1 @ X18))
% 0.24/0.56          | ~ (v1_relat_1 @ X18))),
% 0.24/0.56      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.24/0.56  thf('41', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.24/0.56           k1_xboole_0)
% 0.24/0.56          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.24/0.56          | ~ (v1_relat_1 @ X0))),
% 0.24/0.56      inference('sup+', [status(thm)], ['39', '40'])).
% 0.24/0.56  thf('42', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.24/0.56          | ~ (v1_relat_1 @ X0)
% 0.24/0.56          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.24/0.56             k1_xboole_0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['38', '41'])).
% 0.24/0.56  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.56  thf('44', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (~ (v1_relat_1 @ X0)
% 0.24/0.56          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.24/0.56             k1_xboole_0))),
% 0.24/0.56      inference('demod', [status(thm)], ['42', '43'])).
% 0.24/0.56  thf('45', plain,
% 0.24/0.56      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['13', '14'])).
% 0.24/0.56  thf('46', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (~ (v1_relat_1 @ X0)
% 0.24/0.56          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['44', '45'])).
% 0.24/0.56  thf(fc8_relat_1, axiom,
% 0.24/0.56    (![A:$i]:
% 0.24/0.56     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.24/0.56       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.24/0.56  thf('47', plain,
% 0.24/0.56      (![X15 : $i]:
% 0.24/0.56         (~ (v1_xboole_0 @ (k1_relat_1 @ X15))
% 0.24/0.56          | ~ (v1_relat_1 @ X15)
% 0.24/0.56          | (v1_xboole_0 @ X15))),
% 0.24/0.56      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.24/0.56  thf('48', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.24/0.56          | ~ (v1_relat_1 @ X0)
% 0.24/0.56          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.24/0.56          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['46', '47'])).
% 0.24/0.56  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.56  thf('50', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (~ (v1_relat_1 @ X0)
% 0.24/0.56          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.24/0.56          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.24/0.56      inference('demod', [status(thm)], ['48', '49'])).
% 0.24/0.56  thf('51', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (~ (v1_relat_1 @ X0)
% 0.24/0.56          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.24/0.56          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.24/0.56          | ~ (v1_relat_1 @ X0))),
% 0.24/0.56      inference('sup-', [status(thm)], ['37', '50'])).
% 0.24/0.56  thf('52', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.24/0.56          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.24/0.56          | ~ (v1_relat_1 @ X0))),
% 0.24/0.56      inference('simplify', [status(thm)], ['51'])).
% 0.24/0.56  thf('53', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.24/0.56          | ~ (v1_relat_1 @ X0)
% 0.24/0.56          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.24/0.56      inference('sup-', [status(thm)], ['36', '52'])).
% 0.24/0.56  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.56  thf('55', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.24/0.56      inference('demod', [status(thm)], ['53', '54'])).
% 0.24/0.56  thf('56', plain,
% 0.24/0.56      (![X10 : $i, X11 : $i]:
% 0.24/0.56         (~ (v1_xboole_0 @ X10) | ~ (v1_xboole_0 @ X11) | ((X10) = (X11)))),
% 0.24/0.56      inference('cnf', [status(esa)], [t8_boole])).
% 0.24/0.56  thf('57', plain,
% 0.24/0.56      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.24/0.56         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.24/0.56      inference('split', [status(esa)], ['28'])).
% 0.24/0.56  thf('58', plain,
% 0.24/0.56      ((![X0 : $i]:
% 0.24/0.56          (((X0) != (k1_xboole_0))
% 0.24/0.56           | ~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A))
% 0.24/0.56           | ~ (v1_xboole_0 @ X0)))
% 0.24/0.56         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['56', '57'])).
% 0.24/0.56  thf('59', plain,
% 0.24/0.56      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.24/0.56         | ~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A))))
% 0.24/0.56         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.24/0.56      inference('simplify', [status(thm)], ['58'])).
% 0.24/0.56  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.24/0.56      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.24/0.56  thf('61', plain,
% 0.24/0.56      ((~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A)))
% 0.24/0.56         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.24/0.56      inference('simplify_reflect+', [status(thm)], ['59', '60'])).
% 0.24/0.56  thf('62', plain,
% 0.24/0.56      ((~ (v1_relat_1 @ sk_A))
% 0.24/0.56         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.24/0.56      inference('sup-', [status(thm)], ['55', '61'])).
% 0.24/0.56  thf('63', plain, ((v1_relat_1 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('64', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.24/0.56      inference('demod', [status(thm)], ['62', '63'])).
% 0.24/0.56  thf('65', plain,
% 0.24/0.56      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.24/0.56       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.24/0.56      inference('split', [status(esa)], ['28'])).
% 0.24/0.56  thf('66', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.24/0.56      inference('sat_resolution*', [status(thm)], ['64', '65'])).
% 0.24/0.56  thf('67', plain,
% 0.24/0.56      (![X0 : $i]:
% 0.24/0.56         (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 0.24/0.56          | ~ (v1_xboole_0 @ X0))),
% 0.24/0.56      inference('simpl_trail', [status(thm)], ['35', '66'])).
% 0.24/0.56  thf('68', plain, (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))),
% 0.24/0.56      inference('condensation', [status(thm)], ['67'])).
% 0.24/0.56  thf('69', plain, (~ (v1_relat_1 @ sk_A)),
% 0.24/0.56      inference('sup-', [status(thm)], ['25', '68'])).
% 0.24/0.56  thf('70', plain, ((v1_relat_1 @ sk_A)),
% 0.24/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.56  thf('71', plain, ($false), inference('demod', [status(thm)], ['69', '70'])).
% 0.24/0.56  
% 0.24/0.56  % SZS output end Refutation
% 0.24/0.56  
% 0.40/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
