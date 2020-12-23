%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3H8xrApN89

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:31 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 134 expanded)
%              Number of leaves         :   20 (  47 expanded)
%              Depth                    :   17
%              Number of atoms          :  663 ( 887 expanded)
%              Number of equality atoms :   54 (  89 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('2',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
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

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X13 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('7',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('12',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','17'])).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('26',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

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
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('30',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ ( k2_relat_1 @ X0 ) @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ ( k2_relat_1 @ X1 ) @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ ( k2_relat_1 @ X1 ) @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('34',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ ( k2_relat_1 @ X1 ) @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','34'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('37',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('40',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('41',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('42',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) ) @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X1: $i,X3: $i] :
      ( ( X1 = X3 )
      | ~ ( r1_tarski @ X3 @ X1 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('51',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['38','56'])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('62',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('67',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('71',plain,
    ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['28'])).

thf('73',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['71','72'])).

thf('74',plain,(
    ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['37','73'])).

thf('75',plain,(
    ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['75','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3H8xrApN89
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:48:18 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.37/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.54  % Solved by: fo/fo7.sh
% 0.37/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.54  % done 170 iterations in 0.121s
% 0.37/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.54  % SZS output start Refutation
% 0.37/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.37/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.54  thf(cc1_relat_1, axiom,
% 0.37/0.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.37/0.54  thf('0', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.37/0.54      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.37/0.54  thf(dt_k5_relat_1, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.37/0.54       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.37/0.54  thf('1', plain,
% 0.37/0.54      (![X6 : $i, X7 : $i]:
% 0.37/0.54         (~ (v1_relat_1 @ X6)
% 0.37/0.54          | ~ (v1_relat_1 @ X7)
% 0.37/0.54          | (v1_relat_1 @ (k5_relat_1 @ X6 @ X7)))),
% 0.37/0.54      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.37/0.54  thf('2', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.37/0.54      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.37/0.54  thf(t60_relat_1, axiom,
% 0.37/0.54    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.37/0.54     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.37/0.54  thf('3', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.37/0.54  thf(t46_relat_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( v1_relat_1 @ A ) =>
% 0.37/0.54       ( ![B:$i]:
% 0.37/0.54         ( ( v1_relat_1 @ B ) =>
% 0.37/0.54           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.37/0.54             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.37/0.54  thf('4', plain,
% 0.37/0.54      (![X12 : $i, X13 : $i]:
% 0.37/0.54         (~ (v1_relat_1 @ X12)
% 0.37/0.54          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12)) = (k1_relat_1 @ X13))
% 0.37/0.54          | ~ (r1_tarski @ (k2_relat_1 @ X13) @ (k1_relat_1 @ X12))
% 0.37/0.54          | ~ (v1_relat_1 @ X13))),
% 0.37/0.54      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.37/0.54  thf('5', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.37/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.54          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.37/0.54              = (k1_relat_1 @ k1_xboole_0))
% 0.37/0.54          | ~ (v1_relat_1 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.37/0.54  thf('6', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.37/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.54  thf('7', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.37/0.54  thf('8', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.54          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.37/0.54          | ~ (v1_relat_1 @ X0))),
% 0.37/0.54      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.37/0.54  thf('9', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.54          | ~ (v1_relat_1 @ X0)
% 0.37/0.54          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['2', '8'])).
% 0.37/0.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.37/0.54  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.54  thf('11', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_relat_1 @ X0)
% 0.37/0.54          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.37/0.54      inference('demod', [status(thm)], ['9', '10'])).
% 0.37/0.54  thf(fc8_relat_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.37/0.54       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.37/0.54  thf('12', plain,
% 0.37/0.54      (![X8 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ (k1_relat_1 @ X8))
% 0.37/0.54          | ~ (v1_relat_1 @ X8)
% 0.37/0.54          | (v1_xboole_0 @ X8))),
% 0.37/0.54      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.37/0.54  thf('13', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.54          | ~ (v1_relat_1 @ X0)
% 0.37/0.54          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.37/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.54  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.54  thf('15', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_relat_1 @ X0)
% 0.37/0.54          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.37/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.37/0.54      inference('demod', [status(thm)], ['13', '14'])).
% 0.37/0.54  thf('16', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_relat_1 @ X0)
% 0.37/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.54          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.37/0.54          | ~ (v1_relat_1 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['1', '15'])).
% 0.37/0.54  thf('17', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.37/0.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.54          | ~ (v1_relat_1 @ X0))),
% 0.37/0.54      inference('simplify', [status(thm)], ['16'])).
% 0.37/0.54  thf('18', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.54          | ~ (v1_relat_1 @ X0)
% 0.37/0.54          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['0', '17'])).
% 0.37/0.54  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.54  thf('20', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.37/0.54      inference('demod', [status(thm)], ['18', '19'])).
% 0.37/0.54  thf('21', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.37/0.54  thf(l13_xboole_0, axiom,
% 0.37/0.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.37/0.54  thf('22', plain,
% 0.37/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.54  thf('23', plain,
% 0.37/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.54  thf('24', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.54      inference('sup+', [status(thm)], ['22', '23'])).
% 0.37/0.54  thf('25', plain,
% 0.37/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.54  thf('26', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.37/0.54  thf('27', plain,
% 0.37/0.54      (![X0 : $i]: (((k2_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('sup+', [status(thm)], ['25', '26'])).
% 0.37/0.54  thf(t62_relat_1, conjecture,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( v1_relat_1 @ A ) =>
% 0.37/0.54       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.37/0.54         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.37/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.54    (~( ![A:$i]:
% 0.37/0.54        ( ( v1_relat_1 @ A ) =>
% 0.37/0.54          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.37/0.54            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.37/0.54    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.37/0.54  thf('28', plain,
% 0.37/0.54      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.37/0.54        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('29', plain,
% 0.37/0.54      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.37/0.54         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.54      inference('split', [status(esa)], ['28'])).
% 0.37/0.54  thf('30', plain,
% 0.37/0.54      ((![X0 : $i]:
% 0.37/0.54          (((k5_relat_1 @ (k2_relat_1 @ X0) @ sk_A) != (k1_xboole_0))
% 0.37/0.54           | ~ (v1_xboole_0 @ X0)))
% 0.37/0.54         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['27', '29'])).
% 0.37/0.54  thf('31', plain,
% 0.37/0.54      ((![X0 : $i, X1 : $i]:
% 0.37/0.54          (((X0) != (k1_xboole_0))
% 0.37/0.54           | ~ (v1_xboole_0 @ X0)
% 0.37/0.54           | ~ (v1_xboole_0 @ (k5_relat_1 @ (k2_relat_1 @ X1) @ sk_A))
% 0.37/0.54           | ~ (v1_xboole_0 @ X1)))
% 0.37/0.54         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['24', '30'])).
% 0.37/0.54  thf('32', plain,
% 0.37/0.54      ((![X1 : $i]:
% 0.37/0.54          (~ (v1_xboole_0 @ X1)
% 0.37/0.54           | ~ (v1_xboole_0 @ (k5_relat_1 @ (k2_relat_1 @ X1) @ sk_A))
% 0.37/0.54           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.37/0.54         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.54      inference('simplify', [status(thm)], ['31'])).
% 0.37/0.54  thf('33', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.54  thf('34', plain,
% 0.37/0.54      ((![X1 : $i]:
% 0.37/0.54          (~ (v1_xboole_0 @ X1)
% 0.37/0.54           | ~ (v1_xboole_0 @ (k5_relat_1 @ (k2_relat_1 @ X1) @ sk_A))))
% 0.37/0.54         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.54      inference('simplify_reflect+', [status(thm)], ['32', '33'])).
% 0.37/0.54  thf('35', plain,
% 0.37/0.54      (((~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A))
% 0.37/0.54         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.37/0.54         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['21', '34'])).
% 0.37/0.54  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.54  thf('37', plain,
% 0.37/0.54      ((~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A)))
% 0.37/0.54         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.37/0.54      inference('demod', [status(thm)], ['35', '36'])).
% 0.37/0.54  thf('38', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.37/0.54      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.37/0.54  thf('39', plain,
% 0.37/0.54      (![X6 : $i, X7 : $i]:
% 0.37/0.54         (~ (v1_relat_1 @ X6)
% 0.37/0.54          | ~ (v1_relat_1 @ X7)
% 0.37/0.54          | (v1_relat_1 @ (k5_relat_1 @ X6 @ X7)))),
% 0.37/0.54      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.37/0.54  thf('40', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.37/0.54      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.37/0.54  thf('41', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.37/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.37/0.54  thf(t45_relat_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( v1_relat_1 @ A ) =>
% 0.37/0.54       ( ![B:$i]:
% 0.37/0.54         ( ( v1_relat_1 @ B ) =>
% 0.37/0.54           ( r1_tarski @
% 0.37/0.54             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.37/0.54  thf('42', plain,
% 0.37/0.54      (![X10 : $i, X11 : $i]:
% 0.37/0.54         (~ (v1_relat_1 @ X10)
% 0.37/0.54          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X11 @ X10)) @ 
% 0.37/0.54             (k2_relat_1 @ X10))
% 0.37/0.54          | ~ (v1_relat_1 @ X11))),
% 0.37/0.54      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.37/0.54  thf('43', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.37/0.54           k1_xboole_0)
% 0.37/0.54          | ~ (v1_relat_1 @ X0)
% 0.37/0.54          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.54      inference('sup+', [status(thm)], ['41', '42'])).
% 0.37/0.54  thf('44', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.54          | ~ (v1_relat_1 @ X0)
% 0.37/0.54          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.37/0.54             k1_xboole_0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['40', '43'])).
% 0.37/0.54  thf('45', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.54  thf('46', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_relat_1 @ X0)
% 0.37/0.54          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.37/0.54             k1_xboole_0))),
% 0.37/0.54      inference('demod', [status(thm)], ['44', '45'])).
% 0.37/0.54  thf('47', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.37/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.37/0.54  thf(d10_xboole_0, axiom,
% 0.37/0.54    (![A:$i,B:$i]:
% 0.37/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.54  thf('48', plain,
% 0.37/0.54      (![X1 : $i, X3 : $i]:
% 0.37/0.54         (((X1) = (X3)) | ~ (r1_tarski @ X3 @ X1) | ~ (r1_tarski @ X1 @ X3))),
% 0.37/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.54  thf('49', plain,
% 0.37/0.54      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['47', '48'])).
% 0.37/0.54  thf('50', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_relat_1 @ X0)
% 0.37/0.54          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['46', '49'])).
% 0.37/0.54  thf(fc9_relat_1, axiom,
% 0.37/0.54    (![A:$i]:
% 0.37/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.37/0.54       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.37/0.54  thf('51', plain,
% 0.37/0.54      (![X9 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ (k2_relat_1 @ X9))
% 0.37/0.54          | ~ (v1_relat_1 @ X9)
% 0.37/0.54          | (v1_xboole_0 @ X9))),
% 0.37/0.54      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.37/0.54  thf('52', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.54          | ~ (v1_relat_1 @ X0)
% 0.37/0.54          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.37/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.37/0.54  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.54  thf('54', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_relat_1 @ X0)
% 0.37/0.54          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.37/0.54          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.37/0.54      inference('demod', [status(thm)], ['52', '53'])).
% 0.37/0.54  thf('55', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_relat_1 @ k1_xboole_0)
% 0.37/0.54          | ~ (v1_relat_1 @ X0)
% 0.37/0.54          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.37/0.54          | ~ (v1_relat_1 @ X0))),
% 0.37/0.54      inference('sup-', [status(thm)], ['39', '54'])).
% 0.37/0.54  thf('56', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.37/0.54          | ~ (v1_relat_1 @ X0)
% 0.37/0.54          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.37/0.54      inference('simplify', [status(thm)], ['55'])).
% 0.37/0.54  thf('57', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.37/0.54          | ~ (v1_relat_1 @ X0)
% 0.37/0.54          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.37/0.54      inference('sup-', [status(thm)], ['38', '56'])).
% 0.37/0.54  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.54  thf('59', plain,
% 0.37/0.54      (![X0 : $i]:
% 0.37/0.54         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.37/0.54      inference('demod', [status(thm)], ['57', '58'])).
% 0.37/0.54  thf('60', plain,
% 0.37/0.54      (![X0 : $i, X1 : $i]:
% 0.37/0.54         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.54      inference('sup+', [status(thm)], ['22', '23'])).
% 0.37/0.54  thf('61', plain,
% 0.37/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.37/0.54  thf('62', plain,
% 0.37/0.54      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.37/0.54         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.54      inference('split', [status(esa)], ['28'])).
% 0.37/0.54  thf('63', plain,
% 0.37/0.54      ((![X0 : $i]:
% 0.37/0.54          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.37/0.54         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['61', '62'])).
% 0.37/0.54  thf('64', plain,
% 0.37/0.54      ((![X0 : $i, X1 : $i]:
% 0.37/0.54          (((X0) != (k1_xboole_0))
% 0.37/0.54           | ~ (v1_xboole_0 @ X0)
% 0.37/0.54           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.37/0.54           | ~ (v1_xboole_0 @ X1)))
% 0.37/0.54         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['60', '63'])).
% 0.37/0.54  thf('65', plain,
% 0.37/0.54      ((![X1 : $i]:
% 0.37/0.54          (~ (v1_xboole_0 @ X1)
% 0.37/0.54           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.37/0.54           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.37/0.54         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.54      inference('simplify', [status(thm)], ['64'])).
% 0.37/0.54  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.54  thf('67', plain,
% 0.37/0.54      ((![X1 : $i]:
% 0.37/0.54          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))))
% 0.37/0.54         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.54      inference('simplify_reflect+', [status(thm)], ['65', '66'])).
% 0.37/0.54  thf('68', plain,
% 0.37/0.54      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.37/0.54         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.37/0.54      inference('sup-', [status(thm)], ['59', '67'])).
% 0.37/0.54  thf('69', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.37/0.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.37/0.54  thf('71', plain, ((((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.37/0.54      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.37/0.54  thf('72', plain,
% 0.37/0.54      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))) | 
% 0.37/0.54       ~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.37/0.54      inference('split', [status(esa)], ['28'])).
% 0.37/0.54  thf('73', plain, (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.37/0.54      inference('sat_resolution*', [status(thm)], ['71', '72'])).
% 0.37/0.54  thf('74', plain, (~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A))),
% 0.37/0.54      inference('simpl_trail', [status(thm)], ['37', '73'])).
% 0.37/0.54  thf('75', plain, (~ (v1_relat_1 @ sk_A)),
% 0.37/0.54      inference('sup-', [status(thm)], ['20', '74'])).
% 0.37/0.54  thf('76', plain, ((v1_relat_1 @ sk_A)),
% 0.37/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.54  thf('77', plain, ($false), inference('demod', [status(thm)], ['75', '76'])).
% 0.37/0.54  
% 0.37/0.54  % SZS output end Refutation
% 0.37/0.54  
% 0.37/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
