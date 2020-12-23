%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KLSxZ6KKWG

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:31 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 308 expanded)
%              Number of leaves         :   20 ( 101 expanded)
%              Depth                    :   29
%              Number of atoms          :  690 (1999 expanded)
%              Number of equality atoms :   47 ( 130 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

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

thf('4',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('6',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('7',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('8',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('14',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','23'])).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('29',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('30',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['26','41'])).

thf('43',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('47',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','50'])).

thf('52',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','42'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('56',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('57',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('65',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('67',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('69',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','70'])).

thf('72',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('74',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('78',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['75','76','77'])).

thf('79',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('80',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['65','80'])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['82','83','84'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KLSxZ6KKWG
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:55:18 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.64  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.64  % Solved by: fo/fo7.sh
% 0.45/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.64  % done 328 iterations in 0.180s
% 0.45/0.64  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.64  % SZS output start Refutation
% 0.45/0.64  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.45/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.64  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.64  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.64  thf(dt_k5_relat_1, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.45/0.64       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.45/0.64  thf('0', plain,
% 0.45/0.64      (![X7 : $i, X8 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X7)
% 0.45/0.64          | ~ (v1_relat_1 @ X8)
% 0.45/0.64          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.45/0.64  thf(t60_relat_1, axiom,
% 0.45/0.64    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.45/0.64     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.45/0.64  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.64      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.64  thf(t45_relat_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( v1_relat_1 @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( v1_relat_1 @ B ) =>
% 0.45/0.64           ( r1_tarski @
% 0.45/0.64             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.45/0.64  thf('2', plain,
% 0.45/0.64      (![X13 : $i, X14 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X13)
% 0.45/0.64          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X14 @ X13)) @ 
% 0.45/0.64             (k2_relat_1 @ X13))
% 0.45/0.64          | ~ (v1_relat_1 @ X14))),
% 0.45/0.64      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.45/0.64  thf('3', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.45/0.64           k1_xboole_0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['1', '2'])).
% 0.45/0.64  thf(t62_relat_1, conjecture,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( v1_relat_1 @ A ) =>
% 0.45/0.64       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.45/0.64         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.45/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.64    (~( ![A:$i]:
% 0.45/0.64        ( ( v1_relat_1 @ A ) =>
% 0.45/0.64          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.45/0.64            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.45/0.64    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.45/0.64  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf(cc1_relat_1, axiom,
% 0.45/0.64    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.45/0.64  thf('5', plain, (![X6 : $i]: ((v1_relat_1 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.45/0.64  thf('6', plain,
% 0.45/0.64      (![X7 : $i, X8 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X7)
% 0.45/0.64          | ~ (v1_relat_1 @ X8)
% 0.45/0.64          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.45/0.64  thf('7', plain, (![X6 : $i]: ((v1_relat_1 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.45/0.64  thf('8', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.45/0.64      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.45/0.64  thf(t44_relat_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( v1_relat_1 @ A ) =>
% 0.45/0.64       ( ![B:$i]:
% 0.45/0.64         ( ( v1_relat_1 @ B ) =>
% 0.45/0.64           ( r1_tarski @
% 0.45/0.64             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.45/0.64  thf('9', plain,
% 0.45/0.64      (![X11 : $i, X12 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X11)
% 0.45/0.64          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X12 @ X11)) @ 
% 0.45/0.64             (k1_relat_1 @ X12))
% 0.45/0.64          | ~ (v1_relat_1 @ X12))),
% 0.45/0.64      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.45/0.64  thf('10', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.45/0.64           k1_xboole_0)
% 0.45/0.64          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('sup+', [status(thm)], ['8', '9'])).
% 0.45/0.64  thf('11', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.45/0.64             k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['7', '10'])).
% 0.45/0.64  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.64  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.64  thf('13', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X0)
% 0.45/0.64          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.45/0.64             k1_xboole_0))),
% 0.45/0.64      inference('demod', [status(thm)], ['11', '12'])).
% 0.45/0.64  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.64  thf('14', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.45/0.64      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.64  thf(d10_xboole_0, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.64  thf('15', plain,
% 0.45/0.64      (![X0 : $i, X2 : $i]:
% 0.45/0.64         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.64      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.64  thf('16', plain,
% 0.45/0.64      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.64  thf('17', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X0)
% 0.45/0.64          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['13', '16'])).
% 0.45/0.64  thf(fc8_relat_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.45/0.64       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.45/0.64  thf('18', plain,
% 0.45/0.64      (![X9 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ (k1_relat_1 @ X9))
% 0.45/0.64          | ~ (v1_relat_1 @ X9)
% 0.45/0.64          | (v1_xboole_0 @ X9))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.45/0.64  thf('19', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['17', '18'])).
% 0.45/0.64  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.64  thf('21', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X0)
% 0.45/0.64          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['19', '20'])).
% 0.45/0.64  thf('22', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.45/0.64          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['6', '21'])).
% 0.45/0.64  thf('23', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.45/0.64          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['22'])).
% 0.45/0.64  thf('24', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['5', '23'])).
% 0.45/0.64  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.64  thf('26', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['24', '25'])).
% 0.45/0.64  thf('27', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('28', plain, (![X6 : $i]: ((v1_relat_1 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.45/0.64      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.45/0.64  thf('29', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.64  thf(t8_boole, axiom,
% 0.45/0.64    (![A:$i,B:$i]:
% 0.45/0.64     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.45/0.64  thf('30', plain,
% 0.45/0.64      (![X4 : $i, X5 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t8_boole])).
% 0.45/0.64  thf('31', plain,
% 0.45/0.64      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.64  thf('32', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['24', '25'])).
% 0.45/0.64  thf('33', plain,
% 0.45/0.64      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.64  thf('34', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X0)
% 0.45/0.64          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['32', '33'])).
% 0.45/0.64  thf('35', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.45/0.64          | ~ (v1_xboole_0 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X1))),
% 0.45/0.64      inference('sup+', [status(thm)], ['31', '34'])).
% 0.45/0.64  thf('36', plain,
% 0.45/0.64      (![X7 : $i, X8 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X7)
% 0.45/0.64          | ~ (v1_relat_1 @ X8)
% 0.45/0.64          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 0.45/0.64      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.45/0.64  thf('37', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         ((v1_relat_1 @ k1_xboole_0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_xboole_0 @ X1)
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | ~ (v1_relat_1 @ X1))),
% 0.45/0.64      inference('sup+', [status(thm)], ['35', '36'])).
% 0.45/0.64  thf('38', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X1)
% 0.45/0.64          | ~ (v1_xboole_0 @ X1)
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | (v1_relat_1 @ k1_xboole_0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['37'])).
% 0.45/0.64  thf('39', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ X0)
% 0.45/0.64          | (v1_relat_1 @ k1_xboole_0)
% 0.45/0.64          | ~ (v1_relat_1 @ X1)
% 0.45/0.64          | ~ (v1_xboole_0 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['28', '38'])).
% 0.45/0.64  thf('40', plain,
% 0.45/0.64      (![X0 : $i, X1 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X1)
% 0.45/0.64          | (v1_relat_1 @ k1_xboole_0)
% 0.45/0.64          | ~ (v1_xboole_0 @ X0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['39'])).
% 0.45/0.64  thf('41', plain,
% 0.45/0.64      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['27', '40'])).
% 0.45/0.64  thf('42', plain,
% 0.45/0.64      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['26', '41'])).
% 0.45/0.64  thf('43', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.45/0.64      inference('sup-', [status(thm)], ['4', '42'])).
% 0.45/0.64  thf('44', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.45/0.64           k1_xboole_0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['3', '43'])).
% 0.45/0.64  thf('45', plain,
% 0.45/0.64      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['14', '15'])).
% 0.45/0.64  thf('46', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X0)
% 0.45/0.64          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['44', '45'])).
% 0.45/0.64  thf(fc9_relat_1, axiom,
% 0.45/0.64    (![A:$i]:
% 0.45/0.64     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.45/0.64       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.45/0.64  thf('47', plain,
% 0.45/0.64      (![X10 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ (k2_relat_1 @ X10))
% 0.45/0.64          | ~ (v1_relat_1 @ X10)
% 0.45/0.64          | (v1_xboole_0 @ X10))),
% 0.45/0.64      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.45/0.64  thf('48', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.45/0.64          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.45/0.64      inference('sup-', [status(thm)], ['46', '47'])).
% 0.45/0.64  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.64  thf('50', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X0)
% 0.45/0.64          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.45/0.64          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['48', '49'])).
% 0.45/0.64  thf('51', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ k1_xboole_0)
% 0.45/0.64          | ~ (v1_relat_1 @ X0)
% 0.45/0.64          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['0', '50'])).
% 0.45/0.64  thf('52', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.45/0.64      inference('sup-', [status(thm)], ['4', '42'])).
% 0.45/0.64  thf('53', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X0)
% 0.45/0.64          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.45/0.64          | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('demod', [status(thm)], ['51', '52'])).
% 0.45/0.64  thf('54', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.45/0.64      inference('simplify', [status(thm)], ['53'])).
% 0.45/0.64  thf('55', plain,
% 0.45/0.64      (![X4 : $i, X5 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t8_boole])).
% 0.45/0.64  thf('56', plain,
% 0.45/0.64      (![X4 : $i, X5 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t8_boole])).
% 0.45/0.64  thf('57', plain,
% 0.45/0.64      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.45/0.64        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('58', plain,
% 0.45/0.64      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.45/0.64         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.45/0.64      inference('split', [status(esa)], ['57'])).
% 0.45/0.64  thf('59', plain,
% 0.45/0.64      ((![X0 : $i]:
% 0.45/0.64          (((X0) != (k1_xboole_0))
% 0.45/0.64           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 0.45/0.64           | ~ (v1_xboole_0 @ X0)))
% 0.45/0.64         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['56', '58'])).
% 0.45/0.64  thf('60', plain,
% 0.45/0.64      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.64         | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))))
% 0.45/0.64         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['59'])).
% 0.45/0.64  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.64  thf('62', plain,
% 0.45/0.64      ((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0)))
% 0.45/0.64         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.45/0.64      inference('simplify_reflect+', [status(thm)], ['60', '61'])).
% 0.45/0.64  thf('63', plain,
% 0.45/0.64      ((![X0 : $i]:
% 0.45/0.64          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0))
% 0.45/0.64           | ~ (v1_xboole_0 @ X0)
% 0.45/0.64           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.45/0.64         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['55', '62'])).
% 0.45/0.64  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.64  thf('65', plain,
% 0.45/0.64      ((![X0 : $i]:
% 0.45/0.64          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0)))
% 0.45/0.64         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.45/0.64      inference('demod', [status(thm)], ['63', '64'])).
% 0.45/0.64  thf('66', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['24', '25'])).
% 0.45/0.64  thf('67', plain,
% 0.45/0.64      (![X4 : $i, X5 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 0.45/0.64      inference('cnf', [status(esa)], [t8_boole])).
% 0.45/0.64  thf('68', plain,
% 0.45/0.64      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['29', '30'])).
% 0.45/0.64  thf('69', plain,
% 0.45/0.64      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.45/0.64         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('split', [status(esa)], ['57'])).
% 0.45/0.64  thf('70', plain,
% 0.45/0.64      ((![X0 : $i]:
% 0.45/0.64          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.45/0.64         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['68', '69'])).
% 0.45/0.64  thf('71', plain,
% 0.45/0.64      ((![X0 : $i, X1 : $i]:
% 0.45/0.64          (((X0) != (k1_xboole_0))
% 0.45/0.64           | ~ (v1_xboole_0 @ X0)
% 0.45/0.64           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.45/0.64           | ~ (v1_xboole_0 @ X1)))
% 0.45/0.64         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['67', '70'])).
% 0.45/0.64  thf('72', plain,
% 0.45/0.64      ((![X1 : $i]:
% 0.45/0.64          (~ (v1_xboole_0 @ X1)
% 0.45/0.64           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.45/0.64           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.45/0.64         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('simplify', [status(thm)], ['71'])).
% 0.45/0.64  thf('73', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.64  thf('74', plain,
% 0.45/0.64      ((![X1 : $i]:
% 0.45/0.64          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.45/0.64         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('simplify_reflect+', [status(thm)], ['72', '73'])).
% 0.45/0.64  thf('75', plain,
% 0.45/0.64      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.45/0.64         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.45/0.64      inference('sup-', [status(thm)], ['66', '74'])).
% 0.45/0.64  thf('76', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('77', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.64  thf('78', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.45/0.64      inference('demod', [status(thm)], ['75', '76', '77'])).
% 0.45/0.64  thf('79', plain,
% 0.45/0.64      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.45/0.64       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.45/0.64      inference('split', [status(esa)], ['57'])).
% 0.45/0.64  thf('80', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.45/0.64      inference('sat_resolution*', [status(thm)], ['78', '79'])).
% 0.45/0.64  thf('81', plain,
% 0.45/0.64      (![X0 : $i]:
% 0.45/0.64         (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.45/0.64      inference('simpl_trail', [status(thm)], ['65', '80'])).
% 0.45/0.64  thf('82', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.45/0.64      inference('sup-', [status(thm)], ['54', '81'])).
% 0.45/0.64  thf('83', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.64  thf('84', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.64  thf('85', plain, ($false),
% 0.45/0.64      inference('demod', [status(thm)], ['82', '83', '84'])).
% 0.45/0.64  
% 0.45/0.64  % SZS output end Refutation
% 0.45/0.64  
% 0.45/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
