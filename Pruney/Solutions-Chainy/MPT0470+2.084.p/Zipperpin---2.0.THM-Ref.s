%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9GfxrTV4vO

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:38 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 289 expanded)
%              Number of leaves         :   22 (  97 expanded)
%              Depth                    :   28
%              Number of atoms          :  683 (1937 expanded)
%              Number of equality atoms :   52 ( 146 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
        = ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','4'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

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

thf('7',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('9',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('10',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('11',plain,
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

thf('12',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X13 @ X14 ) )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ X14 ) @ ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t47_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('14',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('15',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','16'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['8','25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['28','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['42'])).

thf('44',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['5','6','44'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','49'])).

thf('51',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['7','43'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('56',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['56'])).

thf('58',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','58'])).

thf('60',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('62',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('64',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('65',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['56'])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('69',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['56'])).

thf('74',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) ) ),
    inference(simpl_trail,[status(thm)],['62','74'])).

thf('76',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['76','77','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9GfxrTV4vO
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.69/0.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.69/0.88  % Solved by: fo/fo7.sh
% 0.69/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.88  % done 840 iterations in 0.424s
% 0.69/0.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.69/0.88  % SZS output start Refutation
% 0.69/0.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.69/0.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.69/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.69/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.88  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.69/0.88  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.69/0.88  thf(dt_k5_relat_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.69/0.88       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.69/0.88  thf('0', plain,
% 0.69/0.88      (![X7 : $i, X8 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X7)
% 0.69/0.88          | ~ (v1_relat_1 @ X8)
% 0.69/0.88          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 0.69/0.88      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.69/0.88  thf(t60_relat_1, axiom,
% 0.69/0.88    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.69/0.88     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.69/0.88  thf('1', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.88      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.69/0.88  thf(t44_relat_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( v1_relat_1 @ A ) =>
% 0.69/0.88       ( ![B:$i]:
% 0.69/0.88         ( ( v1_relat_1 @ B ) =>
% 0.69/0.88           ( r1_tarski @
% 0.69/0.88             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.69/0.88  thf('2', plain,
% 0.69/0.88      (![X11 : $i, X12 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X11)
% 0.69/0.88          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X12 @ X11)) @ 
% 0.69/0.88             (k1_relat_1 @ X12))
% 0.69/0.88          | ~ (v1_relat_1 @ X12))),
% 0.69/0.88      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.69/0.88  thf(t28_xboole_1, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.69/0.88  thf('3', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.69/0.88      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.69/0.88  thf('4', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X1)
% 0.69/0.88          | ((k3_xboole_0 @ (k1_relat_1 @ (k5_relat_1 @ X0 @ X1)) @ 
% 0.69/0.88              (k1_relat_1 @ X0)) = (k1_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['2', '3'])).
% 0.69/0.88  thf('5', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((k3_xboole_0 @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.69/0.88            k1_xboole_0) = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.69/0.88      inference('sup+', [status(thm)], ['1', '4'])).
% 0.69/0.88  thf(t2_boole, axiom,
% 0.69/0.88    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.69/0.88  thf('6', plain,
% 0.69/0.88      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.88      inference('cnf', [status(esa)], [t2_boole])).
% 0.69/0.88  thf(t62_relat_1, conjecture,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( v1_relat_1 @ A ) =>
% 0.69/0.88       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.69/0.88         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.69/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.88    (~( ![A:$i]:
% 0.69/0.88        ( ( v1_relat_1 @ A ) =>
% 0.69/0.88          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.69/0.88            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.69/0.88    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.69/0.88  thf('7', plain, ((v1_relat_1 @ sk_A)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf(cc1_relat_1, axiom,
% 0.69/0.88    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.69/0.88  thf('8', plain, (![X6 : $i]: ((v1_relat_1 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.69/0.88      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.69/0.88  thf('9', plain,
% 0.69/0.88      (![X7 : $i, X8 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X7)
% 0.69/0.88          | ~ (v1_relat_1 @ X8)
% 0.69/0.88          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 0.69/0.88      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.69/0.88  thf('10', plain, (![X6 : $i]: ((v1_relat_1 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.69/0.88      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.69/0.88  thf('11', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.88      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.69/0.88  thf(t47_relat_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( v1_relat_1 @ A ) =>
% 0.69/0.88       ( ![B:$i]:
% 0.69/0.88         ( ( v1_relat_1 @ B ) =>
% 0.69/0.88           ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) =>
% 0.69/0.88             ( ( k2_relat_1 @ ( k5_relat_1 @ B @ A ) ) = ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.69/0.88  thf('12', plain,
% 0.69/0.88      (![X13 : $i, X14 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X13)
% 0.69/0.88          | ((k2_relat_1 @ (k5_relat_1 @ X13 @ X14)) = (k2_relat_1 @ X14))
% 0.69/0.88          | ~ (r1_tarski @ (k1_relat_1 @ X14) @ (k2_relat_1 @ X13))
% 0.69/0.88          | ~ (v1_relat_1 @ X14))),
% 0.69/0.88      inference('cnf', [status(esa)], [t47_relat_1])).
% 0.69/0.88  thf('13', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (r1_tarski @ k1_xboole_0 @ (k2_relat_1 @ X0))
% 0.69/0.88          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.69/0.88          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.69/0.88              = (k2_relat_1 @ k1_xboole_0))
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['11', '12'])).
% 0.69/0.88  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.69/0.88  thf('14', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.69/0.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.69/0.88  thf('15', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.88      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.69/0.88  thf('16', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ k1_xboole_0)
% 0.69/0.88          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.69/0.88  thf('17', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['10', '16'])).
% 0.69/0.88  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.69/0.88  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.88  thf('19', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.69/0.88      inference('demod', [status(thm)], ['17', '18'])).
% 0.69/0.88  thf(fc9_relat_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.69/0.88       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.69/0.88  thf('20', plain,
% 0.69/0.88      (![X10 : $i]:
% 0.69/0.88         (~ (v1_xboole_0 @ (k2_relat_1 @ X10))
% 0.69/0.88          | ~ (v1_relat_1 @ X10)
% 0.69/0.88          | (v1_xboole_0 @ X10))),
% 0.69/0.88      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.69/0.88  thf('21', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.69/0.88          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['19', '20'])).
% 0.69/0.88  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.88  thf('23', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.69/0.88          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.69/0.88      inference('demod', [status(thm)], ['21', '22'])).
% 0.69/0.88  thf('24', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ k1_xboole_0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['9', '23'])).
% 0.69/0.88  thf('25', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['24'])).
% 0.69/0.88  thf('26', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['8', '25'])).
% 0.69/0.88  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.88  thf('28', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.69/0.88      inference('demod', [status(thm)], ['26', '27'])).
% 0.69/0.88  thf('29', plain, (![X6 : $i]: ((v1_relat_1 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.69/0.88      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.69/0.88  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.88  thf(t8_boole, axiom,
% 0.69/0.88    (![A:$i,B:$i]:
% 0.69/0.88     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.69/0.88  thf('31', plain,
% 0.69/0.88      (![X4 : $i, X5 : $i]:
% 0.69/0.88         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 0.69/0.88      inference('cnf', [status(esa)], [t8_boole])).
% 0.69/0.88  thf('32', plain,
% 0.69/0.88      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['30', '31'])).
% 0.69/0.88  thf('33', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.69/0.88      inference('demod', [status(thm)], ['26', '27'])).
% 0.69/0.88  thf('34', plain,
% 0.69/0.88      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['30', '31'])).
% 0.69/0.88  thf('35', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['33', '34'])).
% 0.69/0.88  thf('36', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (((k1_xboole_0) = (k5_relat_1 @ X1 @ X0))
% 0.69/0.88          | ~ (v1_xboole_0 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X1))),
% 0.69/0.88      inference('sup+', [status(thm)], ['32', '35'])).
% 0.69/0.88  thf('37', plain,
% 0.69/0.88      (![X7 : $i, X8 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X7)
% 0.69/0.88          | ~ (v1_relat_1 @ X8)
% 0.69/0.88          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 0.69/0.88      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.69/0.88  thf('38', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         ((v1_relat_1 @ k1_xboole_0)
% 0.69/0.88          | ~ (v1_relat_1 @ X1)
% 0.69/0.88          | ~ (v1_xboole_0 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X1))),
% 0.69/0.88      inference('sup+', [status(thm)], ['36', '37'])).
% 0.69/0.88  thf('39', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_xboole_0 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ X1)
% 0.69/0.88          | (v1_relat_1 @ k1_xboole_0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['38'])).
% 0.69/0.88  thf('40', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (~ (v1_xboole_0 @ X0)
% 0.69/0.88          | (v1_relat_1 @ k1_xboole_0)
% 0.69/0.88          | ~ (v1_relat_1 @ X1)
% 0.69/0.88          | ~ (v1_xboole_0 @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['29', '39'])).
% 0.69/0.88  thf('41', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X1)
% 0.69/0.88          | (v1_relat_1 @ k1_xboole_0)
% 0.69/0.88          | ~ (v1_xboole_0 @ X0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['40'])).
% 0.69/0.88  thf('42', plain,
% 0.69/0.88      (![X0 : $i, X1 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | (v1_relat_1 @ k1_xboole_0)
% 0.69/0.88          | ~ (v1_relat_1 @ X1))),
% 0.69/0.88      inference('sup-', [status(thm)], ['28', '41'])).
% 0.69/0.88  thf('43', plain,
% 0.69/0.88      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.69/0.88      inference('condensation', [status(thm)], ['42'])).
% 0.69/0.88  thf('44', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.69/0.88      inference('sup-', [status(thm)], ['7', '43'])).
% 0.69/0.88  thf('45', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (((k1_xboole_0) = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('demod', [status(thm)], ['5', '6', '44'])).
% 0.69/0.88  thf(fc8_relat_1, axiom,
% 0.69/0.88    (![A:$i]:
% 0.69/0.88     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.69/0.88       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.69/0.88  thf('46', plain,
% 0.69/0.88      (![X9 : $i]:
% 0.69/0.88         (~ (v1_xboole_0 @ (k1_relat_1 @ X9))
% 0.69/0.88          | ~ (v1_relat_1 @ X9)
% 0.69/0.88          | (v1_xboole_0 @ X9))),
% 0.69/0.88      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.69/0.88  thf('47', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.69/0.88          | ~ (v1_relat_1 @ X0)
% 0.69/0.88          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.69/0.88          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.69/0.88      inference('sup-', [status(thm)], ['45', '46'])).
% 0.69/0.88  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.88  thf('49', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.69/0.88          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.69/0.88      inference('demod', [status(thm)], ['47', '48'])).
% 0.69/0.88  thf('50', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.69/0.88          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['0', '49'])).
% 0.69/0.88  thf('51', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.69/0.88      inference('sup-', [status(thm)], ['7', '43'])).
% 0.69/0.88  thf('52', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0)
% 0.69/0.88          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.69/0.88          | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('demod', [status(thm)], ['50', '51'])).
% 0.69/0.88  thf('53', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)) | ~ (v1_relat_1 @ X0))),
% 0.69/0.88      inference('simplify', [status(thm)], ['52'])).
% 0.69/0.88  thf('54', plain,
% 0.69/0.88      (![X4 : $i, X5 : $i]:
% 0.69/0.88         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 0.69/0.88      inference('cnf', [status(esa)], [t8_boole])).
% 0.69/0.88  thf('55', plain,
% 0.69/0.88      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['30', '31'])).
% 0.69/0.88  thf('56', plain,
% 0.69/0.88      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.69/0.88        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('57', plain,
% 0.69/0.88      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.69/0.88         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('split', [status(esa)], ['56'])).
% 0.69/0.88  thf('58', plain,
% 0.69/0.88      ((![X0 : $i]:
% 0.69/0.88          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.69/0.88         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['55', '57'])).
% 0.69/0.88  thf('59', plain,
% 0.69/0.88      ((![X0 : $i, X1 : $i]:
% 0.69/0.88          (((X0) != (k1_xboole_0))
% 0.69/0.88           | ~ (v1_xboole_0 @ X0)
% 0.69/0.88           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.69/0.88           | ~ (v1_xboole_0 @ X1)))
% 0.69/0.88         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['54', '58'])).
% 0.69/0.88  thf('60', plain,
% 0.69/0.88      ((![X1 : $i]:
% 0.69/0.88          (~ (v1_xboole_0 @ X1)
% 0.69/0.88           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.69/0.88           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.69/0.88         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('simplify', [status(thm)], ['59'])).
% 0.69/0.88  thf('61', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.88  thf('62', plain,
% 0.69/0.88      ((![X1 : $i]:
% 0.69/0.88          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.69/0.88         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.69/0.88      inference('simplify_reflect+', [status(thm)], ['60', '61'])).
% 0.69/0.88  thf('63', plain,
% 0.69/0.88      (![X0 : $i]:
% 0.69/0.88         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.69/0.88      inference('demod', [status(thm)], ['26', '27'])).
% 0.69/0.88  thf('64', plain,
% 0.69/0.88      (![X4 : $i, X5 : $i]:
% 0.69/0.88         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 0.69/0.88      inference('cnf', [status(esa)], [t8_boole])).
% 0.69/0.88  thf('65', plain,
% 0.69/0.88      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.69/0.88         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.69/0.88      inference('split', [status(esa)], ['56'])).
% 0.69/0.88  thf('66', plain,
% 0.69/0.88      ((![X0 : $i]:
% 0.69/0.88          (((X0) != (k1_xboole_0))
% 0.69/0.88           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 0.69/0.88           | ~ (v1_xboole_0 @ X0)))
% 0.69/0.88         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['64', '65'])).
% 0.69/0.88  thf('67', plain,
% 0.69/0.88      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.69/0.88         | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))))
% 0.69/0.88         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.69/0.88      inference('simplify', [status(thm)], ['66'])).
% 0.69/0.88  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.88  thf('69', plain,
% 0.69/0.88      ((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0)))
% 0.69/0.88         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.69/0.88      inference('simplify_reflect+', [status(thm)], ['67', '68'])).
% 0.69/0.88  thf('70', plain,
% 0.69/0.88      ((~ (v1_relat_1 @ sk_A))
% 0.69/0.88         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.69/0.88      inference('sup-', [status(thm)], ['63', '69'])).
% 0.69/0.88  thf('71', plain, ((v1_relat_1 @ sk_A)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('72', plain, ((((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.69/0.88      inference('demod', [status(thm)], ['70', '71'])).
% 0.69/0.88  thf('73', plain,
% 0.69/0.88      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))) | 
% 0.69/0.88       ~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.69/0.88      inference('split', [status(esa)], ['56'])).
% 0.69/0.88  thf('74', plain, (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.69/0.88      inference('sat_resolution*', [status(thm)], ['72', '73'])).
% 0.69/0.88  thf('75', plain,
% 0.69/0.88      (![X1 : $i]:
% 0.69/0.88         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A)))),
% 0.69/0.88      inference('simpl_trail', [status(thm)], ['62', '74'])).
% 0.69/0.88  thf('76', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.69/0.88      inference('sup-', [status(thm)], ['53', '75'])).
% 0.69/0.88  thf('77', plain, ((v1_relat_1 @ sk_A)),
% 0.69/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.88  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.88  thf('79', plain, ($false),
% 0.69/0.88      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.69/0.88  
% 0.69/0.88  % SZS output end Refutation
% 0.69/0.88  
% 0.69/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
