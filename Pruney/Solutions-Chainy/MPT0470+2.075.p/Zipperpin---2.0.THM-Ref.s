%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lcfxfzURas

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:37 EST 2020

% Result     : Theorem 0.87s
% Output     : Refutation 0.87s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 286 expanded)
%              Number of leaves         :   22 (  96 expanded)
%              Depth                    :   30
%              Number of atoms          :  706 (1929 expanded)
%              Number of equality atoms :   55 ( 150 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) ) @ ( k2_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X14 @ X13 ) )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X14 ) @ ( k1_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('11',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('12',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X9: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','22'])).

thf('24',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['37'])).

thf('39',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','39'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('41',plain,(
    ! [X1: $i,X3: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('43',plain,(
    ! [X5: $i] :
      ( ( k4_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('45',plain,(
    ! [X10: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','48'])).

thf('50',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','38'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

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
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('63',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('67',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','68'])).

thf('70',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('72',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','72'])).

thf('74',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('76',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['57'])).

thf('78',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X1 ) ) ) ),
    inference(simpl_trail,[status(thm)],['63','78'])).

thf('80',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','79'])).

thf('81',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,(
    $false ),
    inference(demod,[status(thm)],['80','81','82'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.lcfxfzURas
% 0.13/0.37  % Computer   : n015.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 09:55:38 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.87/1.07  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.87/1.07  % Solved by: fo/fo7.sh
% 0.87/1.07  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.87/1.07  % done 674 iterations in 0.584s
% 0.87/1.07  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.87/1.07  % SZS output start Refutation
% 0.87/1.07  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.87/1.07  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.87/1.07  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.87/1.07  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.87/1.07  thf(sk_A_type, type, sk_A: $i).
% 0.87/1.07  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.87/1.07  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.87/1.07  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.87/1.07  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.87/1.07  thf(dt_k5_relat_1, axiom,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.87/1.07       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.87/1.07  thf('0', plain,
% 0.87/1.07      (![X7 : $i, X8 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X7)
% 0.87/1.07          | ~ (v1_relat_1 @ X8)
% 0.87/1.07          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 0.87/1.07      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.87/1.07  thf(t60_relat_1, axiom,
% 0.87/1.07    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.87/1.07     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.87/1.07  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.87/1.07      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.87/1.07  thf(t45_relat_1, axiom,
% 0.87/1.07    (![A:$i]:
% 0.87/1.07     ( ( v1_relat_1 @ A ) =>
% 0.87/1.07       ( ![B:$i]:
% 0.87/1.07         ( ( v1_relat_1 @ B ) =>
% 0.87/1.07           ( r1_tarski @
% 0.87/1.07             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.87/1.07  thf('2', plain,
% 0.87/1.07      (![X11 : $i, X12 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X11)
% 0.87/1.07          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X12 @ X11)) @ 
% 0.87/1.07             (k2_relat_1 @ X11))
% 0.87/1.07          | ~ (v1_relat_1 @ X12))),
% 0.87/1.07      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.87/1.07  thf('3', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.87/1.07           k1_xboole_0)
% 0.87/1.07          | ~ (v1_relat_1 @ X0)
% 0.87/1.07          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.87/1.07      inference('sup+', [status(thm)], ['1', '2'])).
% 0.87/1.07  thf(t62_relat_1, conjecture,
% 0.87/1.07    (![A:$i]:
% 0.87/1.07     ( ( v1_relat_1 @ A ) =>
% 0.87/1.07       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.87/1.07         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.87/1.07  thf(zf_stmt_0, negated_conjecture,
% 0.87/1.07    (~( ![A:$i]:
% 0.87/1.07        ( ( v1_relat_1 @ A ) =>
% 0.87/1.07          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.87/1.07            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.87/1.07    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.87/1.07  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf(cc1_relat_1, axiom,
% 0.87/1.07    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.87/1.07  thf('5', plain, (![X6 : $i]: ((v1_relat_1 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.87/1.07      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.87/1.07  thf('6', plain,
% 0.87/1.07      (![X7 : $i, X8 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X7)
% 0.87/1.07          | ~ (v1_relat_1 @ X8)
% 0.87/1.07          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 0.87/1.07      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.87/1.07  thf('7', plain, (![X6 : $i]: ((v1_relat_1 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.87/1.07      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.87/1.07  thf('8', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.87/1.07      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.87/1.07  thf(t46_relat_1, axiom,
% 0.87/1.07    (![A:$i]:
% 0.87/1.07     ( ( v1_relat_1 @ A ) =>
% 0.87/1.07       ( ![B:$i]:
% 0.87/1.07         ( ( v1_relat_1 @ B ) =>
% 0.87/1.07           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.87/1.07             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.87/1.07  thf('9', plain,
% 0.87/1.07      (![X13 : $i, X14 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X13)
% 0.87/1.07          | ((k1_relat_1 @ (k5_relat_1 @ X14 @ X13)) = (k1_relat_1 @ X14))
% 0.87/1.07          | ~ (r1_tarski @ (k2_relat_1 @ X14) @ (k1_relat_1 @ X13))
% 0.87/1.07          | ~ (v1_relat_1 @ X14))),
% 0.87/1.07      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.87/1.07  thf('10', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.87/1.07          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.87/1.07          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.87/1.07              = (k1_relat_1 @ k1_xboole_0))
% 0.87/1.07          | ~ (v1_relat_1 @ X0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['8', '9'])).
% 0.87/1.07  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.87/1.07  thf('11', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.87/1.07      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.87/1.07  thf('12', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.87/1.07      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.87/1.07  thf('13', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ k1_xboole_0)
% 0.87/1.07          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.87/1.07          | ~ (v1_relat_1 @ X0))),
% 0.87/1.07      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.87/1.07  thf('14', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.87/1.07          | ~ (v1_relat_1 @ X0)
% 0.87/1.07          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.87/1.07      inference('sup-', [status(thm)], ['7', '13'])).
% 0.87/1.07  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.87/1.07  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.87/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.87/1.07  thf('16', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X0)
% 0.87/1.07          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.87/1.07      inference('demod', [status(thm)], ['14', '15'])).
% 0.87/1.07  thf(fc8_relat_1, axiom,
% 0.87/1.07    (![A:$i]:
% 0.87/1.07     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.87/1.07       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.87/1.07  thf('17', plain,
% 0.87/1.07      (![X9 : $i]:
% 0.87/1.07         (~ (v1_xboole_0 @ (k1_relat_1 @ X9))
% 0.87/1.07          | ~ (v1_relat_1 @ X9)
% 0.87/1.07          | (v1_xboole_0 @ X9))),
% 0.87/1.07      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.87/1.07  thf('18', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.87/1.07          | ~ (v1_relat_1 @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.87/1.07          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.87/1.07      inference('sup-', [status(thm)], ['16', '17'])).
% 0.87/1.07  thf('19', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.87/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.87/1.07  thf('20', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.87/1.07          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.87/1.07      inference('demod', [status(thm)], ['18', '19'])).
% 0.87/1.07  thf('21', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X0)
% 0.87/1.07          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.87/1.07          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.87/1.07          | ~ (v1_relat_1 @ X0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['6', '20'])).
% 0.87/1.07  thf('22', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.87/1.07          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.87/1.07          | ~ (v1_relat_1 @ X0))),
% 0.87/1.07      inference('simplify', [status(thm)], ['21'])).
% 0.87/1.07  thf('23', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.87/1.07          | ~ (v1_relat_1 @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.87/1.07      inference('sup-', [status(thm)], ['5', '22'])).
% 0.87/1.07  thf('24', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.87/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.87/1.07  thf('25', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.87/1.07      inference('demod', [status(thm)], ['23', '24'])).
% 0.87/1.07  thf('26', plain, (![X6 : $i]: ((v1_relat_1 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.87/1.07      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.87/1.07  thf(l13_xboole_0, axiom,
% 0.87/1.07    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.87/1.07  thf('27', plain,
% 0.87/1.07      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.87/1.07      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.87/1.07  thf('28', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.87/1.07      inference('demod', [status(thm)], ['23', '24'])).
% 0.87/1.07  thf('29', plain,
% 0.87/1.07      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.87/1.07      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.87/1.07  thf('30', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X0)
% 0.87/1.07          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.87/1.07      inference('sup-', [status(thm)], ['28', '29'])).
% 0.87/1.07  thf('31', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.87/1.07          | ~ (v1_xboole_0 @ X0)
% 0.87/1.07          | ~ (v1_relat_1 @ X1))),
% 0.87/1.07      inference('sup+', [status(thm)], ['27', '30'])).
% 0.87/1.07  thf('32', plain,
% 0.87/1.07      (![X7 : $i, X8 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X7)
% 0.87/1.07          | ~ (v1_relat_1 @ X8)
% 0.87/1.07          | (v1_relat_1 @ (k5_relat_1 @ X7 @ X8)))),
% 0.87/1.07      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.87/1.07  thf('33', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         ((v1_relat_1 @ k1_xboole_0)
% 0.87/1.07          | ~ (v1_relat_1 @ X0)
% 0.87/1.07          | ~ (v1_xboole_0 @ X1)
% 0.87/1.07          | ~ (v1_relat_1 @ X0)
% 0.87/1.07          | ~ (v1_relat_1 @ X1))),
% 0.87/1.07      inference('sup+', [status(thm)], ['31', '32'])).
% 0.87/1.07  thf('34', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X1)
% 0.87/1.07          | ~ (v1_xboole_0 @ X1)
% 0.87/1.07          | ~ (v1_relat_1 @ X0)
% 0.87/1.07          | (v1_relat_1 @ k1_xboole_0))),
% 0.87/1.07      inference('simplify', [status(thm)], ['33'])).
% 0.87/1.07  thf('35', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         (~ (v1_xboole_0 @ X0)
% 0.87/1.07          | (v1_relat_1 @ k1_xboole_0)
% 0.87/1.07          | ~ (v1_relat_1 @ X1)
% 0.87/1.07          | ~ (v1_xboole_0 @ X0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['26', '34'])).
% 0.87/1.07  thf('36', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X1)
% 0.87/1.07          | (v1_relat_1 @ k1_xboole_0)
% 0.87/1.07          | ~ (v1_xboole_0 @ X0))),
% 0.87/1.07      inference('simplify', [status(thm)], ['35'])).
% 0.87/1.07  thf('37', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X0)
% 0.87/1.07          | (v1_relat_1 @ k1_xboole_0)
% 0.87/1.07          | ~ (v1_relat_1 @ X1))),
% 0.87/1.07      inference('sup-', [status(thm)], ['25', '36'])).
% 0.87/1.07  thf('38', plain,
% 0.87/1.07      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.87/1.07      inference('condensation', [status(thm)], ['37'])).
% 0.87/1.07  thf('39', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.87/1.07      inference('sup-', [status(thm)], ['4', '38'])).
% 0.87/1.07  thf('40', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.87/1.07           k1_xboole_0)
% 0.87/1.07          | ~ (v1_relat_1 @ X0))),
% 0.87/1.07      inference('demod', [status(thm)], ['3', '39'])).
% 0.87/1.07  thf(l32_xboole_1, axiom,
% 0.87/1.07    (![A:$i,B:$i]:
% 0.87/1.07     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.87/1.07  thf('41', plain,
% 0.87/1.07      (![X1 : $i, X3 : $i]:
% 0.87/1.07         (((k4_xboole_0 @ X1 @ X3) = (k1_xboole_0)) | ~ (r1_tarski @ X1 @ X3))),
% 0.87/1.07      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.87/1.07  thf('42', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X0)
% 0.87/1.07          | ((k4_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.87/1.07              k1_xboole_0) = (k1_xboole_0)))),
% 0.87/1.07      inference('sup-', [status(thm)], ['40', '41'])).
% 0.87/1.07  thf(t3_boole, axiom,
% 0.87/1.07    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.87/1.07  thf('43', plain, (![X5 : $i]: ((k4_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.87/1.07      inference('cnf', [status(esa)], [t3_boole])).
% 0.87/1.07  thf('44', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X0)
% 0.87/1.07          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.87/1.07      inference('demod', [status(thm)], ['42', '43'])).
% 0.87/1.07  thf(fc9_relat_1, axiom,
% 0.87/1.07    (![A:$i]:
% 0.87/1.07     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.87/1.07       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.87/1.07  thf('45', plain,
% 0.87/1.07      (![X10 : $i]:
% 0.87/1.07         (~ (v1_xboole_0 @ (k2_relat_1 @ X10))
% 0.87/1.07          | ~ (v1_relat_1 @ X10)
% 0.87/1.07          | (v1_xboole_0 @ X10))),
% 0.87/1.07      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.87/1.07  thf('46', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.87/1.07          | ~ (v1_relat_1 @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.87/1.07          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.87/1.07      inference('sup-', [status(thm)], ['44', '45'])).
% 0.87/1.07  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.87/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.87/1.07  thf('48', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.87/1.07          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.87/1.07      inference('demod', [status(thm)], ['46', '47'])).
% 0.87/1.07  thf('49', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ k1_xboole_0)
% 0.87/1.07          | ~ (v1_relat_1 @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.87/1.07          | ~ (v1_relat_1 @ X0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['0', '48'])).
% 0.87/1.07  thf('50', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.87/1.07      inference('sup-', [status(thm)], ['4', '38'])).
% 0.87/1.07  thf('51', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X0)
% 0.87/1.07          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.87/1.07          | ~ (v1_relat_1 @ X0))),
% 0.87/1.07      inference('demod', [status(thm)], ['49', '50'])).
% 0.87/1.07  thf('52', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.87/1.07      inference('simplify', [status(thm)], ['51'])).
% 0.87/1.07  thf('53', plain,
% 0.87/1.07      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.87/1.07      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.87/1.07  thf('54', plain,
% 0.87/1.07      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.87/1.07      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.87/1.07  thf('55', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.87/1.07      inference('sup+', [status(thm)], ['53', '54'])).
% 0.87/1.07  thf('56', plain,
% 0.87/1.07      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.87/1.07      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.87/1.07  thf('57', plain,
% 0.87/1.07      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.87/1.07        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('58', plain,
% 0.87/1.07      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.87/1.07         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.87/1.07      inference('split', [status(esa)], ['57'])).
% 0.87/1.07  thf('59', plain,
% 0.87/1.07      ((![X0 : $i]:
% 0.87/1.07          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.87/1.07         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.87/1.07      inference('sup-', [status(thm)], ['56', '58'])).
% 0.87/1.07  thf('60', plain,
% 0.87/1.07      ((![X0 : $i, X1 : $i]:
% 0.87/1.07          (((X0) != (k1_xboole_0))
% 0.87/1.07           | ~ (v1_xboole_0 @ X0)
% 0.87/1.07           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.87/1.07           | ~ (v1_xboole_0 @ X1)))
% 0.87/1.07         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.87/1.07      inference('sup-', [status(thm)], ['55', '59'])).
% 0.87/1.07  thf('61', plain,
% 0.87/1.07      ((![X1 : $i]:
% 0.87/1.07          (~ (v1_xboole_0 @ X1)
% 0.87/1.07           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))
% 0.87/1.07           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.87/1.07         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.87/1.07      inference('simplify', [status(thm)], ['60'])).
% 0.87/1.07  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.87/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.87/1.07  thf('63', plain,
% 0.87/1.07      ((![X1 : $i]:
% 0.87/1.07          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1))))
% 0.87/1.07         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.87/1.07      inference('simplify_reflect+', [status(thm)], ['61', '62'])).
% 0.87/1.07  thf('64', plain,
% 0.87/1.07      (![X0 : $i]:
% 0.87/1.07         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.87/1.07      inference('demod', [status(thm)], ['23', '24'])).
% 0.87/1.07  thf('65', plain,
% 0.87/1.07      (![X0 : $i, X1 : $i]:
% 0.87/1.07         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.87/1.07      inference('sup+', [status(thm)], ['53', '54'])).
% 0.87/1.07  thf('66', plain,
% 0.87/1.07      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.87/1.07      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.87/1.07  thf('67', plain,
% 0.87/1.07      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.87/1.07         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.87/1.07      inference('split', [status(esa)], ['57'])).
% 0.87/1.07  thf('68', plain,
% 0.87/1.07      ((![X0 : $i]:
% 0.87/1.07          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.87/1.07         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.87/1.07      inference('sup-', [status(thm)], ['66', '67'])).
% 0.87/1.07  thf('69', plain,
% 0.87/1.07      ((![X0 : $i, X1 : $i]:
% 0.87/1.07          (((X0) != (k1_xboole_0))
% 0.87/1.07           | ~ (v1_xboole_0 @ X0)
% 0.87/1.07           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.87/1.07           | ~ (v1_xboole_0 @ X1)))
% 0.87/1.07         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.87/1.07      inference('sup-', [status(thm)], ['65', '68'])).
% 0.87/1.07  thf('70', plain,
% 0.87/1.07      ((![X1 : $i]:
% 0.87/1.07          (~ (v1_xboole_0 @ X1)
% 0.87/1.07           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.87/1.07           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.87/1.07         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.87/1.07      inference('simplify', [status(thm)], ['69'])).
% 0.87/1.07  thf('71', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.87/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.87/1.07  thf('72', plain,
% 0.87/1.07      ((![X1 : $i]:
% 0.87/1.07          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.87/1.07         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.87/1.07      inference('simplify_reflect+', [status(thm)], ['70', '71'])).
% 0.87/1.07  thf('73', plain,
% 0.87/1.07      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.87/1.07         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.87/1.07      inference('sup-', [status(thm)], ['64', '72'])).
% 0.87/1.07  thf('74', plain, ((v1_relat_1 @ sk_A)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.87/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.87/1.07  thf('76', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.87/1.07      inference('demod', [status(thm)], ['73', '74', '75'])).
% 0.87/1.07  thf('77', plain,
% 0.87/1.07      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.87/1.07       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.87/1.07      inference('split', [status(esa)], ['57'])).
% 0.87/1.07  thf('78', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.87/1.07      inference('sat_resolution*', [status(thm)], ['76', '77'])).
% 0.87/1.07  thf('79', plain,
% 0.87/1.07      (![X1 : $i]:
% 0.87/1.07         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X1)))),
% 0.87/1.07      inference('simpl_trail', [status(thm)], ['63', '78'])).
% 0.87/1.07  thf('80', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.87/1.07      inference('sup-', [status(thm)], ['52', '79'])).
% 0.87/1.07  thf('81', plain, ((v1_relat_1 @ sk_A)),
% 0.87/1.07      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.87/1.07  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.87/1.07      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.87/1.07  thf('83', plain, ($false),
% 0.87/1.07      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.87/1.07  
% 0.87/1.07  % SZS output end Refutation
% 0.87/1.07  
% 0.87/1.08  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
