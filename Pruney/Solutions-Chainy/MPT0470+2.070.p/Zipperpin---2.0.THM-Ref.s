%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TERJ1JA79U

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:36 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 512 expanded)
%              Number of leaves         :   22 ( 168 expanded)
%              Depth                    :   35
%              Number of atoms          :  758 (3452 expanded)
%              Number of equality atoms :   66 ( 250 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('5',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('6',plain,
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

thf('7',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('9',plain,(
    ! [X1: $i] :
      ( r1_tarski @ k1_xboole_0 @ X1 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('10',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','20'])).

thf('22',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf('28',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('29',plain,(
    ! [X3: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(t37_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k2_relat_1 @ A )
          = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) )
        & ( ( k1_relat_1 @ A )
          = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('30',plain,(
    ! [X8: $i] :
      ( ( ( k2_relat_1 @ X8 )
        = ( k1_relat_1 @ ( k4_relat_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t37_relat_1])).

thf('31',plain,(
    ! [X6: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X6 ) )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','34'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

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

thf('37',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('39',plain,(
    ! [X2: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','25'])).

thf('41',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['46'])).

thf('48',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','47'])).

thf('49',plain,(
    v1_xboole_0 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('51',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('52',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X12 @ X11 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X11 ) @ ( k4_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','47'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','55'])).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('60',plain,(
    ! [X7: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X7 ) )
        = X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['0','63'])).

thf('65',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','47'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('69',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['69'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['69'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('80',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ sk_A ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['69'])).

thf('85',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['71','85'])).

thf('87',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','86'])).

thf('88',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    $false ),
    inference(simplify,[status(thm)],['90'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TERJ1JA79U
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:31:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.70/0.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.92  % Solved by: fo/fo7.sh
% 0.70/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.92  % done 786 iterations in 0.462s
% 0.70/0.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.92  % SZS output start Refutation
% 0.70/0.92  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.70/0.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.70/0.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.70/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.92  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.70/0.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.70/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.92  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.70/0.92  thf(dt_k5_relat_1, axiom,
% 0.70/0.92    (![A:$i,B:$i]:
% 0.70/0.92     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.70/0.92       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.70/0.92  thf('0', plain,
% 0.70/0.92      (![X4 : $i, X5 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ X4)
% 0.70/0.92          | ~ (v1_relat_1 @ X5)
% 0.70/0.92          | (v1_relat_1 @ (k5_relat_1 @ X4 @ X5)))),
% 0.70/0.92      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.70/0.92  thf(dt_k4_relat_1, axiom,
% 0.70/0.92    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.70/0.92  thf('1', plain,
% 0.70/0.92      (![X3 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X3)) | ~ (v1_relat_1 @ X3))),
% 0.70/0.92      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.70/0.92  thf(l13_xboole_0, axiom,
% 0.70/0.92    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.70/0.92  thf('2', plain,
% 0.70/0.92      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.92      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.70/0.92  thf(cc1_relat_1, axiom,
% 0.70/0.92    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.70/0.92  thf('3', plain, (![X2 : $i]: ((v1_relat_1 @ X2) | ~ (v1_xboole_0 @ X2))),
% 0.70/0.92      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.70/0.92  thf('4', plain,
% 0.70/0.92      (![X4 : $i, X5 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ X4)
% 0.70/0.92          | ~ (v1_relat_1 @ X5)
% 0.70/0.92          | (v1_relat_1 @ (k5_relat_1 @ X4 @ X5)))),
% 0.70/0.92      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.70/0.92  thf('5', plain, (![X2 : $i]: ((v1_relat_1 @ X2) | ~ (v1_xboole_0 @ X2))),
% 0.70/0.92      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.70/0.92  thf(t60_relat_1, axiom,
% 0.70/0.92    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.70/0.92     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.70/0.92  thf('6', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.92      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.70/0.92  thf(t46_relat_1, axiom,
% 0.70/0.92    (![A:$i]:
% 0.70/0.92     ( ( v1_relat_1 @ A ) =>
% 0.70/0.92       ( ![B:$i]:
% 0.70/0.92         ( ( v1_relat_1 @ B ) =>
% 0.70/0.92           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.70/0.92             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.70/0.92  thf('7', plain,
% 0.70/0.92      (![X9 : $i, X10 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ X9)
% 0.70/0.92          | ((k1_relat_1 @ (k5_relat_1 @ X10 @ X9)) = (k1_relat_1 @ X10))
% 0.70/0.92          | ~ (r1_tarski @ (k2_relat_1 @ X10) @ (k1_relat_1 @ X9))
% 0.70/0.92          | ~ (v1_relat_1 @ X10))),
% 0.70/0.92      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.70/0.92  thf('8', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (r1_tarski @ k1_xboole_0 @ (k1_relat_1 @ X0))
% 0.70/0.92          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.70/0.92          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.70/0.92              = (k1_relat_1 @ k1_xboole_0))
% 0.70/0.92          | ~ (v1_relat_1 @ X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['6', '7'])).
% 0.70/0.92  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.70/0.92  thf('9', plain, (![X1 : $i]: (r1_tarski @ k1_xboole_0 @ X1)),
% 0.70/0.92      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.70/0.92  thf('10', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.92      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.70/0.92  thf('11', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ k1_xboole_0)
% 0.70/0.92          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 0.70/0.92          | ~ (v1_relat_1 @ X0))),
% 0.70/0.92      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.70/0.92  thf('12', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.70/0.92          | ~ (v1_relat_1 @ X0)
% 0.70/0.92          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['5', '11'])).
% 0.70/0.92  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.70/0.92  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.70/0.92  thf('14', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ X0)
% 0.70/0.92          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.70/0.92      inference('demod', [status(thm)], ['12', '13'])).
% 0.70/0.92  thf(fc8_relat_1, axiom,
% 0.70/0.92    (![A:$i]:
% 0.70/0.92     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.70/0.92       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.70/0.92  thf('15', plain,
% 0.70/0.92      (![X6 : $i]:
% 0.70/0.92         (~ (v1_xboole_0 @ (k1_relat_1 @ X6))
% 0.70/0.92          | ~ (v1_relat_1 @ X6)
% 0.70/0.92          | (v1_xboole_0 @ X6))),
% 0.70/0.92      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.70/0.92  thf('16', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.70/0.92          | ~ (v1_relat_1 @ X0)
% 0.70/0.92          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.70/0.92          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['14', '15'])).
% 0.70/0.92  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.70/0.92  thf('18', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ X0)
% 0.70/0.92          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.70/0.92          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.70/0.92      inference('demod', [status(thm)], ['16', '17'])).
% 0.70/0.92  thf('19', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ X0)
% 0.70/0.92          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.70/0.92          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.70/0.92          | ~ (v1_relat_1 @ X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['4', '18'])).
% 0.70/0.92  thf('20', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.70/0.92          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.70/0.92          | ~ (v1_relat_1 @ X0))),
% 0.70/0.92      inference('simplify', [status(thm)], ['19'])).
% 0.70/0.92  thf('21', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.70/0.92          | ~ (v1_relat_1 @ X0)
% 0.70/0.92          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['3', '20'])).
% 0.70/0.92  thf('22', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.70/0.92  thf('23', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.70/0.92      inference('demod', [status(thm)], ['21', '22'])).
% 0.70/0.92  thf('24', plain,
% 0.70/0.92      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.92      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.70/0.92  thf('25', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ X0)
% 0.70/0.92          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['23', '24'])).
% 0.70/0.92  thf('26', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.70/0.92          | ~ (v1_xboole_0 @ X0)
% 0.70/0.92          | ~ (v1_relat_1 @ X1))),
% 0.70/0.92      inference('sup+', [status(thm)], ['2', '25'])).
% 0.70/0.92  thf('27', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ X0)
% 0.70/0.92          | ~ (v1_xboole_0 @ X1)
% 0.70/0.92          | ((k5_relat_1 @ X1 @ (k4_relat_1 @ X0)) = (k1_xboole_0)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['1', '26'])).
% 0.70/0.92  thf('28', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.92      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.70/0.92  thf('29', plain,
% 0.70/0.92      (![X3 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X3)) | ~ (v1_relat_1 @ X3))),
% 0.70/0.92      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.70/0.92  thf(t37_relat_1, axiom,
% 0.70/0.92    (![A:$i]:
% 0.70/0.92     ( ( v1_relat_1 @ A ) =>
% 0.70/0.92       ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k4_relat_1 @ A ) ) ) & 
% 0.70/0.92         ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k4_relat_1 @ A ) ) ) ) ))).
% 0.70/0.92  thf('30', plain,
% 0.70/0.92      (![X8 : $i]:
% 0.70/0.92         (((k2_relat_1 @ X8) = (k1_relat_1 @ (k4_relat_1 @ X8)))
% 0.70/0.92          | ~ (v1_relat_1 @ X8))),
% 0.70/0.92      inference('cnf', [status(esa)], [t37_relat_1])).
% 0.70/0.92  thf('31', plain,
% 0.70/0.92      (![X6 : $i]:
% 0.70/0.92         (~ (v1_xboole_0 @ (k1_relat_1 @ X6))
% 0.70/0.92          | ~ (v1_relat_1 @ X6)
% 0.70/0.92          | (v1_xboole_0 @ X6))),
% 0.70/0.92      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.70/0.92  thf('32', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.70/0.92          | ~ (v1_relat_1 @ X0)
% 0.70/0.92          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.70/0.92          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['30', '31'])).
% 0.70/0.92  thf('33', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ X0)
% 0.70/0.92          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.70/0.92          | ~ (v1_relat_1 @ X0)
% 0.70/0.92          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['29', '32'])).
% 0.70/0.92  thf('34', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v1_xboole_0 @ (k2_relat_1 @ X0))
% 0.70/0.92          | (v1_xboole_0 @ (k4_relat_1 @ X0))
% 0.70/0.92          | ~ (v1_relat_1 @ X0))),
% 0.70/0.92      inference('simplify', [status(thm)], ['33'])).
% 0.70/0.92  thf('35', plain,
% 0.70/0.92      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.70/0.92        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.70/0.92        | (v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['28', '34'])).
% 0.70/0.92  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.70/0.92  thf(t62_relat_1, conjecture,
% 0.70/0.92    (![A:$i]:
% 0.70/0.92     ( ( v1_relat_1 @ A ) =>
% 0.70/0.92       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.70/0.92         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.70/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.92    (~( ![A:$i]:
% 0.70/0.92        ( ( v1_relat_1 @ A ) =>
% 0.70/0.92          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.70/0.92            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.70/0.92    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.70/0.92  thf('37', plain, ((v1_relat_1 @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('38', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.70/0.92      inference('demod', [status(thm)], ['21', '22'])).
% 0.70/0.92  thf('39', plain, (![X2 : $i]: ((v1_relat_1 @ X2) | ~ (v1_xboole_0 @ X2))),
% 0.70/0.92      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.70/0.92  thf('40', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.70/0.92          | ~ (v1_xboole_0 @ X0)
% 0.70/0.92          | ~ (v1_relat_1 @ X1))),
% 0.70/0.92      inference('sup+', [status(thm)], ['2', '25'])).
% 0.70/0.92  thf('41', plain,
% 0.70/0.92      (![X4 : $i, X5 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ X4)
% 0.70/0.92          | ~ (v1_relat_1 @ X5)
% 0.70/0.92          | (v1_relat_1 @ (k5_relat_1 @ X4 @ X5)))),
% 0.70/0.92      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.70/0.92  thf('42', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         ((v1_relat_1 @ k1_xboole_0)
% 0.70/0.92          | ~ (v1_relat_1 @ X0)
% 0.70/0.92          | ~ (v1_xboole_0 @ X1)
% 0.70/0.92          | ~ (v1_relat_1 @ X0)
% 0.70/0.92          | ~ (v1_relat_1 @ X1))),
% 0.70/0.92      inference('sup+', [status(thm)], ['40', '41'])).
% 0.70/0.92  thf('43', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ X1)
% 0.70/0.92          | ~ (v1_xboole_0 @ X1)
% 0.70/0.92          | ~ (v1_relat_1 @ X0)
% 0.70/0.92          | (v1_relat_1 @ k1_xboole_0))),
% 0.70/0.92      inference('simplify', [status(thm)], ['42'])).
% 0.70/0.92  thf('44', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         (~ (v1_xboole_0 @ X0)
% 0.70/0.92          | (v1_relat_1 @ k1_xboole_0)
% 0.70/0.92          | ~ (v1_relat_1 @ X1)
% 0.70/0.92          | ~ (v1_xboole_0 @ X0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['39', '43'])).
% 0.70/0.92  thf('45', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ X1)
% 0.70/0.92          | (v1_relat_1 @ k1_xboole_0)
% 0.70/0.92          | ~ (v1_xboole_0 @ X0))),
% 0.70/0.92      inference('simplify', [status(thm)], ['44'])).
% 0.70/0.92  thf('46', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ X0)
% 0.70/0.92          | (v1_relat_1 @ k1_xboole_0)
% 0.70/0.92          | ~ (v1_relat_1 @ X1))),
% 0.70/0.92      inference('sup-', [status(thm)], ['38', '45'])).
% 0.70/0.92  thf('47', plain,
% 0.70/0.92      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.70/0.92      inference('condensation', [status(thm)], ['46'])).
% 0.70/0.92  thf('48', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.70/0.92      inference('sup-', [status(thm)], ['37', '47'])).
% 0.70/0.92  thf('49', plain, ((v1_xboole_0 @ (k4_relat_1 @ k1_xboole_0))),
% 0.70/0.92      inference('demod', [status(thm)], ['35', '36', '48'])).
% 0.70/0.92  thf('50', plain,
% 0.70/0.92      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.92      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.70/0.92  thf('51', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['49', '50'])).
% 0.70/0.92  thf(t54_relat_1, axiom,
% 0.70/0.92    (![A:$i]:
% 0.70/0.92     ( ( v1_relat_1 @ A ) =>
% 0.70/0.92       ( ![B:$i]:
% 0.70/0.92         ( ( v1_relat_1 @ B ) =>
% 0.70/0.92           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.70/0.92             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 0.70/0.92  thf('52', plain,
% 0.70/0.92      (![X11 : $i, X12 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ X11)
% 0.70/0.92          | ((k4_relat_1 @ (k5_relat_1 @ X12 @ X11))
% 0.70/0.92              = (k5_relat_1 @ (k4_relat_1 @ X11) @ (k4_relat_1 @ X12)))
% 0.70/0.92          | ~ (v1_relat_1 @ X12))),
% 0.70/0.92      inference('cnf', [status(esa)], [t54_relat_1])).
% 0.70/0.92  thf('53', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.70/0.92            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 0.70/0.92          | ~ (v1_relat_1 @ X0)
% 0.70/0.92          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['51', '52'])).
% 0.70/0.92  thf('54', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.70/0.92      inference('sup-', [status(thm)], ['37', '47'])).
% 0.70/0.92  thf('55', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.70/0.92            = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 0.70/0.92          | ~ (v1_relat_1 @ X0))),
% 0.70/0.92      inference('demod', [status(thm)], ['53', '54'])).
% 0.70/0.92  thf('56', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.70/0.92          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.70/0.92          | ~ (v1_relat_1 @ X0)
% 0.70/0.92          | ~ (v1_relat_1 @ X0))),
% 0.70/0.92      inference('sup+', [status(thm)], ['27', '55'])).
% 0.70/0.92  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.70/0.92  thf('58', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 0.70/0.92          | ~ (v1_relat_1 @ X0)
% 0.70/0.92          | ~ (v1_relat_1 @ X0))),
% 0.70/0.92      inference('demod', [status(thm)], ['56', '57'])).
% 0.70/0.92  thf('59', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ X0)
% 0.70/0.92          | ((k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.70/0.92      inference('simplify', [status(thm)], ['58'])).
% 0.70/0.92  thf(involutiveness_k4_relat_1, axiom,
% 0.70/0.92    (![A:$i]:
% 0.70/0.92     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 0.70/0.92  thf('60', plain,
% 0.70/0.92      (![X7 : $i]:
% 0.70/0.92         (((k4_relat_1 @ (k4_relat_1 @ X7)) = (X7)) | ~ (v1_relat_1 @ X7))),
% 0.70/0.92      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 0.70/0.92  thf('61', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.70/0.92          | ~ (v1_relat_1 @ X0)
% 0.70/0.92          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.70/0.92      inference('sup+', [status(thm)], ['59', '60'])).
% 0.70/0.92  thf('62', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['49', '50'])).
% 0.70/0.92  thf('63', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.70/0.92          | ~ (v1_relat_1 @ X0)
% 0.70/0.92          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.70/0.92      inference('demod', [status(thm)], ['61', '62'])).
% 0.70/0.92  thf('64', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ k1_xboole_0)
% 0.70/0.92          | ~ (v1_relat_1 @ X0)
% 0.70/0.92          | ~ (v1_relat_1 @ X0)
% 0.70/0.92          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.70/0.92      inference('sup-', [status(thm)], ['0', '63'])).
% 0.70/0.92  thf('65', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.70/0.92      inference('sup-', [status(thm)], ['37', '47'])).
% 0.70/0.92  thf('66', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ X0)
% 0.70/0.92          | ~ (v1_relat_1 @ X0)
% 0.70/0.92          | ((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.70/0.92      inference('demod', [status(thm)], ['64', '65'])).
% 0.70/0.92  thf('67', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (((k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.70/0.92          | ~ (v1_relat_1 @ X0))),
% 0.70/0.92      inference('simplify', [status(thm)], ['66'])).
% 0.70/0.92  thf('68', plain,
% 0.70/0.92      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.92      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.70/0.92  thf('69', plain,
% 0.70/0.92      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.70/0.92        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('70', plain,
% 0.70/0.92      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.70/0.92         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.70/0.92      inference('split', [status(esa)], ['69'])).
% 0.70/0.92  thf('71', plain,
% 0.70/0.92      ((![X0 : $i]:
% 0.70/0.92          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.70/0.92         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.70/0.92      inference('sup-', [status(thm)], ['68', '70'])).
% 0.70/0.92  thf('72', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.70/0.92      inference('demod', [status(thm)], ['21', '22'])).
% 0.70/0.92  thf('73', plain,
% 0.70/0.92      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.92      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.70/0.92  thf('74', plain,
% 0.70/0.92      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.92      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.70/0.92  thf('75', plain,
% 0.70/0.92      (![X0 : $i, X1 : $i]:
% 0.70/0.92         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.70/0.92      inference('sup+', [status(thm)], ['73', '74'])).
% 0.70/0.92  thf('76', plain,
% 0.70/0.92      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.70/0.92         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.70/0.92      inference('split', [status(esa)], ['69'])).
% 0.70/0.92  thf('77', plain,
% 0.70/0.92      ((![X0 : $i]:
% 0.70/0.92          (((X0) != (k1_xboole_0))
% 0.70/0.92           | ~ (v1_xboole_0 @ X0)
% 0.70/0.92           | ~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A))))
% 0.70/0.92         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.70/0.92      inference('sup-', [status(thm)], ['75', '76'])).
% 0.70/0.92  thf('78', plain,
% 0.70/0.92      (((~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A))
% 0.70/0.92         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.70/0.92         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.70/0.92      inference('simplify', [status(thm)], ['77'])).
% 0.70/0.92  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.70/0.92  thf('80', plain,
% 0.70/0.92      ((~ (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ sk_A)))
% 0.70/0.92         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.70/0.92      inference('simplify_reflect+', [status(thm)], ['78', '79'])).
% 0.70/0.92  thf('81', plain,
% 0.70/0.92      ((~ (v1_relat_1 @ sk_A))
% 0.70/0.92         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.70/0.92      inference('sup-', [status(thm)], ['72', '80'])).
% 0.70/0.92  thf('82', plain, ((v1_relat_1 @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('83', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.70/0.92      inference('demod', [status(thm)], ['81', '82'])).
% 0.70/0.92  thf('84', plain,
% 0.70/0.92      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.70/0.92       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.70/0.92      inference('split', [status(esa)], ['69'])).
% 0.70/0.92  thf('85', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.70/0.92      inference('sat_resolution*', [status(thm)], ['83', '84'])).
% 0.70/0.92  thf('86', plain,
% 0.70/0.92      (![X0 : $i]:
% 0.70/0.92         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.70/0.92      inference('simpl_trail', [status(thm)], ['71', '85'])).
% 0.70/0.92  thf('87', plain,
% 0.70/0.92      ((((k1_xboole_0) != (k1_xboole_0))
% 0.70/0.92        | ~ (v1_relat_1 @ sk_A)
% 0.70/0.92        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.70/0.92      inference('sup-', [status(thm)], ['67', '86'])).
% 0.70/0.92  thf('88', plain, ((v1_relat_1 @ sk_A)),
% 0.70/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.92  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.70/0.92  thf('90', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.70/0.92      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.70/0.92  thf('91', plain, ($false), inference('simplify', [status(thm)], ['90'])).
% 0.70/0.92  
% 0.70/0.92  % SZS output end Refutation
% 0.70/0.92  
% 0.70/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
