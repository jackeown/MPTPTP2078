%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5m78V5u68z

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:37 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 297 expanded)
%              Number of leaves         :   21 (  98 expanded)
%              Depth                    :   31
%              Number of atoms          :  718 (1979 expanded)
%              Number of equality atoms :   52 ( 138 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
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
    ! [X4: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('6',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('7',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) ) @ ( k1_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
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

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('14',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X2 )
        = X1 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
        = ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('16',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
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
    ! [X4: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','31'])).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['38'])).

thf('40',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','40'])).

thf('42',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X2 )
        = X1 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('46',plain,(
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','49'])).

thf('51',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','39'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('58',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('60',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,
    ( ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('63',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['61','62'])).

thf('64',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('66',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('70',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('71',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('75',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['67','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('79',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['58'])).

thf('81',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['66','81'])).

thf('83',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['53','82'])).

thf('84',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['83','84','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5m78V5u68z
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:21:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.76  % Solved by: fo/fo7.sh
% 0.19/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.76  % done 652 iterations in 0.319s
% 0.19/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.76  % SZS output start Refutation
% 0.19/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.76  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.76  thf(dt_k5_relat_1, axiom,
% 0.19/0.76    (![A:$i,B:$i]:
% 0.19/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.19/0.76       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.19/0.76  thf('0', plain,
% 0.19/0.76      (![X5 : $i, X6 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X5)
% 0.19/0.76          | ~ (v1_relat_1 @ X6)
% 0.19/0.76          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.19/0.76      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.19/0.76  thf(t60_relat_1, axiom,
% 0.19/0.76    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.19/0.76     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.76  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.76      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.76  thf(t45_relat_1, axiom,
% 0.19/0.76    (![A:$i]:
% 0.19/0.76     ( ( v1_relat_1 @ A ) =>
% 0.19/0.76       ( ![B:$i]:
% 0.19/0.76         ( ( v1_relat_1 @ B ) =>
% 0.19/0.76           ( r1_tarski @
% 0.19/0.76             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.19/0.76  thf('2', plain,
% 0.19/0.76      (![X11 : $i, X12 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X11)
% 0.19/0.76          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X12 @ X11)) @ 
% 0.19/0.76             (k2_relat_1 @ X11))
% 0.19/0.76          | ~ (v1_relat_1 @ X12))),
% 0.19/0.76      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.19/0.76  thf('3', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.19/0.76           k1_xboole_0)
% 0.19/0.76          | ~ (v1_relat_1 @ X0)
% 0.19/0.76          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.19/0.76      inference('sup+', [status(thm)], ['1', '2'])).
% 0.19/0.76  thf(t62_relat_1, conjecture,
% 0.19/0.76    (![A:$i]:
% 0.19/0.76     ( ( v1_relat_1 @ A ) =>
% 0.19/0.76       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.19/0.76         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.76    (~( ![A:$i]:
% 0.19/0.76        ( ( v1_relat_1 @ A ) =>
% 0.19/0.76          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.19/0.76            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.19/0.76    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.19/0.76  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.76  thf(cc1_relat_1, axiom,
% 0.19/0.76    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.19/0.76  thf('5', plain, (![X4 : $i]: ((v1_relat_1 @ X4) | ~ (v1_xboole_0 @ X4))),
% 0.19/0.76      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.19/0.76  thf('6', plain,
% 0.19/0.76      (![X5 : $i, X6 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X5)
% 0.19/0.76          | ~ (v1_relat_1 @ X6)
% 0.19/0.76          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.19/0.76      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.19/0.76  thf('7', plain, (![X4 : $i]: ((v1_relat_1 @ X4) | ~ (v1_xboole_0 @ X4))),
% 0.19/0.76      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.19/0.76  thf('8', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.76      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.19/0.76  thf(t44_relat_1, axiom,
% 0.19/0.76    (![A:$i]:
% 0.19/0.76     ( ( v1_relat_1 @ A ) =>
% 0.19/0.76       ( ![B:$i]:
% 0.19/0.76         ( ( v1_relat_1 @ B ) =>
% 0.19/0.76           ( r1_tarski @
% 0.19/0.76             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.19/0.76  thf('9', plain,
% 0.19/0.76      (![X9 : $i, X10 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X9)
% 0.19/0.76          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X10 @ X9)) @ 
% 0.19/0.76             (k1_relat_1 @ X10))
% 0.19/0.76          | ~ (v1_relat_1 @ X10))),
% 0.19/0.76      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.19/0.76  thf('10', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.19/0.76           k1_xboole_0)
% 0.19/0.76          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.76          | ~ (v1_relat_1 @ X0))),
% 0.19/0.76      inference('sup+', [status(thm)], ['8', '9'])).
% 0.19/0.76  thf('11', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.76          | ~ (v1_relat_1 @ X0)
% 0.19/0.76          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.19/0.76             k1_xboole_0))),
% 0.19/0.76      inference('sup-', [status(thm)], ['7', '10'])).
% 0.19/0.76  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.76  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.76  thf('13', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X0)
% 0.19/0.76          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.19/0.76             k1_xboole_0))),
% 0.19/0.76      inference('demod', [status(thm)], ['11', '12'])).
% 0.19/0.76  thf(t28_xboole_1, axiom,
% 0.19/0.76    (![A:$i,B:$i]:
% 0.19/0.76     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.19/0.76  thf('14', plain,
% 0.19/0.76      (![X1 : $i, X2 : $i]:
% 0.19/0.76         (((k3_xboole_0 @ X1 @ X2) = (X1)) | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.76      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.76  thf('15', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X0)
% 0.19/0.76          | ((k3_xboole_0 @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.19/0.76              k1_xboole_0) = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 0.19/0.76      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.76  thf(t2_boole, axiom,
% 0.19/0.76    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.19/0.76  thf('16', plain,
% 0.19/0.76      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.76      inference('cnf', [status(esa)], [t2_boole])).
% 0.19/0.76  thf('17', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X0)
% 0.19/0.76          | ((k1_xboole_0) = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 0.19/0.76      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.76  thf(fc8_relat_1, axiom,
% 0.19/0.76    (![A:$i]:
% 0.19/0.76     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.19/0.76       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.19/0.76  thf('18', plain,
% 0.19/0.76      (![X7 : $i]:
% 0.19/0.76         (~ (v1_xboole_0 @ (k1_relat_1 @ X7))
% 0.19/0.76          | ~ (v1_relat_1 @ X7)
% 0.19/0.76          | (v1_xboole_0 @ X7))),
% 0.19/0.76      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.19/0.76  thf('19', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.76          | ~ (v1_relat_1 @ X0)
% 0.19/0.76          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.19/0.76          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.19/0.76      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.76  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.76  thf('21', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X0)
% 0.19/0.76          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.19/0.76          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.19/0.76      inference('demod', [status(thm)], ['19', '20'])).
% 0.19/0.76  thf('22', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X0)
% 0.19/0.76          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.76          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.19/0.76          | ~ (v1_relat_1 @ X0))),
% 0.19/0.76      inference('sup-', [status(thm)], ['6', '21'])).
% 0.19/0.76  thf('23', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.19/0.76          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.76          | ~ (v1_relat_1 @ X0))),
% 0.19/0.76      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.76  thf('24', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.76          | ~ (v1_relat_1 @ X0)
% 0.19/0.76          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.19/0.76      inference('sup-', [status(thm)], ['5', '23'])).
% 0.19/0.76  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.76  thf('26', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.19/0.76      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.76  thf('27', plain, (![X4 : $i]: ((v1_relat_1 @ X4) | ~ (v1_xboole_0 @ X4))),
% 0.19/0.76      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.19/0.76  thf(l13_xboole_0, axiom,
% 0.19/0.76    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.76  thf('28', plain,
% 0.19/0.76      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.76      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.76  thf('29', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.19/0.76      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.76  thf('30', plain,
% 0.19/0.76      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.76      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.76  thf('31', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X0)
% 0.19/0.76          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.19/0.76      inference('sup-', [status(thm)], ['29', '30'])).
% 0.19/0.76  thf('32', plain,
% 0.19/0.76      (![X0 : $i, X1 : $i]:
% 0.19/0.76         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.19/0.76          | ~ (v1_xboole_0 @ X0)
% 0.19/0.76          | ~ (v1_relat_1 @ X1))),
% 0.19/0.76      inference('sup+', [status(thm)], ['28', '31'])).
% 0.19/0.76  thf('33', plain,
% 0.19/0.76      (![X5 : $i, X6 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X5)
% 0.19/0.76          | ~ (v1_relat_1 @ X6)
% 0.19/0.76          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.19/0.76      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.19/0.76  thf('34', plain,
% 0.19/0.76      (![X0 : $i, X1 : $i]:
% 0.19/0.76         ((v1_relat_1 @ k1_xboole_0)
% 0.19/0.76          | ~ (v1_relat_1 @ X0)
% 0.19/0.76          | ~ (v1_xboole_0 @ X1)
% 0.19/0.76          | ~ (v1_relat_1 @ X0)
% 0.19/0.76          | ~ (v1_relat_1 @ X1))),
% 0.19/0.76      inference('sup+', [status(thm)], ['32', '33'])).
% 0.19/0.76  thf('35', plain,
% 0.19/0.76      (![X0 : $i, X1 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X1)
% 0.19/0.76          | ~ (v1_xboole_0 @ X1)
% 0.19/0.76          | ~ (v1_relat_1 @ X0)
% 0.19/0.76          | (v1_relat_1 @ k1_xboole_0))),
% 0.19/0.76      inference('simplify', [status(thm)], ['34'])).
% 0.19/0.76  thf('36', plain,
% 0.19/0.76      (![X0 : $i, X1 : $i]:
% 0.19/0.76         (~ (v1_xboole_0 @ X0)
% 0.19/0.76          | (v1_relat_1 @ k1_xboole_0)
% 0.19/0.76          | ~ (v1_relat_1 @ X1)
% 0.19/0.76          | ~ (v1_xboole_0 @ X0))),
% 0.19/0.76      inference('sup-', [status(thm)], ['27', '35'])).
% 0.19/0.76  thf('37', plain,
% 0.19/0.76      (![X0 : $i, X1 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X1)
% 0.19/0.76          | (v1_relat_1 @ k1_xboole_0)
% 0.19/0.76          | ~ (v1_xboole_0 @ X0))),
% 0.19/0.76      inference('simplify', [status(thm)], ['36'])).
% 0.19/0.76  thf('38', plain,
% 0.19/0.76      (![X0 : $i, X1 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X0)
% 0.19/0.76          | (v1_relat_1 @ k1_xboole_0)
% 0.19/0.76          | ~ (v1_relat_1 @ X1))),
% 0.19/0.76      inference('sup-', [status(thm)], ['26', '37'])).
% 0.19/0.76  thf('39', plain,
% 0.19/0.76      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.19/0.76      inference('condensation', [status(thm)], ['38'])).
% 0.19/0.76  thf('40', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.76      inference('sup-', [status(thm)], ['4', '39'])).
% 0.19/0.76  thf('41', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.19/0.76           k1_xboole_0)
% 0.19/0.76          | ~ (v1_relat_1 @ X0))),
% 0.19/0.76      inference('demod', [status(thm)], ['3', '40'])).
% 0.19/0.76  thf('42', plain,
% 0.19/0.76      (![X1 : $i, X2 : $i]:
% 0.19/0.76         (((k3_xboole_0 @ X1 @ X2) = (X1)) | ~ (r1_tarski @ X1 @ X2))),
% 0.19/0.76      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.19/0.76  thf('43', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X0)
% 0.19/0.76          | ((k3_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.19/0.76              k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 0.19/0.76      inference('sup-', [status(thm)], ['41', '42'])).
% 0.19/0.76  thf('44', plain,
% 0.19/0.76      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.76      inference('cnf', [status(esa)], [t2_boole])).
% 0.19/0.76  thf('45', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X0)
% 0.19/0.76          | ((k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 0.19/0.76      inference('demod', [status(thm)], ['43', '44'])).
% 0.19/0.76  thf(fc9_relat_1, axiom,
% 0.19/0.76    (![A:$i]:
% 0.19/0.76     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.19/0.76       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.19/0.76  thf('46', plain,
% 0.19/0.76      (![X8 : $i]:
% 0.19/0.76         (~ (v1_xboole_0 @ (k2_relat_1 @ X8))
% 0.19/0.76          | ~ (v1_relat_1 @ X8)
% 0.19/0.76          | (v1_xboole_0 @ X8))),
% 0.19/0.76      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.19/0.76  thf('47', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.76          | ~ (v1_relat_1 @ X0)
% 0.19/0.76          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.19/0.76          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.19/0.76      inference('sup-', [status(thm)], ['45', '46'])).
% 0.19/0.76  thf('48', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.76  thf('49', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X0)
% 0.19/0.76          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.19/0.76          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.19/0.76      inference('demod', [status(thm)], ['47', '48'])).
% 0.19/0.76  thf('50', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ k1_xboole_0)
% 0.19/0.76          | ~ (v1_relat_1 @ X0)
% 0.19/0.76          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.19/0.76          | ~ (v1_relat_1 @ X0))),
% 0.19/0.76      inference('sup-', [status(thm)], ['0', '49'])).
% 0.19/0.76  thf('51', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.19/0.76      inference('sup-', [status(thm)], ['4', '39'])).
% 0.19/0.76  thf('52', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X0)
% 0.19/0.76          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.19/0.76          | ~ (v1_relat_1 @ X0))),
% 0.19/0.76      inference('demod', [status(thm)], ['50', '51'])).
% 0.19/0.76  thf('53', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.19/0.76      inference('simplify', [status(thm)], ['52'])).
% 0.19/0.76  thf('54', plain,
% 0.19/0.76      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.76      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.76  thf('55', plain,
% 0.19/0.76      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.76      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.76  thf('56', plain,
% 0.19/0.76      (![X0 : $i, X1 : $i]:
% 0.19/0.76         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.76      inference('sup+', [status(thm)], ['54', '55'])).
% 0.19/0.76  thf('57', plain,
% 0.19/0.76      (![X0 : $i, X1 : $i]:
% 0.19/0.76         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.76      inference('sup+', [status(thm)], ['54', '55'])).
% 0.19/0.76  thf('58', plain,
% 0.19/0.76      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.19/0.76        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.19/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.76  thf('59', plain,
% 0.19/0.76      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.19/0.76         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.19/0.76      inference('split', [status(esa)], ['58'])).
% 0.19/0.76  thf('60', plain,
% 0.19/0.76      ((![X0 : $i]:
% 0.19/0.76          (((X0) != (k1_xboole_0))
% 0.19/0.76           | ~ (v1_xboole_0 @ X0)
% 0.19/0.76           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))))
% 0.19/0.76         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.19/0.76      inference('sup-', [status(thm)], ['57', '59'])).
% 0.19/0.76  thf('61', plain,
% 0.19/0.76      (((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 0.19/0.76         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.19/0.76         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.19/0.76      inference('simplify', [status(thm)], ['60'])).
% 0.19/0.76  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.76  thf('63', plain,
% 0.19/0.76      ((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0)))
% 0.19/0.76         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.19/0.76      inference('simplify_reflect+', [status(thm)], ['61', '62'])).
% 0.19/0.76  thf('64', plain,
% 0.19/0.76      ((![X0 : $i]:
% 0.19/0.76          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0))
% 0.19/0.76           | ~ (v1_xboole_0 @ X0)
% 0.19/0.76           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.19/0.76         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.19/0.76      inference('sup-', [status(thm)], ['56', '63'])).
% 0.19/0.76  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.76  thf('66', plain,
% 0.19/0.76      ((![X0 : $i]:
% 0.19/0.76          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0)))
% 0.19/0.76         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.19/0.76      inference('demod', [status(thm)], ['64', '65'])).
% 0.19/0.76  thf('67', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.19/0.76      inference('demod', [status(thm)], ['24', '25'])).
% 0.19/0.76  thf('68', plain,
% 0.19/0.76      (![X0 : $i, X1 : $i]:
% 0.19/0.76         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.76      inference('sup+', [status(thm)], ['54', '55'])).
% 0.19/0.76  thf('69', plain,
% 0.19/0.76      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.76      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.19/0.76  thf('70', plain,
% 0.19/0.76      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.19/0.76         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.76      inference('split', [status(esa)], ['58'])).
% 0.19/0.76  thf('71', plain,
% 0.19/0.76      ((![X0 : $i]:
% 0.19/0.76          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.19/0.76         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.76      inference('sup-', [status(thm)], ['69', '70'])).
% 0.19/0.76  thf('72', plain,
% 0.19/0.76      ((![X0 : $i, X1 : $i]:
% 0.19/0.76          (((X0) != (k1_xboole_0))
% 0.19/0.76           | ~ (v1_xboole_0 @ X0)
% 0.19/0.76           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.19/0.76           | ~ (v1_xboole_0 @ X1)))
% 0.19/0.76         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.76      inference('sup-', [status(thm)], ['68', '71'])).
% 0.19/0.76  thf('73', plain,
% 0.19/0.76      ((![X1 : $i]:
% 0.19/0.76          (~ (v1_xboole_0 @ X1)
% 0.19/0.76           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.19/0.76           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.19/0.76         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.76      inference('simplify', [status(thm)], ['72'])).
% 0.19/0.76  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.76  thf('75', plain,
% 0.19/0.76      ((![X1 : $i]:
% 0.19/0.76          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.19/0.76         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.76      inference('simplify_reflect+', [status(thm)], ['73', '74'])).
% 0.19/0.76  thf('76', plain,
% 0.19/0.76      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.19/0.76         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.19/0.76      inference('sup-', [status(thm)], ['67', '75'])).
% 0.19/0.76  thf('77', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.76  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.76  thf('79', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.19/0.76      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.19/0.76  thf('80', plain,
% 0.19/0.76      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.19/0.76       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.19/0.76      inference('split', [status(esa)], ['58'])).
% 0.19/0.76  thf('81', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.19/0.76      inference('sat_resolution*', [status(thm)], ['79', '80'])).
% 0.19/0.76  thf('82', plain,
% 0.19/0.76      (![X0 : $i]:
% 0.19/0.76         (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.76      inference('simpl_trail', [status(thm)], ['66', '81'])).
% 0.19/0.76  thf('83', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.19/0.76      inference('sup-', [status(thm)], ['53', '82'])).
% 0.19/0.76  thf('84', plain, ((v1_relat_1 @ sk_A)),
% 0.19/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.76  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.76  thf('86', plain, ($false),
% 0.19/0.76      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.19/0.76  
% 0.19/0.76  % SZS output end Refutation
% 0.19/0.76  
% 0.19/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
