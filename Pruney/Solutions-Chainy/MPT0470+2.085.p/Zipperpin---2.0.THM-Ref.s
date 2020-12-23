%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Eko5wOzArs

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:38 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 303 expanded)
%              Number of leaves         :   21 ( 100 expanded)
%              Depth                    :   31
%              Number of atoms          :  719 (2005 expanded)
%              Number of equality atoms :   51 ( 134 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) ) ) ),
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
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
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
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('7',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
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
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X11 @ X10 ) ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
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
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
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
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
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
    ! [X8: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 )
      | ( v1_xboole_0 @ X8 ) ) ),
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
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['40'])).

thf('42',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = X0 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k3_xboole_0 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['45','46'])).

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
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','51'])).

thf('53',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','41'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('57',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

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
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) )
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
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

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
    inference('sup-',[status(thm)],['55','82'])).

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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Eko5wOzArs
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:33:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.54/0.76  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.54/0.76  % Solved by: fo/fo7.sh
% 0.54/0.76  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.76  % done 575 iterations in 0.313s
% 0.54/0.76  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.54/0.76  % SZS output start Refutation
% 0.54/0.76  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.76  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.54/0.76  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.76  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.76  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.76  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.76  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.76  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.76  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.54/0.76  thf(dt_k5_relat_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.54/0.76       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.54/0.76  thf('0', plain,
% 0.54/0.76      (![X6 : $i, X7 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X6)
% 0.54/0.76          | ~ (v1_relat_1 @ X7)
% 0.54/0.76          | (v1_relat_1 @ (k5_relat_1 @ X6 @ X7)))),
% 0.54/0.76      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.54/0.76  thf(t60_relat_1, axiom,
% 0.54/0.76    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.54/0.76     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.54/0.76  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.76      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.54/0.76  thf(t45_relat_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( v1_relat_1 @ A ) =>
% 0.54/0.76       ( ![B:$i]:
% 0.54/0.76         ( ( v1_relat_1 @ B ) =>
% 0.54/0.76           ( r1_tarski @
% 0.54/0.76             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.54/0.76  thf('2', plain,
% 0.54/0.76      (![X12 : $i, X13 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X12)
% 0.54/0.76          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X13 @ X12)) @ 
% 0.54/0.76             (k2_relat_1 @ X12))
% 0.54/0.76          | ~ (v1_relat_1 @ X13))),
% 0.54/0.76      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.54/0.76  thf('3', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.54/0.76           k1_xboole_0)
% 0.54/0.76          | ~ (v1_relat_1 @ X0)
% 0.54/0.76          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.54/0.76      inference('sup+', [status(thm)], ['1', '2'])).
% 0.54/0.76  thf(t62_relat_1, conjecture,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( v1_relat_1 @ A ) =>
% 0.54/0.76       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.54/0.76         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.54/0.76  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.76    (~( ![A:$i]:
% 0.54/0.76        ( ( v1_relat_1 @ A ) =>
% 0.54/0.76          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.54/0.76            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.54/0.76    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.54/0.76  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf(cc1_relat_1, axiom,
% 0.54/0.76    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.54/0.76  thf('5', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.54/0.76      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.54/0.76  thf('6', plain,
% 0.54/0.76      (![X6 : $i, X7 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X6)
% 0.54/0.76          | ~ (v1_relat_1 @ X7)
% 0.54/0.76          | (v1_relat_1 @ (k5_relat_1 @ X6 @ X7)))),
% 0.54/0.76      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.54/0.76  thf('7', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.54/0.76      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.54/0.76  thf('8', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.76      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.54/0.76  thf(t44_relat_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( v1_relat_1 @ A ) =>
% 0.54/0.76       ( ![B:$i]:
% 0.54/0.76         ( ( v1_relat_1 @ B ) =>
% 0.54/0.76           ( r1_tarski @
% 0.54/0.76             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.54/0.76  thf('9', plain,
% 0.54/0.76      (![X10 : $i, X11 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X10)
% 0.54/0.76          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X11 @ X10)) @ 
% 0.54/0.76             (k1_relat_1 @ X11))
% 0.54/0.76          | ~ (v1_relat_1 @ X11))),
% 0.54/0.76      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.54/0.76  thf('10', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.54/0.76           k1_xboole_0)
% 0.54/0.76          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.54/0.76          | ~ (v1_relat_1 @ X0))),
% 0.54/0.76      inference('sup+', [status(thm)], ['8', '9'])).
% 0.54/0.76  thf('11', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.54/0.76          | ~ (v1_relat_1 @ X0)
% 0.54/0.76          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.54/0.76             k1_xboole_0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['7', '10'])).
% 0.54/0.76  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.54/0.76  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.76  thf('13', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X0)
% 0.54/0.76          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.54/0.76             k1_xboole_0))),
% 0.54/0.76      inference('demod', [status(thm)], ['11', '12'])).
% 0.54/0.76  thf(t28_xboole_1, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.54/0.76  thf('14', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.54/0.76      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.54/0.76  thf('15', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X0)
% 0.54/0.76          | ((k3_xboole_0 @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.54/0.76              k1_xboole_0) = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['13', '14'])).
% 0.54/0.76  thf(t2_boole, axiom,
% 0.54/0.76    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.54/0.76  thf('16', plain,
% 0.54/0.76      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.76      inference('cnf', [status(esa)], [t2_boole])).
% 0.54/0.76  thf('17', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X0)
% 0.54/0.76          | ((k1_xboole_0) = (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))))),
% 0.54/0.76      inference('demod', [status(thm)], ['15', '16'])).
% 0.54/0.76  thf(fc8_relat_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.54/0.76       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.54/0.76  thf('18', plain,
% 0.54/0.76      (![X8 : $i]:
% 0.54/0.76         (~ (v1_xboole_0 @ (k1_relat_1 @ X8))
% 0.54/0.76          | ~ (v1_relat_1 @ X8)
% 0.54/0.76          | (v1_xboole_0 @ X8))),
% 0.54/0.76      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.54/0.76  thf('19', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.54/0.76          | ~ (v1_relat_1 @ X0)
% 0.54/0.76          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.54/0.76          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['17', '18'])).
% 0.54/0.76  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.76  thf('21', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X0)
% 0.54/0.76          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.54/0.76          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.54/0.76      inference('demod', [status(thm)], ['19', '20'])).
% 0.54/0.76  thf('22', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X0)
% 0.54/0.76          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.54/0.76          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.54/0.76          | ~ (v1_relat_1 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['6', '21'])).
% 0.54/0.76  thf('23', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.54/0.76          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.54/0.76          | ~ (v1_relat_1 @ X0))),
% 0.54/0.76      inference('simplify', [status(thm)], ['22'])).
% 0.54/0.76  thf('24', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.54/0.76          | ~ (v1_relat_1 @ X0)
% 0.54/0.76          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['5', '23'])).
% 0.54/0.76  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.76  thf('26', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.54/0.76      inference('demod', [status(thm)], ['24', '25'])).
% 0.54/0.76  thf('27', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.54/0.76      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.54/0.76  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.76  thf(t8_boole, axiom,
% 0.54/0.76    (![A:$i,B:$i]:
% 0.54/0.76     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.54/0.76  thf('29', plain,
% 0.54/0.76      (![X3 : $i, X4 : $i]:
% 0.54/0.76         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.54/0.76      inference('cnf', [status(esa)], [t8_boole])).
% 0.54/0.76  thf('30', plain,
% 0.54/0.76      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['28', '29'])).
% 0.54/0.76  thf('31', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.54/0.76      inference('demod', [status(thm)], ['24', '25'])).
% 0.54/0.76  thf('32', plain,
% 0.54/0.76      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['28', '29'])).
% 0.54/0.76  thf('33', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X0)
% 0.54/0.76          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['31', '32'])).
% 0.54/0.76  thf('34', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         (((k1_xboole_0) = (k5_relat_1 @ X0 @ X1))
% 0.54/0.76          | ~ (v1_xboole_0 @ X0)
% 0.54/0.76          | ~ (v1_relat_1 @ X1))),
% 0.54/0.76      inference('sup+', [status(thm)], ['30', '33'])).
% 0.54/0.76  thf('35', plain,
% 0.54/0.76      (![X6 : $i, X7 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X6)
% 0.54/0.76          | ~ (v1_relat_1 @ X7)
% 0.54/0.76          | (v1_relat_1 @ (k5_relat_1 @ X6 @ X7)))),
% 0.54/0.76      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.54/0.76  thf('36', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         ((v1_relat_1 @ k1_xboole_0)
% 0.54/0.76          | ~ (v1_relat_1 @ X0)
% 0.54/0.76          | ~ (v1_xboole_0 @ X1)
% 0.54/0.76          | ~ (v1_relat_1 @ X0)
% 0.54/0.76          | ~ (v1_relat_1 @ X1))),
% 0.54/0.76      inference('sup+', [status(thm)], ['34', '35'])).
% 0.54/0.76  thf('37', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X1)
% 0.54/0.76          | ~ (v1_xboole_0 @ X1)
% 0.54/0.76          | ~ (v1_relat_1 @ X0)
% 0.54/0.76          | (v1_relat_1 @ k1_xboole_0))),
% 0.54/0.76      inference('simplify', [status(thm)], ['36'])).
% 0.54/0.76  thf('38', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         (~ (v1_xboole_0 @ X0)
% 0.54/0.76          | (v1_relat_1 @ k1_xboole_0)
% 0.54/0.76          | ~ (v1_relat_1 @ X1)
% 0.54/0.76          | ~ (v1_xboole_0 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['27', '37'])).
% 0.54/0.76  thf('39', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X1)
% 0.54/0.76          | (v1_relat_1 @ k1_xboole_0)
% 0.54/0.76          | ~ (v1_xboole_0 @ X0))),
% 0.54/0.76      inference('simplify', [status(thm)], ['38'])).
% 0.54/0.76  thf('40', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X0)
% 0.54/0.76          | (v1_relat_1 @ k1_xboole_0)
% 0.54/0.76          | ~ (v1_relat_1 @ X1))),
% 0.54/0.76      inference('sup-', [status(thm)], ['26', '39'])).
% 0.54/0.76  thf('41', plain,
% 0.54/0.76      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.54/0.76      inference('condensation', [status(thm)], ['40'])).
% 0.54/0.76  thf('42', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.54/0.76      inference('sup-', [status(thm)], ['4', '41'])).
% 0.54/0.76  thf('43', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.54/0.76           k1_xboole_0)
% 0.54/0.76          | ~ (v1_relat_1 @ X0))),
% 0.54/0.76      inference('demod', [status(thm)], ['3', '42'])).
% 0.54/0.76  thf('44', plain,
% 0.54/0.76      (![X0 : $i, X1 : $i]:
% 0.54/0.76         (((k3_xboole_0 @ X0 @ X1) = (X0)) | ~ (r1_tarski @ X0 @ X1))),
% 0.54/0.76      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.54/0.76  thf('45', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X0)
% 0.54/0.76          | ((k3_xboole_0 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.54/0.76              k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['43', '44'])).
% 0.54/0.76  thf('46', plain,
% 0.54/0.76      (![X2 : $i]: ((k3_xboole_0 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.76      inference('cnf', [status(esa)], [t2_boole])).
% 0.54/0.76  thf('47', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X0)
% 0.54/0.76          | ((k1_xboole_0) = (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 0.54/0.76      inference('demod', [status(thm)], ['45', '46'])).
% 0.54/0.76  thf(fc9_relat_1, axiom,
% 0.54/0.76    (![A:$i]:
% 0.54/0.76     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.54/0.76       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 0.54/0.76  thf('48', plain,
% 0.54/0.76      (![X9 : $i]:
% 0.54/0.76         (~ (v1_xboole_0 @ (k2_relat_1 @ X9))
% 0.54/0.76          | ~ (v1_relat_1 @ X9)
% 0.54/0.76          | (v1_xboole_0 @ X9))),
% 0.54/0.76      inference('cnf', [status(esa)], [fc9_relat_1])).
% 0.54/0.76  thf('49', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.54/0.76          | ~ (v1_relat_1 @ X0)
% 0.54/0.76          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.54/0.76          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.54/0.76      inference('sup-', [status(thm)], ['47', '48'])).
% 0.54/0.76  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.76  thf('51', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X0)
% 0.54/0.76          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.54/0.76          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 0.54/0.76      inference('demod', [status(thm)], ['49', '50'])).
% 0.54/0.76  thf('52', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ k1_xboole_0)
% 0.54/0.76          | ~ (v1_relat_1 @ X0)
% 0.54/0.76          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.54/0.76          | ~ (v1_relat_1 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['0', '51'])).
% 0.54/0.76  thf('53', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.54/0.76      inference('sup-', [status(thm)], ['4', '41'])).
% 0.54/0.76  thf('54', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X0)
% 0.54/0.76          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.54/0.76          | ~ (v1_relat_1 @ X0))),
% 0.54/0.76      inference('demod', [status(thm)], ['52', '53'])).
% 0.54/0.76  thf('55', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.54/0.76      inference('simplify', [status(thm)], ['54'])).
% 0.54/0.76  thf('56', plain,
% 0.54/0.76      (![X3 : $i, X4 : $i]:
% 0.54/0.76         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.54/0.76      inference('cnf', [status(esa)], [t8_boole])).
% 0.54/0.76  thf('57', plain,
% 0.54/0.76      (![X3 : $i, X4 : $i]:
% 0.54/0.76         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.54/0.76      inference('cnf', [status(esa)], [t8_boole])).
% 0.54/0.76  thf('58', plain,
% 0.54/0.76      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.54/0.76        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('59', plain,
% 0.54/0.76      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.54/0.76         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.54/0.76      inference('split', [status(esa)], ['58'])).
% 0.54/0.76  thf('60', plain,
% 0.54/0.76      ((![X0 : $i]:
% 0.54/0.76          (((X0) != (k1_xboole_0))
% 0.54/0.76           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 0.54/0.76           | ~ (v1_xboole_0 @ X0)))
% 0.54/0.76         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['57', '59'])).
% 0.54/0.76  thf('61', plain,
% 0.54/0.76      (((~ (v1_xboole_0 @ k1_xboole_0)
% 0.54/0.76         | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))))
% 0.54/0.76         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.54/0.76      inference('simplify', [status(thm)], ['60'])).
% 0.54/0.76  thf('62', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.76  thf('63', plain,
% 0.54/0.76      ((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0)))
% 0.54/0.76         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.54/0.76      inference('simplify_reflect+', [status(thm)], ['61', '62'])).
% 0.54/0.76  thf('64', plain,
% 0.54/0.76      ((![X0 : $i]:
% 0.54/0.76          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0))
% 0.54/0.76           | ~ (v1_xboole_0 @ X0)
% 0.54/0.76           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.54/0.76         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['56', '63'])).
% 0.54/0.76  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.76  thf('66', plain,
% 0.54/0.76      ((![X0 : $i]:
% 0.54/0.76          (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0)))
% 0.54/0.76         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.54/0.76      inference('demod', [status(thm)], ['64', '65'])).
% 0.54/0.76  thf('67', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.54/0.76      inference('demod', [status(thm)], ['24', '25'])).
% 0.54/0.76  thf('68', plain,
% 0.54/0.76      (![X3 : $i, X4 : $i]:
% 0.54/0.76         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.54/0.76      inference('cnf', [status(esa)], [t8_boole])).
% 0.54/0.76  thf('69', plain,
% 0.54/0.76      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['28', '29'])).
% 0.54/0.76  thf('70', plain,
% 0.54/0.76      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.54/0.76         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.76      inference('split', [status(esa)], ['58'])).
% 0.54/0.76  thf('71', plain,
% 0.54/0.76      ((![X0 : $i]:
% 0.54/0.76          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.54/0.76         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['69', '70'])).
% 0.54/0.76  thf('72', plain,
% 0.54/0.76      ((![X0 : $i, X1 : $i]:
% 0.54/0.76          (((X0) != (k1_xboole_0))
% 0.54/0.76           | ~ (v1_xboole_0 @ X0)
% 0.54/0.76           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.54/0.76           | ~ (v1_xboole_0 @ X1)))
% 0.54/0.76         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['68', '71'])).
% 0.54/0.76  thf('73', plain,
% 0.54/0.76      ((![X1 : $i]:
% 0.54/0.76          (~ (v1_xboole_0 @ X1)
% 0.54/0.76           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.54/0.76           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.54/0.76         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.76      inference('simplify', [status(thm)], ['72'])).
% 0.54/0.76  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.76  thf('75', plain,
% 0.54/0.76      ((![X1 : $i]:
% 0.54/0.76          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.54/0.76         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.76      inference('simplify_reflect+', [status(thm)], ['73', '74'])).
% 0.54/0.76  thf('76', plain,
% 0.54/0.76      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.54/0.76         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.54/0.76      inference('sup-', [status(thm)], ['67', '75'])).
% 0.54/0.76  thf('77', plain, ((v1_relat_1 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.76  thf('79', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.54/0.76      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.54/0.76  thf('80', plain,
% 0.54/0.76      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.54/0.76       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.54/0.76      inference('split', [status(esa)], ['58'])).
% 0.54/0.76  thf('81', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.54/0.76      inference('sat_resolution*', [status(thm)], ['79', '80'])).
% 0.54/0.76  thf('82', plain,
% 0.54/0.76      (![X0 : $i]:
% 0.54/0.76         (~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.54/0.76      inference('simpl_trail', [status(thm)], ['66', '81'])).
% 0.54/0.76  thf('83', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.54/0.76      inference('sup-', [status(thm)], ['55', '82'])).
% 0.54/0.76  thf('84', plain, ((v1_relat_1 @ sk_A)),
% 0.54/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.76  thf('85', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.54/0.76      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.54/0.76  thf('86', plain, ($false),
% 0.54/0.76      inference('demod', [status(thm)], ['83', '84', '85'])).
% 0.54/0.76  
% 0.54/0.76  % SZS output end Refutation
% 0.54/0.76  
% 0.54/0.77  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
