%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UNooU9LK3d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:25:42 EST 2020

% Result     : Theorem 3.78s
% Output     : Refutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 286 expanded)
%              Number of leaves         :   18 (  96 expanded)
%              Depth                    :   17
%              Number of atoms          :  737 (1947 expanded)
%              Number of equality atoms :   84 ( 199 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t83_xboole_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_xboole_0 @ A @ B )
      <=> ( ( k4_xboole_0 @ A @ B )
          = A ) ) ),
    inference('cnf.neg',[status(esa)],[t83_xboole_1])).

thf('0',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
    | ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
    | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('5',plain,(
    ! [X25: $i,X26: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X25 @ X26 ) @ X26 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('6',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( r1_xboole_0 @ sk_A @ sk_B )
   <= ~ ( r1_xboole_0 @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('8',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_xboole_0 @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ sk_A @ sk_B )
      = sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference('sat_resolution*',[status(thm)],['3','8','9'])).

thf('11',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(simpl_trail,[status(thm)],['1','10'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('12',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('13',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t34_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ) )).

thf('14',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k4_xboole_0 @ X8 @ X7 ) @ ( k4_xboole_0 @ X8 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t34_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['12','17'])).

thf(t37_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t54_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ) )).

thf('21',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t54_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('23',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','26'])).

thf('28',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 )
      = ( k4_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['20','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('32',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('33',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t54_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t52_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('36',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ k1_xboole_0 @ X1 ) )
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X5: $i] :
      ( r1_tarski @ k1_xboole_0 @ X5 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('39',plain,(
    ! [X9: $i,X11: $i] :
      ( ( ( k4_xboole_0 @ X9 @ X11 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['37','40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('46',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['31','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','49'])).

thf('51',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('55',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ( ( k4_xboole_0 @ X9 @ X10 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t37_xboole_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference(simplify,[status(thm)],['56'])).

thf(t67_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ( r1_xboole_0 @ B @ C ) )
     => ( A = k1_xboole_0 ) ) )).

thf('58',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( r1_tarski @ X22 @ X23 )
      | ~ ( r1_tarski @ X22 @ X24 )
      | ~ ( r1_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t67_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r1_tarski @ ( k3_xboole_0 @ X0 @ X1 ) @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','59'])).

thf('61',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['11','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('63',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X19 @ ( k3_xboole_0 @ X20 @ X21 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ ( k4_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t54_xboole_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('67',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k2_xboole_0 @ ( k4_xboole_0 @ X16 @ X17 ) @ ( k3_xboole_0 @ X16 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t52_xboole_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['65','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('71',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('79',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('80',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['64','80'])).

thf('82',plain,
    ( ( k4_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['61','81'])).

thf('83',plain,(
    ! [X12: $i] :
      ( ( k4_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('84',plain,
    ( sk_A
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ sk_B )
     != sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf('86',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['3','8'])).

thf('87',plain,(
    ( k4_xboole_0 @ sk_A @ sk_B )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['85','86'])).

thf('88',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['84','87'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UNooU9LK3d
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:34:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.78/4.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.78/4.00  % Solved by: fo/fo7.sh
% 3.78/4.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.78/4.00  % done 6042 iterations in 3.552s
% 3.78/4.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.78/4.00  % SZS output start Refutation
% 3.78/4.00  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.78/4.00  thf(sk_B_type, type, sk_B: $i).
% 3.78/4.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.78/4.00  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.78/4.00  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.78/4.00  thf(sk_A_type, type, sk_A: $i).
% 3.78/4.00  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.78/4.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.78/4.00  thf(t83_xboole_1, conjecture,
% 3.78/4.00    (![A:$i,B:$i]:
% 3.78/4.00     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 3.78/4.00  thf(zf_stmt_0, negated_conjecture,
% 3.78/4.00    (~( ![A:$i,B:$i]:
% 3.78/4.00        ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ) )),
% 3.78/4.00    inference('cnf.neg', [status(esa)], [t83_xboole_1])).
% 3.78/4.00  thf('0', plain,
% 3.78/4.00      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)) | (r1_xboole_0 @ sk_A @ sk_B))),
% 3.78/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.78/4.00  thf('1', plain,
% 3.78/4.00      (((r1_xboole_0 @ sk_A @ sk_B)) <= (((r1_xboole_0 @ sk_A @ sk_B)))),
% 3.78/4.00      inference('split', [status(esa)], ['0'])).
% 3.78/4.00  thf('2', plain,
% 3.78/4.00      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)) | ~ (r1_xboole_0 @ sk_A @ sk_B))),
% 3.78/4.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.78/4.00  thf('3', plain,
% 3.78/4.00      (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))) | 
% 3.78/4.00       ~ ((r1_xboole_0 @ sk_A @ sk_B))),
% 3.78/4.00      inference('split', [status(esa)], ['2'])).
% 3.78/4.00  thf('4', plain,
% 3.78/4.00      ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))
% 3.78/4.00         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 3.78/4.00      inference('split', [status(esa)], ['0'])).
% 3.78/4.00  thf(t79_xboole_1, axiom,
% 3.78/4.00    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 3.78/4.00  thf('5', plain,
% 3.78/4.00      (![X25 : $i, X26 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X25 @ X26) @ X26)),
% 3.78/4.00      inference('cnf', [status(esa)], [t79_xboole_1])).
% 3.78/4.00  thf('6', plain,
% 3.78/4.00      (((r1_xboole_0 @ sk_A @ sk_B))
% 3.78/4.00         <= ((((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 3.78/4.00      inference('sup+', [status(thm)], ['4', '5'])).
% 3.78/4.00  thf('7', plain,
% 3.78/4.00      ((~ (r1_xboole_0 @ sk_A @ sk_B)) <= (~ ((r1_xboole_0 @ sk_A @ sk_B)))),
% 3.78/4.00      inference('split', [status(esa)], ['2'])).
% 3.78/4.00  thf('8', plain,
% 3.78/4.00      (((r1_xboole_0 @ sk_A @ sk_B)) | 
% 3.78/4.00       ~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 3.78/4.00      inference('sup-', [status(thm)], ['6', '7'])).
% 3.78/4.00  thf('9', plain,
% 3.78/4.00      (((r1_xboole_0 @ sk_A @ sk_B)) | (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 3.78/4.00      inference('split', [status(esa)], ['0'])).
% 3.78/4.00  thf('10', plain, (((r1_xboole_0 @ sk_A @ sk_B))),
% 3.78/4.00      inference('sat_resolution*', [status(thm)], ['3', '8', '9'])).
% 3.78/4.00  thf('11', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 3.78/4.00      inference('simpl_trail', [status(thm)], ['1', '10'])).
% 3.78/4.00  thf(t3_boole, axiom,
% 3.78/4.00    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.78/4.00  thf('12', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 3.78/4.00      inference('cnf', [status(esa)], [t3_boole])).
% 3.78/4.00  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.78/4.00  thf('13', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 3.78/4.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.78/4.00  thf(t34_xboole_1, axiom,
% 3.78/4.00    (![A:$i,B:$i,C:$i]:
% 3.78/4.00     ( ( r1_tarski @ A @ B ) =>
% 3.78/4.00       ( r1_tarski @ ( k4_xboole_0 @ C @ B ) @ ( k4_xboole_0 @ C @ A ) ) ))).
% 3.78/4.00  thf('14', plain,
% 3.78/4.00      (![X6 : $i, X7 : $i, X8 : $i]:
% 3.78/4.00         (~ (r1_tarski @ X6 @ X7)
% 3.78/4.00          | (r1_tarski @ (k4_xboole_0 @ X8 @ X7) @ (k4_xboole_0 @ X8 @ X6)))),
% 3.78/4.00      inference('cnf', [status(esa)], [t34_xboole_1])).
% 3.78/4.00  thf('15', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]:
% 3.78/4.00         (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ 
% 3.78/4.00          (k4_xboole_0 @ X1 @ k1_xboole_0))),
% 3.78/4.00      inference('sup-', [status(thm)], ['13', '14'])).
% 3.78/4.00  thf('16', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 3.78/4.00      inference('cnf', [status(esa)], [t3_boole])).
% 3.78/4.00  thf('17', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 3.78/4.00      inference('demod', [status(thm)], ['15', '16'])).
% 3.78/4.00  thf('18', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 3.78/4.00      inference('sup+', [status(thm)], ['12', '17'])).
% 3.78/4.00  thf(t37_xboole_1, axiom,
% 3.78/4.00    (![A:$i,B:$i]:
% 3.78/4.00     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.78/4.00  thf('19', plain,
% 3.78/4.00      (![X9 : $i, X11 : $i]:
% 3.78/4.00         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 3.78/4.00      inference('cnf', [status(esa)], [t37_xboole_1])).
% 3.78/4.00  thf('20', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.78/4.00      inference('sup-', [status(thm)], ['18', '19'])).
% 3.78/4.00  thf(t54_xboole_1, axiom,
% 3.78/4.00    (![A:$i,B:$i,C:$i]:
% 3.78/4.00     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) =
% 3.78/4.00       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k4_xboole_0 @ A @ C ) ) ))).
% 3.78/4.00  thf('21', plain,
% 3.78/4.00      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X20 @ X21))
% 3.78/4.00           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 3.78/4.00              (k4_xboole_0 @ X19 @ X21)))),
% 3.78/4.00      inference('cnf', [status(esa)], [t54_xboole_1])).
% 3.78/4.00  thf('22', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X1)),
% 3.78/4.00      inference('demod', [status(thm)], ['15', '16'])).
% 3.78/4.00  thf('23', plain,
% 3.78/4.00      (![X9 : $i, X11 : $i]:
% 3.78/4.00         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 3.78/4.00      inference('cnf', [status(esa)], [t37_xboole_1])).
% 3.78/4.00  thf('24', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 3.78/4.00      inference('sup-', [status(thm)], ['22', '23'])).
% 3.78/4.00  thf(t41_xboole_1, axiom,
% 3.78/4.00    (![A:$i,B:$i,C:$i]:
% 3.78/4.00     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 3.78/4.00       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.78/4.00  thf('25', plain,
% 3.78/4.00      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 3.78/4.00           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 3.78/4.00      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.78/4.00  thf('26', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 3.78/4.00      inference('demod', [status(thm)], ['24', '25'])).
% 3.78/4.00  thf('27', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ 
% 3.78/4.00           (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))) = (k1_xboole_0))),
% 3.78/4.00      inference('sup+', [status(thm)], ['21', '26'])).
% 3.78/4.00  thf('28', plain,
% 3.78/4.00      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ (k4_xboole_0 @ X13 @ X14) @ X15)
% 3.78/4.00           = (k4_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X15)))),
% 3.78/4.00      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.78/4.00  thf('29', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ X2 @ 
% 3.78/4.00           (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0))))
% 3.78/4.00           = (k1_xboole_0))),
% 3.78/4.00      inference('demod', [status(thm)], ['27', '28'])).
% 3.78/4.00  thf('30', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ 
% 3.78/4.00           (k2_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 3.78/4.00      inference('sup+', [status(thm)], ['20', '29'])).
% 3.78/4.00  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.78/4.00      inference('sup-', [status(thm)], ['18', '19'])).
% 3.78/4.00  thf('32', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 3.78/4.00      inference('cnf', [status(esa)], [t3_boole])).
% 3.78/4.00  thf('33', plain,
% 3.78/4.00      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X20 @ X21))
% 3.78/4.00           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 3.78/4.00              (k4_xboole_0 @ X19 @ X21)))),
% 3.78/4.00      inference('cnf', [status(esa)], [t54_xboole_1])).
% 3.78/4.00  thf('34', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ k1_xboole_0 @ X1))
% 3.78/4.00           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 3.78/4.00      inference('sup+', [status(thm)], ['32', '33'])).
% 3.78/4.00  thf('35', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 3.78/4.00      inference('cnf', [status(esa)], [t3_boole])).
% 3.78/4.00  thf(t52_xboole_1, axiom,
% 3.78/4.00    (![A:$i,B:$i,C:$i]:
% 3.78/4.00     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 3.78/4.00       ( k2_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 3.78/4.00  thf('36', plain,
% 3.78/4.00      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 3.78/4.00           = (k2_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ 
% 3.78/4.00              (k3_xboole_0 @ X16 @ X18)))),
% 3.78/4.00      inference('cnf', [status(esa)], [t52_xboole_1])).
% 3.78/4.00  thf('37', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ k1_xboole_0 @ X1))
% 3.78/4.00           = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.78/4.00      inference('sup+', [status(thm)], ['35', '36'])).
% 3.78/4.00  thf('38', plain, (![X5 : $i]: (r1_tarski @ k1_xboole_0 @ X5)),
% 3.78/4.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.78/4.00  thf('39', plain,
% 3.78/4.00      (![X9 : $i, X11 : $i]:
% 3.78/4.00         (((k4_xboole_0 @ X9 @ X11) = (k1_xboole_0)) | ~ (r1_tarski @ X9 @ X11))),
% 3.78/4.00      inference('cnf', [status(esa)], [t37_xboole_1])).
% 3.78/4.00  thf('40', plain,
% 3.78/4.00      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.78/4.00      inference('sup-', [status(thm)], ['38', '39'])).
% 3.78/4.00  thf('41', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 3.78/4.00      inference('cnf', [status(esa)], [t3_boole])).
% 3.78/4.00  thf('42', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]:
% 3.78/4.00         ((X0) = (k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 3.78/4.00      inference('demod', [status(thm)], ['37', '40', '41'])).
% 3.78/4.00  thf('43', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 3.78/4.00      inference('demod', [status(thm)], ['24', '25'])).
% 3.78/4.00  thf('44', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 3.78/4.00      inference('sup+', [status(thm)], ['42', '43'])).
% 3.78/4.00  thf('45', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 3.78/4.00      inference('cnf', [status(esa)], [t3_boole])).
% 3.78/4.00  thf('46', plain,
% 3.78/4.00      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 3.78/4.00      inference('sup+', [status(thm)], ['44', '45'])).
% 3.78/4.00  thf('47', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 3.78/4.00      inference('cnf', [status(esa)], [t3_boole])).
% 3.78/4.00  thf('48', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]:
% 3.78/4.00         ((X0) = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1)))),
% 3.78/4.00      inference('demod', [status(thm)], ['34', '46', '47'])).
% 3.78/4.00  thf('49', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ k1_xboole_0))),
% 3.78/4.00      inference('sup+', [status(thm)], ['31', '48'])).
% 3.78/4.00  thf('50', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0) = (k1_xboole_0))),
% 3.78/4.00      inference('demod', [status(thm)], ['30', '49'])).
% 3.78/4.00  thf('51', plain,
% 3.78/4.00      (![X9 : $i, X10 : $i]:
% 3.78/4.00         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 3.78/4.00      inference('cnf', [status(esa)], [t37_xboole_1])).
% 3.78/4.00  thf('52', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]:
% 3.78/4.00         (((k1_xboole_0) != (k1_xboole_0))
% 3.78/4.00          | (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 3.78/4.00      inference('sup-', [status(thm)], ['50', '51'])).
% 3.78/4.00  thf('53', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 3.78/4.00      inference('simplify', [status(thm)], ['52'])).
% 3.78/4.00  thf('54', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 3.78/4.00      inference('sup+', [status(thm)], ['42', '43'])).
% 3.78/4.00  thf('55', plain,
% 3.78/4.00      (![X9 : $i, X10 : $i]:
% 3.78/4.00         ((r1_tarski @ X9 @ X10) | ((k4_xboole_0 @ X9 @ X10) != (k1_xboole_0)))),
% 3.78/4.00      inference('cnf', [status(esa)], [t37_xboole_1])).
% 3.78/4.00  thf('56', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]:
% 3.78/4.00         (((k1_xboole_0) != (k1_xboole_0))
% 3.78/4.00          | (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 3.78/4.00      inference('sup-', [status(thm)], ['54', '55'])).
% 3.78/4.00  thf('57', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X0)),
% 3.78/4.00      inference('simplify', [status(thm)], ['56'])).
% 3.78/4.00  thf(t67_xboole_1, axiom,
% 3.78/4.00    (![A:$i,B:$i,C:$i]:
% 3.78/4.00     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 3.78/4.00         ( r1_xboole_0 @ B @ C ) ) =>
% 3.78/4.00       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 3.78/4.00  thf('58', plain,
% 3.78/4.00      (![X22 : $i, X23 : $i, X24 : $i]:
% 3.78/4.00         (((X22) = (k1_xboole_0))
% 3.78/4.00          | ~ (r1_tarski @ X22 @ X23)
% 3.78/4.00          | ~ (r1_tarski @ X22 @ X24)
% 3.78/4.00          | ~ (r1_xboole_0 @ X23 @ X24))),
% 3.78/4.00      inference('cnf', [status(esa)], [t67_xboole_1])).
% 3.78/4.00  thf('59', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.78/4.00         (~ (r1_xboole_0 @ X0 @ X2)
% 3.78/4.00          | ~ (r1_tarski @ (k3_xboole_0 @ X0 @ X1) @ X2)
% 3.78/4.00          | ((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)))),
% 3.78/4.00      inference('sup-', [status(thm)], ['57', '58'])).
% 3.78/4.00  thf('60', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]:
% 3.78/4.00         (((k3_xboole_0 @ X1 @ X0) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 3.78/4.00      inference('sup-', [status(thm)], ['53', '59'])).
% 3.78/4.00  thf('61', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 3.78/4.00      inference('sup-', [status(thm)], ['11', '60'])).
% 3.78/4.00  thf('62', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.78/4.00      inference('sup-', [status(thm)], ['18', '19'])).
% 3.78/4.00  thf('63', plain,
% 3.78/4.00      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ X19 @ (k3_xboole_0 @ X20 @ X21))
% 3.78/4.00           = (k2_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ 
% 3.78/4.00              (k4_xboole_0 @ X19 @ X21)))),
% 3.78/4.00      inference('cnf', [status(esa)], [t54_xboole_1])).
% 3.78/4.00  thf('64', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 3.78/4.00           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.78/4.00      inference('sup+', [status(thm)], ['62', '63'])).
% 3.78/4.00  thf('65', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 3.78/4.00      inference('cnf', [status(esa)], [t3_boole])).
% 3.78/4.00  thf('66', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.78/4.00      inference('sup-', [status(thm)], ['18', '19'])).
% 3.78/4.00  thf('67', plain,
% 3.78/4.00      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X18))
% 3.78/4.00           = (k2_xboole_0 @ (k4_xboole_0 @ X16 @ X17) @ 
% 3.78/4.00              (k3_xboole_0 @ X16 @ X18)))),
% 3.78/4.00      inference('cnf', [status(esa)], [t52_xboole_1])).
% 3.78/4.00  thf('68', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ X1 @ (k4_xboole_0 @ X1 @ X0))
% 3.78/4.00           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.78/4.00      inference('sup+', [status(thm)], ['66', '67'])).
% 3.78/4.00  thf('69', plain,
% 3.78/4.00      (![X0 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ X0 @ X0)
% 3.78/4.00           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 3.78/4.00      inference('sup+', [status(thm)], ['65', '68'])).
% 3.78/4.00  thf('70', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 3.78/4.00      inference('sup-', [status(thm)], ['18', '19'])).
% 3.78/4.00  thf('71', plain,
% 3.78/4.00      (![X0 : $i]:
% 3.78/4.00         ((k1_xboole_0)
% 3.78/4.00           = (k2_xboole_0 @ k1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0)))),
% 3.78/4.00      inference('demod', [status(thm)], ['69', '70'])).
% 3.78/4.00  thf('72', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 3.78/4.00      inference('demod', [status(thm)], ['24', '25'])).
% 3.78/4.00  thf('73', plain,
% 3.78/4.00      (![X0 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 3.78/4.00           = (k1_xboole_0))),
% 3.78/4.00      inference('sup+', [status(thm)], ['71', '72'])).
% 3.78/4.00  thf('74', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 3.78/4.00      inference('cnf', [status(esa)], [t3_boole])).
% 3.78/4.00  thf('75', plain,
% 3.78/4.00      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 3.78/4.00      inference('demod', [status(thm)], ['73', '74'])).
% 3.78/4.00  thf('76', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 3.78/4.00           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.78/4.00      inference('sup+', [status(thm)], ['62', '63'])).
% 3.78/4.00  thf('77', plain,
% 3.78/4.00      (![X0 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ X0 @ k1_xboole_0)
% 3.78/4.00           = (k2_xboole_0 @ k1_xboole_0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 3.78/4.00      inference('sup+', [status(thm)], ['75', '76'])).
% 3.78/4.00  thf('78', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 3.78/4.00      inference('cnf', [status(esa)], [t3_boole])).
% 3.78/4.00  thf('79', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 3.78/4.00      inference('cnf', [status(esa)], [t3_boole])).
% 3.78/4.00  thf('80', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 3.78/4.00      inference('demod', [status(thm)], ['77', '78', '79'])).
% 3.78/4.00  thf('81', plain,
% 3.78/4.00      (![X0 : $i, X1 : $i]:
% 3.78/4.00         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))
% 3.78/4.00           = (k4_xboole_0 @ X1 @ X0))),
% 3.78/4.00      inference('demod', [status(thm)], ['64', '80'])).
% 3.78/4.00  thf('82', plain,
% 3.78/4.00      (((k4_xboole_0 @ sk_A @ k1_xboole_0) = (k4_xboole_0 @ sk_A @ sk_B))),
% 3.78/4.00      inference('sup+', [status(thm)], ['61', '81'])).
% 3.78/4.00  thf('83', plain, (![X12 : $i]: ((k4_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 3.78/4.00      inference('cnf', [status(esa)], [t3_boole])).
% 3.78/4.00  thf('84', plain, (((sk_A) = (k4_xboole_0 @ sk_A @ sk_B))),
% 3.78/4.00      inference('demod', [status(thm)], ['82', '83'])).
% 3.78/4.00  thf('85', plain,
% 3.78/4.00      ((((k4_xboole_0 @ sk_A @ sk_B) != (sk_A)))
% 3.78/4.00         <= (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A))))),
% 3.78/4.00      inference('split', [status(esa)], ['2'])).
% 3.78/4.00  thf('86', plain, (~ (((k4_xboole_0 @ sk_A @ sk_B) = (sk_A)))),
% 3.78/4.00      inference('sat_resolution*', [status(thm)], ['3', '8'])).
% 3.78/4.00  thf('87', plain, (((k4_xboole_0 @ sk_A @ sk_B) != (sk_A))),
% 3.78/4.00      inference('simpl_trail', [status(thm)], ['85', '86'])).
% 3.78/4.00  thf('88', plain, ($false),
% 3.78/4.00      inference('simplify_reflect-', [status(thm)], ['84', '87'])).
% 3.78/4.00  
% 3.78/4.00  % SZS output end Refutation
% 3.78/4.00  
% 3.78/4.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
