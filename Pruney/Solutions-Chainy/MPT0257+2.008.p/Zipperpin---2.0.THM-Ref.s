%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RCVp8CNCUk

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:22 EST 2020

% Result     : Theorem 0.66s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 452 expanded)
%              Number of leaves         :   25 ( 160 expanded)
%              Depth                    :   17
%              Number of atoms          : 1000 (3478 expanded)
%              Number of equality atoms :  113 ( 388 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(t52_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r2_hidden @ A @ B )
       => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
          = ( k1_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_zfmisc_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t42_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X38: $i,X40: $i,X41: $i] :
      ( ( r1_tarski @ X40 @ ( k2_tarski @ X38 @ X41 ) )
      | ( X40
       != ( k1_tarski @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t42_zfmisc_1])).

thf('3',plain,(
    ! [X38: $i,X41: $i] :
      ( r1_tarski @ ( k1_tarski @ X38 ) @ ( k2_tarski @ X38 @ X41 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k1_tarski @ X0 ) ) @ ( k2_tarski @ X0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t77_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_enumset1 @ A @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X32 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf(t123_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_enumset1 @ D @ B @ C @ A ) ) )).

thf('8',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( k2_enumset1 @ X31 @ X29 @ X30 @ X28 )
      = ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t123_enumset1])).

thf('9',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k2_enumset1 @ X32 @ X32 @ X32 @ X33 )
      = ( k2_tarski @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t77_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('10',plain,(
    ! [X22: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X26 @ X24 )
      | ( X26 = X25 )
      | ( X26 = X22 )
      | ( X24
       != ( k2_tarski @ X25 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('11',plain,(
    ! [X22: $i,X25: $i,X26: $i] :
      ( ( X26 = X22 )
      | ( X26 = X25 )
      | ~ ( r2_hidden @ X26 @ ( k2_tarski @ X25 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 ) )
      | ( X2 = X1 )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_enumset1 @ X1 @ X0 @ X0 @ X0 ) )
      | ( X2 = X1 )
      | ( X2 = X0 ) ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( X1 = X0 )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['6','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['0','19'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('22',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('24',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( k3_xboole_0 @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf('27',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('35',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf(t111_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t111_xboole_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('39',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['26','45'])).

thf('47',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['37','44'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['46','49','50'])).

thf('52',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 ) )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('56',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('58',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','62'])).

thf('64',plain,(
    ! [X14: $i] :
      ( ( k4_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('65',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k4_xboole_0 @ X17 @ ( k4_xboole_0 @ X17 @ X18 ) )
      = ( k3_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('68',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf(t47_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('69',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('70',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t111_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k4_xboole_0 @ X15 @ ( k3_xboole_0 @ X15 @ X16 ) )
      = ( k4_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t47_xboole_1])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['63','68','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('76',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t111_xboole_1])).

thf(t32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = ( k4_xboole_0 @ B @ A ) )
     => ( A = B ) ) )).

thf('77',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11 = X10 )
      | ( ( k4_xboole_0 @ X11 @ X10 )
       != ( k4_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t32_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X0 ) )
       != ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t111_xboole_1])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ ( k4_xboole_0 @ X1 @ X2 ) @ X0 )
       != ( k3_xboole_0 @ ( k4_xboole_0 @ X2 @ X1 ) @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
       != ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['75','80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('83',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
       != ( k4_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['81','82','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['63','68','73'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
       != ( k4_xboole_0 @ X0 @ X1 ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['74','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55','56','61'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k3_xboole_0 @ X0 @ X1 )
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( k1_tarski @ sk_A )
    = ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','90'])).

thf('92',plain,(
    ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
 != ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['91','92'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.RCVp8CNCUk
% 0.13/0.36  % Computer   : n006.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 12:16:53 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.66/0.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.66/0.91  % Solved by: fo/fo7.sh
% 0.66/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.66/0.91  % done 762 iterations in 0.440s
% 0.66/0.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.66/0.91  % SZS output start Refutation
% 0.66/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.66/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.66/0.91  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.66/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.66/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.66/0.91  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.66/0.91  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.66/0.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.66/0.91  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.66/0.91  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.66/0.91  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.66/0.91  thf(t52_zfmisc_1, conjecture,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( r2_hidden @ A @ B ) =>
% 0.66/0.91       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.66/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.66/0.91    (~( ![A:$i,B:$i]:
% 0.66/0.91        ( ( r2_hidden @ A @ B ) =>
% 0.66/0.91          ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ) )),
% 0.66/0.91    inference('cnf.neg', [status(esa)], [t52_zfmisc_1])).
% 0.66/0.91  thf('0', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf(d3_tarski, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( r1_tarski @ A @ B ) <=>
% 0.66/0.91       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.66/0.91  thf('1', plain,
% 0.66/0.91      (![X1 : $i, X3 : $i]:
% 0.66/0.91         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.66/0.91      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.91  thf(t42_zfmisc_1, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i]:
% 0.66/0.91     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.66/0.91       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.66/0.91            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.66/0.91  thf('2', plain,
% 0.66/0.91      (![X38 : $i, X40 : $i, X41 : $i]:
% 0.66/0.91         ((r1_tarski @ X40 @ (k2_tarski @ X38 @ X41))
% 0.66/0.91          | ((X40) != (k1_tarski @ X38)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t42_zfmisc_1])).
% 0.66/0.91  thf('3', plain,
% 0.66/0.91      (![X38 : $i, X41 : $i]:
% 0.66/0.91         (r1_tarski @ (k1_tarski @ X38) @ (k2_tarski @ X38 @ X41))),
% 0.66/0.91      inference('simplify', [status(thm)], ['2'])).
% 0.66/0.91  thf('4', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X0 @ X1)
% 0.66/0.91          | (r2_hidden @ X0 @ X2)
% 0.66/0.91          | ~ (r1_tarski @ X1 @ X2))),
% 0.66/0.91      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.91  thf('5', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.66/0.91          | ~ (r2_hidden @ X2 @ (k1_tarski @ X1)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['3', '4'])).
% 0.66/0.91  thf('6', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.66/0.91          | (r2_hidden @ (sk_C @ X1 @ (k1_tarski @ X0)) @ (k2_tarski @ X0 @ X2)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['1', '5'])).
% 0.66/0.91  thf(t77_enumset1, axiom,
% 0.66/0.91    (![A:$i,B:$i]: ( ( k2_enumset1 @ A @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.66/0.91  thf('7', plain,
% 0.66/0.91      (![X32 : $i, X33 : $i]:
% 0.66/0.91         ((k2_enumset1 @ X32 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 0.66/0.91      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.66/0.91  thf(t123_enumset1, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.66/0.91     ( ( k2_enumset1 @ A @ B @ C @ D ) = ( k2_enumset1 @ D @ B @ C @ A ) ))).
% 0.66/0.91  thf('8', plain,
% 0.66/0.91      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.66/0.91         ((k2_enumset1 @ X31 @ X29 @ X30 @ X28)
% 0.66/0.91           = (k2_enumset1 @ X28 @ X29 @ X30 @ X31))),
% 0.66/0.91      inference('cnf', [status(esa)], [t123_enumset1])).
% 0.66/0.91  thf('9', plain,
% 0.66/0.91      (![X32 : $i, X33 : $i]:
% 0.66/0.91         ((k2_enumset1 @ X32 @ X32 @ X32 @ X33) = (k2_tarski @ X32 @ X33))),
% 0.66/0.91      inference('cnf', [status(esa)], [t77_enumset1])).
% 0.66/0.91  thf(d2_tarski, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i]:
% 0.66/0.91     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.66/0.91       ( ![D:$i]:
% 0.66/0.91         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.66/0.91  thf('10', plain,
% 0.66/0.91      (![X22 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X26 @ X24)
% 0.66/0.91          | ((X26) = (X25))
% 0.66/0.91          | ((X26) = (X22))
% 0.66/0.91          | ((X24) != (k2_tarski @ X25 @ X22)))),
% 0.66/0.91      inference('cnf', [status(esa)], [d2_tarski])).
% 0.66/0.91  thf('11', plain,
% 0.66/0.91      (![X22 : $i, X25 : $i, X26 : $i]:
% 0.66/0.91         (((X26) = (X22))
% 0.66/0.91          | ((X26) = (X25))
% 0.66/0.91          | ~ (r2_hidden @ X26 @ (k2_tarski @ X25 @ X22)))),
% 0.66/0.91      inference('simplify', [status(thm)], ['10'])).
% 0.66/0.91  thf('12', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X2 @ (k2_enumset1 @ X1 @ X1 @ X1 @ X0))
% 0.66/0.91          | ((X2) = (X1))
% 0.66/0.91          | ((X2) = (X0)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['9', '11'])).
% 0.66/0.91  thf('13', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X2 @ (k2_enumset1 @ X1 @ X0 @ X0 @ X0))
% 0.66/0.91          | ((X2) = (X1))
% 0.66/0.91          | ((X2) = (X0)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['8', '12'])).
% 0.66/0.91  thf('14', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 0.66/0.91          | ((X1) = (X0))
% 0.66/0.91          | ((X1) = (X0)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['7', '13'])).
% 0.66/0.91  thf('15', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         (((X1) = (X0)) | ~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0)))),
% 0.66/0.91      inference('simplify', [status(thm)], ['14'])).
% 0.66/0.91  thf('16', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.66/0.91          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['6', '15'])).
% 0.66/0.91  thf('17', plain,
% 0.66/0.91      (![X1 : $i, X3 : $i]:
% 0.66/0.91         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.66/0.91      inference('cnf', [status(esa)], [d3_tarski])).
% 0.66/0.91  thf('18', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         (~ (r2_hidden @ X0 @ X1)
% 0.66/0.91          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.66/0.91          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.66/0.91      inference('sup-', [status(thm)], ['16', '17'])).
% 0.66/0.91  thf('19', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.66/0.91      inference('simplify', [status(thm)], ['18'])).
% 0.66/0.91  thf('20', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_B)),
% 0.66/0.91      inference('sup-', [status(thm)], ['0', '19'])).
% 0.66/0.91  thf(l32_xboole_1, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.66/0.91  thf('21', plain,
% 0.66/0.91      (![X4 : $i, X6 : $i]:
% 0.66/0.91         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.66/0.91      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.66/0.91  thf('22', plain,
% 0.66/0.91      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['20', '21'])).
% 0.66/0.91  thf(t48_xboole_1, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.66/0.91  thf('23', plain,
% 0.66/0.91      (![X17 : $i, X18 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.66/0.91           = (k3_xboole_0 @ X17 @ X18))),
% 0.66/0.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.66/0.91  thf('24', plain,
% 0.66/0.91      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0)
% 0.66/0.91         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))),
% 0.66/0.91      inference('sup+', [status(thm)], ['22', '23'])).
% 0.66/0.91  thf(t3_boole, axiom,
% 0.66/0.91    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.66/0.91  thf('25', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.66/0.91      inference('cnf', [status(esa)], [t3_boole])).
% 0.66/0.91  thf(t50_xboole_1, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i]:
% 0.66/0.91     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.66/0.91       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.66/0.91  thf('26', plain,
% 0.66/0.91      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.66/0.91         ((k3_xboole_0 @ X19 @ (k4_xboole_0 @ X20 @ X21))
% 0.66/0.91           = (k4_xboole_0 @ (k3_xboole_0 @ X19 @ X20) @ 
% 0.66/0.91              (k3_xboole_0 @ X19 @ X21)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t50_xboole_1])).
% 0.66/0.91  thf('27', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.66/0.91      inference('cnf', [status(esa)], [t3_boole])).
% 0.66/0.91  thf(t36_xboole_1, axiom,
% 0.66/0.91    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.66/0.91  thf('28', plain,
% 0.66/0.91      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.66/0.91      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.66/0.91  thf('29', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.66/0.91      inference('sup+', [status(thm)], ['27', '28'])).
% 0.66/0.91  thf('30', plain,
% 0.66/0.91      (![X4 : $i, X6 : $i]:
% 0.66/0.91         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.66/0.91      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.66/0.91  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['29', '30'])).
% 0.66/0.91  thf('32', plain,
% 0.66/0.91      (![X17 : $i, X18 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.66/0.91           = (k3_xboole_0 @ X17 @ X18))),
% 0.66/0.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.66/0.91  thf('33', plain,
% 0.66/0.91      (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['31', '32'])).
% 0.66/0.91  thf('34', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.66/0.91      inference('cnf', [status(esa)], [t3_boole])).
% 0.66/0.91  thf('35', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['33', '34'])).
% 0.66/0.91  thf(t111_xboole_1, axiom,
% 0.66/0.91    (![A:$i,B:$i,C:$i]:
% 0.66/0.91     ( ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 0.66/0.91       ( k3_xboole_0 @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 0.66/0.91  thf('36', plain,
% 0.66/0.91      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 0.66/0.91           = (k3_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9))),
% 0.66/0.91      inference('cnf', [status(esa)], [t111_xboole_1])).
% 0.66/0.91  thf('37', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.66/0.91           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['35', '36'])).
% 0.66/0.91  thf('38', plain,
% 0.66/0.91      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.66/0.91      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.66/0.91  thf('39', plain,
% 0.66/0.91      (![X4 : $i, X6 : $i]:
% 0.66/0.91         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.66/0.91      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.66/0.91  thf('40', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['38', '39'])).
% 0.66/0.91  thf('41', plain,
% 0.66/0.91      (![X17 : $i, X18 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.66/0.91           = (k3_xboole_0 @ X17 @ X18))),
% 0.66/0.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.66/0.91  thf('42', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 0.66/0.91           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['40', '41'])).
% 0.66/0.91  thf('43', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.66/0.91      inference('cnf', [status(esa)], [t3_boole])).
% 0.66/0.91  thf('44', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X0 @ X1)
% 0.66/0.91           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['42', '43'])).
% 0.66/0.91  thf('45', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X0 @ X1)
% 0.66/0.91           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.66/0.91      inference('sup+', [status(thm)], ['37', '44'])).
% 0.66/0.91  thf('46', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1)
% 0.66/0.91           = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 0.66/0.91      inference('sup+', [status(thm)], ['26', '45'])).
% 0.66/0.91  thf('47', plain,
% 0.66/0.91      (![X17 : $i, X18 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.66/0.91           = (k3_xboole_0 @ X17 @ X18))),
% 0.66/0.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.66/0.91  thf('48', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['38', '39'])).
% 0.66/0.91  thf('49', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['47', '48'])).
% 0.66/0.91  thf('50', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X0 @ X1)
% 0.66/0.91           = (k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.66/0.91      inference('sup+', [status(thm)], ['37', '44'])).
% 0.66/0.91  thf('51', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k1_xboole_0) = (k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X1)))),
% 0.66/0.91      inference('demod', [status(thm)], ['46', '49', '50'])).
% 0.66/0.91  thf('52', plain,
% 0.66/0.91      (![X17 : $i, X18 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.66/0.91           = (k3_xboole_0 @ X17 @ X18))),
% 0.66/0.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.66/0.91  thf('53', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.66/0.91           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['35', '36'])).
% 0.66/0.91  thf('54', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X1 @ (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1))
% 0.66/0.91           = (k3_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1))),
% 0.66/0.91      inference('sup+', [status(thm)], ['52', '53'])).
% 0.66/0.91  thf('55', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.66/0.91           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['35', '36'])).
% 0.66/0.91  thf('56', plain,
% 0.66/0.91      (![X17 : $i, X18 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.66/0.91           = (k3_xboole_0 @ X17 @ X18))),
% 0.66/0.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.66/0.91  thf('57', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['47', '48'])).
% 0.66/0.91  thf('58', plain,
% 0.66/0.91      (![X17 : $i, X18 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.66/0.91           = (k3_xboole_0 @ X17 @ X18))),
% 0.66/0.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.66/0.91  thf('59', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ k1_xboole_0)
% 0.66/0.91           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['57', '58'])).
% 0.66/0.91  thf('60', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.66/0.91      inference('cnf', [status(esa)], [t3_boole])).
% 0.66/0.91  thf('61', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k3_xboole_0 @ X0 @ X1)
% 0.66/0.91           = (k3_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['59', '60'])).
% 0.66/0.91  thf('62', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 0.66/0.91           = (k3_xboole_0 @ X1 @ X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['54', '55', '56', '61'])).
% 0.66/0.91  thf('63', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0)
% 0.66/0.91           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['51', '62'])).
% 0.66/0.91  thf('64', plain, (![X14 : $i]: ((k4_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.66/0.91      inference('cnf', [status(esa)], [t3_boole])).
% 0.66/0.91  thf('65', plain,
% 0.66/0.91      (![X17 : $i, X18 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X17 @ (k4_xboole_0 @ X17 @ X18))
% 0.66/0.91           = (k3_xboole_0 @ X17 @ X18))),
% 0.66/0.91      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.66/0.91  thf('66', plain,
% 0.66/0.91      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['64', '65'])).
% 0.66/0.91  thf('67', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.66/0.91      inference('sup-', [status(thm)], ['29', '30'])).
% 0.66/0.91  thf('68', plain,
% 0.66/0.91      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.66/0.91      inference('demod', [status(thm)], ['66', '67'])).
% 0.66/0.91  thf(t47_xboole_1, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( k4_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.66/0.91  thf('69', plain,
% 0.66/0.91      (![X15 : $i, X16 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 0.66/0.91           = (k4_xboole_0 @ X15 @ X16))),
% 0.66/0.91      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.66/0.91  thf('70', plain,
% 0.66/0.91      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 0.66/0.91           = (k3_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9))),
% 0.66/0.91      inference('cnf', [status(esa)], [t111_xboole_1])).
% 0.66/0.91  thf('71', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.66/0.91           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 0.66/0.91      inference('sup+', [status(thm)], ['69', '70'])).
% 0.66/0.91  thf('72', plain,
% 0.66/0.91      (![X15 : $i, X16 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X15 @ (k3_xboole_0 @ X15 @ X16))
% 0.66/0.91           = (k4_xboole_0 @ X15 @ X16))),
% 0.66/0.91      inference('cnf', [status(esa)], [t47_xboole_1])).
% 0.66/0.91  thf('73', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.66/0.91           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['71', '72'])).
% 0.66/0.91  thf('74', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['63', '68', '73'])).
% 0.66/0.91  thf('75', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.66/0.91           = (k3_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['71', '72'])).
% 0.66/0.91  thf('76', plain,
% 0.66/0.91      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 0.66/0.91           = (k3_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9))),
% 0.66/0.91      inference('cnf', [status(esa)], [t111_xboole_1])).
% 0.66/0.91  thf(t32_xboole_1, axiom,
% 0.66/0.91    (![A:$i,B:$i]:
% 0.66/0.91     ( ( ( k4_xboole_0 @ A @ B ) = ( k4_xboole_0 @ B @ A ) ) =>
% 0.66/0.91       ( ( A ) = ( B ) ) ))).
% 0.66/0.91  thf('77', plain,
% 0.66/0.91      (![X10 : $i, X11 : $i]:
% 0.66/0.91         (((X11) = (X10))
% 0.66/0.91          | ((k4_xboole_0 @ X11 @ X10) != (k4_xboole_0 @ X10 @ X11)))),
% 0.66/0.91      inference('cnf', [status(esa)], [t32_xboole_1])).
% 0.66/0.91  thf('78', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         (((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X0))
% 0.66/0.91            != (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 0.66/0.91          | ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X2 @ X0)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['76', '77'])).
% 0.66/0.91  thf('79', plain,
% 0.66/0.91      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 0.66/0.91           = (k3_xboole_0 @ (k4_xboole_0 @ X7 @ X8) @ X9))),
% 0.66/0.91      inference('cnf', [status(esa)], [t111_xboole_1])).
% 0.66/0.91  thf('80', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.66/0.91         (((k3_xboole_0 @ (k4_xboole_0 @ X1 @ X2) @ X0)
% 0.66/0.91            != (k3_xboole_0 @ (k4_xboole_0 @ X2 @ X1) @ X0))
% 0.66/0.91          | ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X2 @ X0)))),
% 0.66/0.91      inference('demod', [status(thm)], ['78', '79'])).
% 0.66/0.91  thf('81', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         (((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.66/0.91            != (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))
% 0.66/0.91          | ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['75', '80'])).
% 0.66/0.91  thf('82', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k4_xboole_0 @ X0 @ X1)
% 0.66/0.91           = (k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['42', '43'])).
% 0.66/0.91  thf('83', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['33', '34'])).
% 0.66/0.91  thf('84', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         (((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 0.66/0.91            != (k4_xboole_0 @ X0 @ X1))
% 0.66/0.91          | ((k3_xboole_0 @ X1 @ X0) = (X0)))),
% 0.66/0.91      inference('demod', [status(thm)], ['81', '82', '83'])).
% 0.66/0.91  thf('85', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['63', '68', '73'])).
% 0.66/0.91  thf('86', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         (((k1_xboole_0) != (k4_xboole_0 @ X0 @ X1))
% 0.66/0.91          | ((k3_xboole_0 @ X1 @ X0) = (X0)))),
% 0.66/0.91      inference('demod', [status(thm)], ['84', '85'])).
% 0.66/0.91  thf('87', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         (((k1_xboole_0) != (k1_xboole_0))
% 0.66/0.91          | ((k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))
% 0.66/0.91              = (k3_xboole_0 @ X1 @ X0)))),
% 0.66/0.91      inference('sup-', [status(thm)], ['74', '86'])).
% 0.66/0.91  thf('88', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         ((k3_xboole_0 @ X1 @ (k3_xboole_0 @ X0 @ X1))
% 0.66/0.91           = (k3_xboole_0 @ X1 @ X0))),
% 0.66/0.91      inference('demod', [status(thm)], ['54', '55', '56', '61'])).
% 0.66/0.91  thf('89', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]:
% 0.66/0.91         (((k1_xboole_0) != (k1_xboole_0))
% 0.66/0.91          | ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0)))),
% 0.66/0.91      inference('demod', [status(thm)], ['87', '88'])).
% 0.66/0.91  thf('90', plain,
% 0.66/0.91      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 0.66/0.91      inference('simplify', [status(thm)], ['89'])).
% 0.66/0.91  thf('91', plain,
% 0.66/0.91      (((k1_tarski @ sk_A) = (k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.66/0.91      inference('demod', [status(thm)], ['24', '25', '90'])).
% 0.66/0.91  thf('92', plain,
% 0.66/0.91      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) != (k1_tarski @ sk_A))),
% 0.66/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.66/0.91  thf('93', plain, ($false),
% 0.66/0.91      inference('simplify_reflect-', [status(thm)], ['91', '92'])).
% 0.66/0.91  
% 0.66/0.91  % SZS output end Refutation
% 0.66/0.91  
% 0.66/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
