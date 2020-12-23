%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Wqabl777R

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:08 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 225 expanded)
%              Number of leaves         :   18 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :  638 (1893 expanded)
%              Number of equality atoms :   23 (  43 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t38_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 )
      | ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('10',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ ( k1_tarski @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('13',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('17',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r1_tarski @ X14 @ X15 )
      | ~ ( r1_tarski @ X15 @ X16 )
      | ( r1_tarski @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X2 )
      | ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ ( k1_tarski @ X24 ) @ X25 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('24',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('26',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,(
    ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['13','26','27'])).

thf('29',plain,(
    ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','28'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X0 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['31'])).

thf('33',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 )
      | ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X0 @ X0 ) @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['31'])).

thf('37',plain,(
    ! [X0: $i] :
      ( X0
      = ( k2_xboole_0 @ X0 @ X0 ) ) ),
    inference(clc,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('39',plain,(
    ! [X24: $i,X26: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X24 ) @ X26 )
      | ~ ( r2_hidden @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('40',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('42',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sat_resolution*',[status(thm)],['13','26','27','41'])).

thf('43',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C ),
    inference(simpl_trail,[status(thm)],['40','42'])).

thf(t9_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('44',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( r1_tarski @ ( k2_xboole_0 @ X19 @ X21 ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C ) @ sk_C ),
    inference('sup+',[status(thm)],['37','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('48',plain,(
    r1_tarski @ ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ) @ sk_C ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ X17 @ ( k2_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('50',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k2_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) )
    = sk_C ),
    inference('sup-',[status(thm)],['48','51'])).

thf('53',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['53'])).

thf('55',plain,(
    ! [X24: $i,X26: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X24 ) @ X26 )
      | ~ ( r2_hidden @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('56',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['53'])).

thf('58',plain,(
    r2_hidden @ sk_B @ sk_C ),
    inference('sat_resolution*',[status(thm)],['13','26','27','57'])).

thf('59',plain,(
    r1_tarski @ ( k1_tarski @ sk_B ) @ sk_C ),
    inference(simpl_trail,[status(thm)],['56','58'])).

thf('60',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ( r1_tarski @ ( k2_xboole_0 @ X19 @ X21 ) @ ( k2_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t9_xboole_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) @ ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) ) @ sk_C ),
    inference('sup+',[status(thm)],['52','61'])).

thf('63',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k2_tarski @ X22 @ X23 )
      = ( k2_xboole_0 @ ( k1_tarski @ X22 ) @ ( k1_tarski @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['29','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7Wqabl777R
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:59:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.89  % Solved by: fo/fo7.sh
% 0.68/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.89  % done 932 iterations in 0.436s
% 0.68/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.89  % SZS output start Refutation
% 0.68/0.89  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.68/0.89  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.68/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.68/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.89  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.68/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.89  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.68/0.89  thf(t38_zfmisc_1, conjecture,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.68/0.89       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.68/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.89    (~( ![A:$i,B:$i,C:$i]:
% 0.68/0.89        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.68/0.89          ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ) )),
% 0.68/0.89    inference('cnf.neg', [status(esa)], [t38_zfmisc_1])).
% 0.68/0.89  thf('0', plain,
% 0.68/0.89      ((~ (r2_hidden @ sk_B @ sk_C)
% 0.68/0.89        | ~ (r2_hidden @ sk_A @ sk_C)
% 0.68/0.89        | ~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('1', plain,
% 0.68/0.89      ((~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.68/0.89         <= (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.68/0.89      inference('split', [status(esa)], ['0'])).
% 0.68/0.89  thf('2', plain,
% 0.68/0.89      (((r2_hidden @ sk_A @ sk_C)
% 0.68/0.89        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('3', plain,
% 0.68/0.89      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.68/0.89         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.68/0.89      inference('split', [status(esa)], ['2'])).
% 0.68/0.89  thf(t41_enumset1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( k2_tarski @ A @ B ) =
% 0.68/0.89       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.68/0.89  thf('4', plain,
% 0.68/0.89      (![X22 : $i, X23 : $i]:
% 0.68/0.89         ((k2_tarski @ X22 @ X23)
% 0.68/0.89           = (k2_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X23)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.68/0.89  thf(t7_xboole_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.68/0.89  thf('5', plain,
% 0.68/0.89      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.68/0.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.68/0.89  thf('6', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['4', '5'])).
% 0.68/0.89  thf(t1_xboole_1, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.68/0.89       ( r1_tarski @ A @ C ) ))).
% 0.68/0.89  thf('7', plain,
% 0.68/0.89      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.89         (~ (r1_tarski @ X14 @ X15)
% 0.68/0.89          | ~ (r1_tarski @ X15 @ X16)
% 0.68/0.89          | (r1_tarski @ X14 @ X16))),
% 0.68/0.89      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.68/0.89  thf('8', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         ((r1_tarski @ (k1_tarski @ X1) @ X2)
% 0.68/0.89          | ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.68/0.89      inference('sup-', [status(thm)], ['6', '7'])).
% 0.68/0.89  thf('9', plain,
% 0.68/0.89      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C))
% 0.68/0.89         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['3', '8'])).
% 0.68/0.89  thf(l1_zfmisc_1, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.68/0.89  thf('10', plain,
% 0.68/0.89      (![X24 : $i, X25 : $i]:
% 0.68/0.89         ((r2_hidden @ X24 @ X25) | ~ (r1_tarski @ (k1_tarski @ X24) @ X25))),
% 0.68/0.89      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.68/0.89  thf('11', plain,
% 0.68/0.89      (((r2_hidden @ sk_A @ sk_C))
% 0.68/0.89         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['9', '10'])).
% 0.68/0.89  thf('12', plain,
% 0.68/0.89      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.68/0.89      inference('split', [status(esa)], ['0'])).
% 0.68/0.89  thf('13', plain,
% 0.68/0.89      (((r2_hidden @ sk_A @ sk_C)) | 
% 0.68/0.89       ~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.68/0.89      inference('sup-', [status(thm)], ['11', '12'])).
% 0.68/0.89  thf('14', plain,
% 0.68/0.89      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.68/0.89         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.68/0.89      inference('split', [status(esa)], ['2'])).
% 0.68/0.89  thf('15', plain,
% 0.68/0.89      (![X22 : $i, X23 : $i]:
% 0.68/0.89         ((k2_tarski @ X22 @ X23)
% 0.68/0.89           = (k2_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X23)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.68/0.89  thf(commutativity_k2_xboole_0, axiom,
% 0.68/0.89    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.68/0.89  thf('16', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.68/0.89  thf('17', plain,
% 0.68/0.89      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.68/0.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.68/0.89  thf('18', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['16', '17'])).
% 0.68/0.89  thf('19', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['15', '18'])).
% 0.68/0.89  thf('20', plain,
% 0.68/0.89      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.68/0.89         (~ (r1_tarski @ X14 @ X15)
% 0.68/0.89          | ~ (r1_tarski @ X15 @ X16)
% 0.68/0.89          | (r1_tarski @ X14 @ X16))),
% 0.68/0.89      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.68/0.89  thf('21', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.89         ((r1_tarski @ (k1_tarski @ X0) @ X2)
% 0.68/0.89          | ~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2))),
% 0.68/0.89      inference('sup-', [status(thm)], ['19', '20'])).
% 0.68/0.89  thf('22', plain,
% 0.68/0.89      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_C))
% 0.68/0.89         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['14', '21'])).
% 0.68/0.89  thf('23', plain,
% 0.68/0.89      (![X24 : $i, X25 : $i]:
% 0.68/0.89         ((r2_hidden @ X24 @ X25) | ~ (r1_tarski @ (k1_tarski @ X24) @ X25))),
% 0.68/0.89      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.68/0.89  thf('24', plain,
% 0.68/0.89      (((r2_hidden @ sk_B @ sk_C))
% 0.68/0.89         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['22', '23'])).
% 0.68/0.89  thf('25', plain,
% 0.68/0.89      ((~ (r2_hidden @ sk_B @ sk_C)) <= (~ ((r2_hidden @ sk_B @ sk_C)))),
% 0.68/0.89      inference('split', [status(esa)], ['0'])).
% 0.68/0.89  thf('26', plain,
% 0.68/0.89      (((r2_hidden @ sk_B @ sk_C)) | 
% 0.68/0.89       ~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.68/0.89      inference('sup-', [status(thm)], ['24', '25'])).
% 0.68/0.89  thf('27', plain,
% 0.68/0.89      (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)) | 
% 0.68/0.89       ~ ((r2_hidden @ sk_A @ sk_C)) | ~ ((r2_hidden @ sk_B @ sk_C))),
% 0.68/0.89      inference('split', [status(esa)], ['0'])).
% 0.68/0.89  thf('28', plain, (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.68/0.89      inference('sat_resolution*', [status(thm)], ['13', '26', '27'])).
% 0.68/0.89  thf('29', plain, (~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.68/0.89      inference('simpl_trail', [status(thm)], ['1', '28'])).
% 0.68/0.89  thf(d3_xboole_0, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.68/0.89       ( ![D:$i]:
% 0.68/0.89         ( ( r2_hidden @ D @ C ) <=>
% 0.68/0.89           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.68/0.89  thf('30', plain,
% 0.68/0.89      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.68/0.89         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.68/0.89          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.68/0.89          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 0.68/0.89          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.68/0.89  thf('31', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.68/0.89          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X0)
% 0.68/0.89          | ((X1) = (k2_xboole_0 @ X0 @ X0)))),
% 0.68/0.89      inference('eq_fact', [status(thm)], ['30'])).
% 0.68/0.89  thf('32', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 0.68/0.89          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 0.68/0.89      inference('eq_fact', [status(thm)], ['31'])).
% 0.68/0.89  thf('33', plain,
% 0.68/0.89      (![X3 : $i, X5 : $i, X7 : $i]:
% 0.68/0.89         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 0.68/0.89          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 0.68/0.89          | ~ (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 0.68/0.89      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.68/0.89  thf('34', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 0.68/0.89          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.68/0.89          | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['32', '33'])).
% 0.68/0.89  thf('35', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0)
% 0.68/0.89          | ((X0) = (k2_xboole_0 @ X0 @ X0)))),
% 0.68/0.89      inference('simplify', [status(thm)], ['34'])).
% 0.68/0.89  thf('36', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (((X0) = (k2_xboole_0 @ X0 @ X0))
% 0.68/0.89          | (r2_hidden @ (sk_D @ X0 @ X0 @ X0) @ X0))),
% 0.68/0.89      inference('eq_fact', [status(thm)], ['31'])).
% 0.68/0.89  thf('37', plain, (![X0 : $i]: ((X0) = (k2_xboole_0 @ X0 @ X0))),
% 0.68/0.89      inference('clc', [status(thm)], ['35', '36'])).
% 0.68/0.89  thf('38', plain,
% 0.68/0.89      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.68/0.89      inference('split', [status(esa)], ['2'])).
% 0.68/0.89  thf('39', plain,
% 0.68/0.89      (![X24 : $i, X26 : $i]:
% 0.68/0.89         ((r1_tarski @ (k1_tarski @ X24) @ X26) | ~ (r2_hidden @ X24 @ X26))),
% 0.68/0.89      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.68/0.89  thf('40', plain,
% 0.68/0.89      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C))
% 0.68/0.89         <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['38', '39'])).
% 0.68/0.89  thf('41', plain,
% 0.68/0.89      (((r2_hidden @ sk_A @ sk_C)) | 
% 0.68/0.89       ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.68/0.89      inference('split', [status(esa)], ['2'])).
% 0.68/0.89  thf('42', plain, (((r2_hidden @ sk_A @ sk_C))),
% 0.68/0.89      inference('sat_resolution*', [status(thm)], ['13', '26', '27', '41'])).
% 0.68/0.89  thf('43', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ sk_C)),
% 0.68/0.89      inference('simpl_trail', [status(thm)], ['40', '42'])).
% 0.68/0.89  thf(t9_xboole_1, axiom,
% 0.68/0.89    (![A:$i,B:$i,C:$i]:
% 0.68/0.89     ( ( r1_tarski @ A @ B ) =>
% 0.68/0.89       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.68/0.89  thf('44', plain,
% 0.68/0.89      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.68/0.89         (~ (r1_tarski @ X19 @ X20)
% 0.68/0.89          | (r1_tarski @ (k2_xboole_0 @ X19 @ X21) @ (k2_xboole_0 @ X20 @ X21)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t9_xboole_1])).
% 0.68/0.89  thf('45', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ 
% 0.68/0.89          (k2_xboole_0 @ sk_C @ X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['43', '44'])).
% 0.68/0.89  thf('46', plain,
% 0.68/0.89      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_C) @ sk_C)),
% 0.68/0.89      inference('sup+', [status(thm)], ['37', '45'])).
% 0.68/0.89  thf('47', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.68/0.89  thf('48', plain,
% 0.68/0.89      ((r1_tarski @ (k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) @ sk_C)),
% 0.68/0.89      inference('demod', [status(thm)], ['46', '47'])).
% 0.68/0.89  thf('49', plain,
% 0.68/0.89      (![X17 : $i, X18 : $i]: (r1_tarski @ X17 @ (k2_xboole_0 @ X17 @ X18))),
% 0.68/0.89      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.68/0.89  thf(d10_xboole_0, axiom,
% 0.68/0.89    (![A:$i,B:$i]:
% 0.68/0.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.68/0.89  thf('50', plain,
% 0.68/0.89      (![X8 : $i, X10 : $i]:
% 0.68/0.89         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.68/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.89  thf('51', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.68/0.89          | ((k2_xboole_0 @ X1 @ X0) = (X1)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['49', '50'])).
% 0.68/0.89  thf('52', plain, (((k2_xboole_0 @ sk_C @ (k1_tarski @ sk_A)) = (sk_C))),
% 0.68/0.89      inference('sup-', [status(thm)], ['48', '51'])).
% 0.68/0.89  thf('53', plain,
% 0.68/0.89      (((r2_hidden @ sk_B @ sk_C)
% 0.68/0.89        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.68/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.89  thf('54', plain,
% 0.68/0.89      (((r2_hidden @ sk_B @ sk_C)) <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.68/0.89      inference('split', [status(esa)], ['53'])).
% 0.68/0.89  thf('55', plain,
% 0.68/0.89      (![X24 : $i, X26 : $i]:
% 0.68/0.89         ((r1_tarski @ (k1_tarski @ X24) @ X26) | ~ (r2_hidden @ X24 @ X26))),
% 0.68/0.89      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.68/0.89  thf('56', plain,
% 0.68/0.89      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_C))
% 0.68/0.89         <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.68/0.89      inference('sup-', [status(thm)], ['54', '55'])).
% 0.68/0.89  thf('57', plain,
% 0.68/0.89      (((r2_hidden @ sk_B @ sk_C)) | 
% 0.68/0.89       ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.68/0.89      inference('split', [status(esa)], ['53'])).
% 0.68/0.89  thf('58', plain, (((r2_hidden @ sk_B @ sk_C))),
% 0.68/0.89      inference('sat_resolution*', [status(thm)], ['13', '26', '27', '57'])).
% 0.68/0.89  thf('59', plain, ((r1_tarski @ (k1_tarski @ sk_B) @ sk_C)),
% 0.68/0.89      inference('simpl_trail', [status(thm)], ['56', '58'])).
% 0.68/0.89  thf('60', plain,
% 0.68/0.89      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.68/0.89         (~ (r1_tarski @ X19 @ X20)
% 0.68/0.89          | (r1_tarski @ (k2_xboole_0 @ X19 @ X21) @ (k2_xboole_0 @ X20 @ X21)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t9_xboole_1])).
% 0.68/0.89  thf('61', plain,
% 0.68/0.89      (![X0 : $i]:
% 0.68/0.89         (r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_B) @ X0) @ 
% 0.68/0.89          (k2_xboole_0 @ sk_C @ X0))),
% 0.68/0.89      inference('sup-', [status(thm)], ['59', '60'])).
% 0.68/0.89  thf('62', plain,
% 0.68/0.89      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A)) @ 
% 0.68/0.89        sk_C)),
% 0.68/0.89      inference('sup+', [status(thm)], ['52', '61'])).
% 0.68/0.89  thf('63', plain,
% 0.68/0.89      (![X22 : $i, X23 : $i]:
% 0.68/0.89         ((k2_tarski @ X22 @ X23)
% 0.68/0.89           = (k2_xboole_0 @ (k1_tarski @ X22) @ (k1_tarski @ X23)))),
% 0.68/0.89      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.68/0.89  thf('64', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.68/0.89      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.68/0.89  thf('65', plain,
% 0.68/0.89      (![X0 : $i, X1 : $i]:
% 0.68/0.89         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.68/0.89           = (k2_tarski @ X1 @ X0))),
% 0.68/0.89      inference('sup+', [status(thm)], ['63', '64'])).
% 0.68/0.89  thf('66', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.68/0.89      inference('demod', [status(thm)], ['62', '65'])).
% 0.68/0.89  thf('67', plain, ($false), inference('demod', [status(thm)], ['29', '66'])).
% 0.68/0.89  
% 0.68/0.89  % SZS output end Refutation
% 0.68/0.89  
% 0.72/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
