%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qXNMJyP2Ga

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:20 EST 2020

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 158 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :   15
%              Number of atoms          :  638 (1195 expanded)
%              Number of equality atoms :   71 ( 135 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t68_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 )
      <=> ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t68_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('5',plain,(
    ! [X66: $i,X68: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X66 ) @ X68 )
      | ~ ( r2_hidden @ X66 @ X68 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('6',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k2_xboole_0 @ X13 @ X12 )
        = X12 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('8',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X22 @ X23 ) @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X18 @ X19 ) @ X20 )
      = ( k5_xboole_0 @ X18 @ ( k5_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('11',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k3_xboole_0 @ X22 @ X23 )
      = ( k5_xboole_0 @ X22 @ ( k5_xboole_0 @ X23 @ ( k2_xboole_0 @ X22 @ X23 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('13',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('16',plain,(
    ! [X17: $i] :
      ( ( k5_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['12','13','14','17'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k4_xboole_0 @ X10 @ X11 )
      = ( k5_xboole_0 @ X10 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X21: $i] :
      ( ( k5_xboole_0 @ X21 @ X21 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('22',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','25'])).

thf('27',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','26'])).

thf('28',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k2_xboole_0 @ X15 @ ( k4_xboole_0 @ X16 @ X15 ) )
      = ( k2_xboole_0 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('30',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('31',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k2_tarski @ X25 @ X24 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X69: $i,X70: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X69 @ X70 ) )
      = ( k2_xboole_0 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X69: $i,X70: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X69 @ X70 ) )
      = ( k2_xboole_0 @ X69 @ X70 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('37',plain,(
    ! [X14: $i] :
      ( ( k2_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','35','38'])).

thf('40',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('41',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','25','40'])).

thf('42',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['39','41'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('43',plain,(
    ! [X38: $i] :
      ( ( k2_tarski @ X38 @ X38 )
      = ( k1_tarski @ X38 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_enumset1 @ X39 @ X39 @ X40 )
      = ( k2_tarski @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 )
      | ( r2_hidden @ X31 @ X35 )
      | ( X35
       != ( k1_enumset1 @ X34 @ X33 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( r2_hidden @ X31 @ ( k1_enumset1 @ X34 @ X33 @ X32 ) )
      | ( zip_tseitin_0 @ X31 @ X32 @ X33 @ X34 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X27 != X26 )
      | ~ ( zip_tseitin_0 @ X27 @ X28 @ X29 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('49',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ~ ( zip_tseitin_0 @ X26 @ X28 @ X29 @ X26 ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['43','50'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('52',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('53',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['42','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['27','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qXNMJyP2Ga
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:36:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.77/1.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.77/1.97  % Solved by: fo/fo7.sh
% 1.77/1.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.77/1.97  % done 836 iterations in 1.483s
% 1.77/1.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.77/1.97  % SZS output start Refutation
% 1.77/1.97  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.77/1.97  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 1.77/1.97  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.77/1.97  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.77/1.97  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.77/1.97  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.77/1.97  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.77/1.97  thf(sk_A_type, type, sk_A: $i).
% 1.77/1.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.77/1.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.77/1.97  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.77/1.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.77/1.97  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.77/1.97  thf(sk_B_type, type, sk_B: $i).
% 1.77/1.97  thf(t68_zfmisc_1, conjecture,
% 1.77/1.97    (![A:$i,B:$i]:
% 1.77/1.97     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 1.77/1.97       ( r2_hidden @ A @ B ) ))).
% 1.77/1.97  thf(zf_stmt_0, negated_conjecture,
% 1.77/1.97    (~( ![A:$i,B:$i]:
% 1.77/1.97        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 1.77/1.97          ( r2_hidden @ A @ B ) ) )),
% 1.77/1.97    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 1.77/1.97  thf('0', plain,
% 1.77/1.97      ((~ (r2_hidden @ sk_A @ sk_B)
% 1.77/1.97        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 1.77/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.97  thf('1', plain,
% 1.77/1.97      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 1.77/1.97      inference('split', [status(esa)], ['0'])).
% 1.77/1.97  thf('2', plain,
% 1.77/1.97      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 1.77/1.97       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 1.77/1.97      inference('split', [status(esa)], ['0'])).
% 1.77/1.97  thf('3', plain,
% 1.77/1.97      (((r2_hidden @ sk_A @ sk_B)
% 1.77/1.97        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 1.77/1.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.97  thf('4', plain,
% 1.77/1.97      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.77/1.97      inference('split', [status(esa)], ['3'])).
% 1.77/1.97  thf(l1_zfmisc_1, axiom,
% 1.77/1.97    (![A:$i,B:$i]:
% 1.77/1.97     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.77/1.97  thf('5', plain,
% 1.77/1.97      (![X66 : $i, X68 : $i]:
% 1.77/1.97         ((r1_tarski @ (k1_tarski @ X66) @ X68) | ~ (r2_hidden @ X66 @ X68))),
% 1.77/1.97      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.77/1.97  thf('6', plain,
% 1.77/1.97      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 1.77/1.97         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.77/1.97      inference('sup-', [status(thm)], ['4', '5'])).
% 1.77/1.97  thf(t12_xboole_1, axiom,
% 1.77/1.97    (![A:$i,B:$i]:
% 1.77/1.97     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 1.77/1.97  thf('7', plain,
% 1.77/1.97      (![X12 : $i, X13 : $i]:
% 1.77/1.97         (((k2_xboole_0 @ X13 @ X12) = (X12)) | ~ (r1_tarski @ X13 @ X12))),
% 1.77/1.97      inference('cnf', [status(esa)], [t12_xboole_1])).
% 1.77/1.97  thf('8', plain,
% 1.77/1.97      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B)))
% 1.77/1.97         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.77/1.97      inference('sup-', [status(thm)], ['6', '7'])).
% 1.77/1.97  thf(t95_xboole_1, axiom,
% 1.77/1.97    (![A:$i,B:$i]:
% 1.77/1.97     ( ( k3_xboole_0 @ A @ B ) =
% 1.77/1.97       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 1.77/1.97  thf('9', plain,
% 1.77/1.97      (![X22 : $i, X23 : $i]:
% 1.77/1.97         ((k3_xboole_0 @ X22 @ X23)
% 1.77/1.97           = (k5_xboole_0 @ (k5_xboole_0 @ X22 @ X23) @ 
% 1.77/1.97              (k2_xboole_0 @ X22 @ X23)))),
% 1.77/1.97      inference('cnf', [status(esa)], [t95_xboole_1])).
% 1.77/1.97  thf(t91_xboole_1, axiom,
% 1.77/1.97    (![A:$i,B:$i,C:$i]:
% 1.77/1.97     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.77/1.97       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.77/1.97  thf('10', plain,
% 1.77/1.97      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.77/1.97         ((k5_xboole_0 @ (k5_xboole_0 @ X18 @ X19) @ X20)
% 1.77/1.97           = (k5_xboole_0 @ X18 @ (k5_xboole_0 @ X19 @ X20)))),
% 1.77/1.97      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.77/1.97  thf('11', plain,
% 1.77/1.97      (![X22 : $i, X23 : $i]:
% 1.77/1.97         ((k3_xboole_0 @ X22 @ X23)
% 1.77/1.97           = (k5_xboole_0 @ X22 @ 
% 1.77/1.97              (k5_xboole_0 @ X23 @ (k2_xboole_0 @ X22 @ X23))))),
% 1.77/1.97      inference('demod', [status(thm)], ['9', '10'])).
% 1.77/1.97  thf('12', plain,
% 1.77/1.97      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 1.77/1.97          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k5_xboole_0 @ sk_B @ sk_B))))
% 1.77/1.97         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.77/1.97      inference('sup+', [status(thm)], ['8', '11'])).
% 1.77/1.97  thf(t92_xboole_1, axiom,
% 1.77/1.97    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.77/1.97  thf('13', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 1.77/1.97      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.77/1.97  thf(commutativity_k5_xboole_0, axiom,
% 1.77/1.97    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.77/1.97  thf('14', plain,
% 1.77/1.97      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.77/1.97      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.77/1.97  thf('15', plain,
% 1.77/1.97      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 1.77/1.97      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.77/1.97  thf(t5_boole, axiom,
% 1.77/1.97    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.77/1.97  thf('16', plain, (![X17 : $i]: ((k5_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 1.77/1.97      inference('cnf', [status(esa)], [t5_boole])).
% 1.77/1.97  thf('17', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.77/1.97      inference('sup+', [status(thm)], ['15', '16'])).
% 1.77/1.97  thf('18', plain,
% 1.77/1.97      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 1.77/1.97         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.77/1.97      inference('demod', [status(thm)], ['12', '13', '14', '17'])).
% 1.77/1.97  thf(t100_xboole_1, axiom,
% 1.77/1.97    (![A:$i,B:$i]:
% 1.77/1.97     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.77/1.97  thf('19', plain,
% 1.77/1.97      (![X10 : $i, X11 : $i]:
% 1.77/1.97         ((k4_xboole_0 @ X10 @ X11)
% 1.77/1.97           = (k5_xboole_0 @ X10 @ (k3_xboole_0 @ X10 @ X11)))),
% 1.77/1.97      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.77/1.97  thf('20', plain,
% 1.77/1.97      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 1.77/1.97          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))
% 1.77/1.97         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.77/1.97      inference('sup+', [status(thm)], ['18', '19'])).
% 1.77/1.97  thf('21', plain, (![X21 : $i]: ((k5_xboole_0 @ X21 @ X21) = (k1_xboole_0))),
% 1.77/1.97      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.77/1.97  thf('22', plain,
% 1.77/1.97      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 1.77/1.97         <= (((r2_hidden @ sk_A @ sk_B)))),
% 1.77/1.97      inference('demod', [status(thm)], ['20', '21'])).
% 1.77/1.97  thf('23', plain,
% 1.77/1.97      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 1.77/1.97         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 1.77/1.97      inference('split', [status(esa)], ['0'])).
% 1.77/1.97  thf('24', plain,
% 1.77/1.97      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.77/1.97         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 1.77/1.97             ((r2_hidden @ sk_A @ sk_B)))),
% 1.77/1.97      inference('sup-', [status(thm)], ['22', '23'])).
% 1.77/1.97  thf('25', plain,
% 1.77/1.97      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 1.77/1.97       ~ ((r2_hidden @ sk_A @ sk_B))),
% 1.77/1.97      inference('simplify', [status(thm)], ['24'])).
% 1.77/1.97  thf('26', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 1.77/1.97      inference('sat_resolution*', [status(thm)], ['2', '25'])).
% 1.77/1.97  thf('27', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 1.77/1.97      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 1.77/1.97  thf('28', plain,
% 1.77/1.97      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 1.77/1.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 1.77/1.97      inference('split', [status(esa)], ['3'])).
% 1.77/1.97  thf(t39_xboole_1, axiom,
% 1.77/1.97    (![A:$i,B:$i]:
% 1.77/1.97     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.77/1.97  thf('29', plain,
% 1.77/1.97      (![X15 : $i, X16 : $i]:
% 1.77/1.97         ((k2_xboole_0 @ X15 @ (k4_xboole_0 @ X16 @ X15))
% 1.77/1.97           = (k2_xboole_0 @ X15 @ X16))),
% 1.77/1.97      inference('cnf', [status(esa)], [t39_xboole_1])).
% 1.77/1.97  thf('30', plain,
% 1.77/1.97      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 1.77/1.97          = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 1.77/1.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 1.77/1.97      inference('sup+', [status(thm)], ['28', '29'])).
% 1.77/1.97  thf(commutativity_k2_tarski, axiom,
% 1.77/1.97    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 1.77/1.97  thf('31', plain,
% 1.77/1.97      (![X24 : $i, X25 : $i]:
% 1.77/1.97         ((k2_tarski @ X25 @ X24) = (k2_tarski @ X24 @ X25))),
% 1.77/1.97      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 1.77/1.97  thf(l51_zfmisc_1, axiom,
% 1.77/1.97    (![A:$i,B:$i]:
% 1.77/1.97     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 1.77/1.97  thf('32', plain,
% 1.77/1.97      (![X69 : $i, X70 : $i]:
% 1.77/1.97         ((k3_tarski @ (k2_tarski @ X69 @ X70)) = (k2_xboole_0 @ X69 @ X70))),
% 1.77/1.97      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.77/1.97  thf('33', plain,
% 1.77/1.97      (![X0 : $i, X1 : $i]:
% 1.77/1.97         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 1.77/1.97      inference('sup+', [status(thm)], ['31', '32'])).
% 1.77/1.97  thf('34', plain,
% 1.77/1.97      (![X69 : $i, X70 : $i]:
% 1.77/1.97         ((k3_tarski @ (k2_tarski @ X69 @ X70)) = (k2_xboole_0 @ X69 @ X70))),
% 1.77/1.97      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 1.77/1.97  thf('35', plain,
% 1.77/1.97      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.77/1.97      inference('sup+', [status(thm)], ['33', '34'])).
% 1.77/1.97  thf('36', plain,
% 1.77/1.97      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 1.77/1.97      inference('sup+', [status(thm)], ['33', '34'])).
% 1.77/1.97  thf(t1_boole, axiom,
% 1.77/1.97    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.77/1.97  thf('37', plain, (![X14 : $i]: ((k2_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.77/1.97      inference('cnf', [status(esa)], [t1_boole])).
% 1.77/1.97  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.77/1.97      inference('sup+', [status(thm)], ['36', '37'])).
% 1.77/1.97  thf('39', plain,
% 1.77/1.97      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 1.77/1.97         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 1.77/1.97      inference('demod', [status(thm)], ['30', '35', '38'])).
% 1.77/1.97  thf('40', plain,
% 1.77/1.97      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 1.77/1.97       ((r2_hidden @ sk_A @ sk_B))),
% 1.77/1.97      inference('split', [status(esa)], ['3'])).
% 1.77/1.97  thf('41', plain,
% 1.77/1.97      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 1.77/1.97      inference('sat_resolution*', [status(thm)], ['2', '25', '40'])).
% 1.77/1.97  thf('42', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 1.77/1.97      inference('simpl_trail', [status(thm)], ['39', '41'])).
% 1.77/1.97  thf(t69_enumset1, axiom,
% 1.77/1.97    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.77/1.97  thf('43', plain,
% 1.77/1.97      (![X38 : $i]: ((k2_tarski @ X38 @ X38) = (k1_tarski @ X38))),
% 1.77/1.97      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.77/1.97  thf(t70_enumset1, axiom,
% 1.77/1.97    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.77/1.97  thf('44', plain,
% 1.77/1.97      (![X39 : $i, X40 : $i]:
% 1.77/1.97         ((k1_enumset1 @ X39 @ X39 @ X40) = (k2_tarski @ X39 @ X40))),
% 1.77/1.97      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.77/1.97  thf(d1_enumset1, axiom,
% 1.77/1.97    (![A:$i,B:$i,C:$i,D:$i]:
% 1.77/1.97     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.77/1.97       ( ![E:$i]:
% 1.77/1.97         ( ( r2_hidden @ E @ D ) <=>
% 1.77/1.97           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.77/1.97  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.77/1.97  thf(zf_stmt_2, axiom,
% 1.77/1.97    (![E:$i,C:$i,B:$i,A:$i]:
% 1.77/1.97     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.77/1.97       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.77/1.97  thf(zf_stmt_3, axiom,
% 1.77/1.97    (![A:$i,B:$i,C:$i,D:$i]:
% 1.77/1.97     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.77/1.97       ( ![E:$i]:
% 1.77/1.97         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.77/1.97  thf('45', plain,
% 1.77/1.97      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 1.77/1.97         ((zip_tseitin_0 @ X31 @ X32 @ X33 @ X34)
% 1.77/1.97          | (r2_hidden @ X31 @ X35)
% 1.77/1.97          | ((X35) != (k1_enumset1 @ X34 @ X33 @ X32)))),
% 1.77/1.97      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.77/1.97  thf('46', plain,
% 1.77/1.97      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.77/1.97         ((r2_hidden @ X31 @ (k1_enumset1 @ X34 @ X33 @ X32))
% 1.77/1.97          | (zip_tseitin_0 @ X31 @ X32 @ X33 @ X34))),
% 1.77/1.97      inference('simplify', [status(thm)], ['45'])).
% 1.77/1.97  thf('47', plain,
% 1.77/1.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.77/1.97         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.77/1.97          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.77/1.97      inference('sup+', [status(thm)], ['44', '46'])).
% 1.77/1.97  thf('48', plain,
% 1.77/1.97      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.77/1.97         (((X27) != (X26)) | ~ (zip_tseitin_0 @ X27 @ X28 @ X29 @ X26))),
% 1.77/1.97      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.77/1.97  thf('49', plain,
% 1.77/1.97      (![X26 : $i, X28 : $i, X29 : $i]:
% 1.77/1.97         ~ (zip_tseitin_0 @ X26 @ X28 @ X29 @ X26)),
% 1.77/1.97      inference('simplify', [status(thm)], ['48'])).
% 1.77/1.97  thf('50', plain,
% 1.77/1.97      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 1.77/1.97      inference('sup-', [status(thm)], ['47', '49'])).
% 1.77/1.97  thf('51', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 1.77/1.97      inference('sup+', [status(thm)], ['43', '50'])).
% 1.77/1.97  thf(d3_xboole_0, axiom,
% 1.77/1.97    (![A:$i,B:$i,C:$i]:
% 1.77/1.97     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 1.77/1.97       ( ![D:$i]:
% 1.77/1.97         ( ( r2_hidden @ D @ C ) <=>
% 1.77/1.97           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.77/1.97  thf('52', plain,
% 1.77/1.97      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 1.77/1.97         (~ (r2_hidden @ X2 @ X3)
% 1.77/1.97          | (r2_hidden @ X2 @ X4)
% 1.77/1.97          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 1.77/1.97      inference('cnf', [status(esa)], [d3_xboole_0])).
% 1.77/1.97  thf('53', plain,
% 1.77/1.97      (![X2 : $i, X3 : $i, X5 : $i]:
% 1.77/1.97         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 1.77/1.97      inference('simplify', [status(thm)], ['52'])).
% 1.77/1.97  thf('54', plain,
% 1.77/1.97      (![X0 : $i, X1 : $i]:
% 1.77/1.97         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 1.77/1.97      inference('sup-', [status(thm)], ['51', '53'])).
% 1.77/1.97  thf('55', plain, ((r2_hidden @ sk_A @ sk_B)),
% 1.77/1.97      inference('sup+', [status(thm)], ['42', '54'])).
% 1.77/1.97  thf('56', plain, ($false), inference('demod', [status(thm)], ['27', '55'])).
% 1.77/1.97  
% 1.77/1.97  % SZS output end Refutation
% 1.77/1.97  
% 1.83/1.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
