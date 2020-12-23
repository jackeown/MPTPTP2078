%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OIwBBdCorL

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:21 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 158 expanded)
%              Number of leaves         :   34 (  58 expanded)
%              Depth                    :   15
%              Number of atoms          :  638 (1195 expanded)
%              Number of equality atoms :   71 ( 135 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

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
    ! [X65: $i,X67: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X65 ) @ X67 )
      | ~ ( r2_hidden @ X65 @ X67 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( ( k2_xboole_0 @ X12 @ X11 )
        = X11 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X21 @ X22 ) @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X17 @ X18 ) @ X19 )
      = ( k5_xboole_0 @ X17 @ ( k5_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('11',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k3_xboole_0 @ X21 @ X22 )
      = ( k5_xboole_0 @ X21 @ ( k5_xboole_0 @ X22 @ ( k2_xboole_0 @ X21 @ X22 ) ) ) ) ),
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
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
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
    ! [X16: $i] :
      ( ( k5_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X20: $i] :
      ( ( k5_xboole_0 @ X20 @ X20 )
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
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) )
      = ( k2_xboole_0 @ X14 @ X15 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X24 @ X23 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('32',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X68 @ X69 ) )
      = ( k2_xboole_0 @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X68: $i,X69: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X68 @ X69 ) )
      = ( k2_xboole_0 @ X68 @ X69 ) ) ),
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
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
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
    ! [X37: $i] :
      ( ( k2_tarski @ X37 @ X37 )
      = ( k1_tarski @ X37 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('44',plain,(
    ! [X38: $i,X39: $i] :
      ( ( k1_enumset1 @ X38 @ X38 @ X39 )
      = ( k2_tarski @ X38 @ X39 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 )
      | ( r2_hidden @ X30 @ X34 )
      | ( X34
       != ( k1_enumset1 @ X33 @ X32 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r2_hidden @ X30 @ ( k1_enumset1 @ X33 @ X32 @ X31 ) )
      | ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X33 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X26 != X25 )
      | ~ ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('49',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ~ ( zip_tseitin_0 @ X25 @ X27 @ X28 @ X25 ) ),
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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.OIwBBdCorL
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:07:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.09  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.09  % Solved by: fo/fo7.sh
% 0.91/1.09  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.09  % done 836 iterations in 0.635s
% 0.91/1.09  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.09  % SZS output start Refutation
% 0.91/1.09  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.91/1.09  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.91/1.09  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.91/1.09  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.91/1.09  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.09  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.91/1.09  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.09  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.09  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.09  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.09  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.09  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.91/1.09  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.91/1.09  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.91/1.09  thf(t68_zfmisc_1, conjecture,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.91/1.09       ( r2_hidden @ A @ B ) ))).
% 0.91/1.09  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.09    (~( ![A:$i,B:$i]:
% 0.91/1.09        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.91/1.09          ( r2_hidden @ A @ B ) ) )),
% 0.91/1.09    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 0.91/1.09  thf('0', plain,
% 0.91/1.09      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.91/1.09        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('1', plain,
% 0.91/1.09      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.09      inference('split', [status(esa)], ['0'])).
% 0.91/1.09  thf('2', plain,
% 0.91/1.09      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.91/1.09       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.91/1.09      inference('split', [status(esa)], ['0'])).
% 0.91/1.09  thf('3', plain,
% 0.91/1.09      (((r2_hidden @ sk_A @ sk_B)
% 0.91/1.09        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.09  thf('4', plain,
% 0.91/1.09      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.09      inference('split', [status(esa)], ['3'])).
% 0.91/1.09  thf(l1_zfmisc_1, axiom,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.91/1.09  thf('5', plain,
% 0.91/1.09      (![X65 : $i, X67 : $i]:
% 0.91/1.09         ((r1_tarski @ (k1_tarski @ X65) @ X67) | ~ (r2_hidden @ X65 @ X67))),
% 0.91/1.09      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.91/1.09  thf('6', plain,
% 0.91/1.09      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 0.91/1.09         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['4', '5'])).
% 0.91/1.09  thf(t12_xboole_1, axiom,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.91/1.09  thf('7', plain,
% 0.91/1.09      (![X11 : $i, X12 : $i]:
% 0.91/1.09         (((k2_xboole_0 @ X12 @ X11) = (X11)) | ~ (r1_tarski @ X12 @ X11))),
% 0.91/1.09      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.91/1.09  thf('8', plain,
% 0.91/1.09      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B)))
% 0.91/1.09         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['6', '7'])).
% 0.91/1.09  thf(t95_xboole_1, axiom,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( k3_xboole_0 @ A @ B ) =
% 0.91/1.09       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.91/1.09  thf('9', plain,
% 0.91/1.09      (![X21 : $i, X22 : $i]:
% 0.91/1.09         ((k3_xboole_0 @ X21 @ X22)
% 0.91/1.09           = (k5_xboole_0 @ (k5_xboole_0 @ X21 @ X22) @ 
% 0.91/1.09              (k2_xboole_0 @ X21 @ X22)))),
% 0.91/1.09      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.91/1.09  thf(t91_xboole_1, axiom,
% 0.91/1.09    (![A:$i,B:$i,C:$i]:
% 0.91/1.09     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.91/1.09       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.91/1.09  thf('10', plain,
% 0.91/1.09      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.91/1.09         ((k5_xboole_0 @ (k5_xboole_0 @ X17 @ X18) @ X19)
% 0.91/1.09           = (k5_xboole_0 @ X17 @ (k5_xboole_0 @ X18 @ X19)))),
% 0.91/1.09      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.91/1.09  thf('11', plain,
% 0.91/1.09      (![X21 : $i, X22 : $i]:
% 0.91/1.09         ((k3_xboole_0 @ X21 @ X22)
% 0.91/1.09           = (k5_xboole_0 @ X21 @ 
% 0.91/1.09              (k5_xboole_0 @ X22 @ (k2_xboole_0 @ X21 @ X22))))),
% 0.91/1.09      inference('demod', [status(thm)], ['9', '10'])).
% 0.91/1.09  thf('12', plain,
% 0.91/1.09      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.91/1.09          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k5_xboole_0 @ sk_B @ sk_B))))
% 0.91/1.09         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.09      inference('sup+', [status(thm)], ['8', '11'])).
% 0.91/1.09  thf(t92_xboole_1, axiom,
% 0.91/1.09    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.91/1.09  thf('13', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.91/1.09      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.91/1.09  thf(commutativity_k5_xboole_0, axiom,
% 0.91/1.09    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.91/1.09  thf('14', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.91/1.09      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.09  thf('15', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.91/1.09      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.91/1.09  thf(t5_boole, axiom,
% 0.91/1.09    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.91/1.09  thf('16', plain, (![X16 : $i]: ((k5_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 0.91/1.09      inference('cnf', [status(esa)], [t5_boole])).
% 0.91/1.09  thf('17', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.09      inference('sup+', [status(thm)], ['15', '16'])).
% 0.91/1.09  thf('18', plain,
% 0.91/1.09      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.91/1.09         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.09      inference('demod', [status(thm)], ['12', '13', '14', '17'])).
% 0.91/1.09  thf(t100_xboole_1, axiom,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.91/1.09  thf('19', plain,
% 0.91/1.09      (![X9 : $i, X10 : $i]:
% 0.91/1.09         ((k4_xboole_0 @ X9 @ X10)
% 0.91/1.09           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.91/1.09      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.91/1.09  thf('20', plain,
% 0.91/1.09      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.91/1.09          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))
% 0.91/1.09         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.09      inference('sup+', [status(thm)], ['18', '19'])).
% 0.91/1.09  thf('21', plain, (![X20 : $i]: ((k5_xboole_0 @ X20 @ X20) = (k1_xboole_0))),
% 0.91/1.09      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.91/1.09  thf('22', plain,
% 0.91/1.09      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.91/1.09         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.09      inference('demod', [status(thm)], ['20', '21'])).
% 0.91/1.09  thf('23', plain,
% 0.91/1.09      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 0.91/1.09         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.91/1.09      inference('split', [status(esa)], ['0'])).
% 0.91/1.09  thf('24', plain,
% 0.91/1.09      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.91/1.09         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 0.91/1.09             ((r2_hidden @ sk_A @ sk_B)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['22', '23'])).
% 0.91/1.09  thf('25', plain,
% 0.91/1.09      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.91/1.09       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.91/1.09      inference('simplify', [status(thm)], ['24'])).
% 0.91/1.09  thf('26', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.91/1.09      inference('sat_resolution*', [status(thm)], ['2', '25'])).
% 0.91/1.09  thf('27', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.91/1.09      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 0.91/1.09  thf('28', plain,
% 0.91/1.09      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.91/1.09         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.91/1.09      inference('split', [status(esa)], ['3'])).
% 0.91/1.09  thf(t39_xboole_1, axiom,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.91/1.09  thf('29', plain,
% 0.91/1.09      (![X14 : $i, X15 : $i]:
% 0.91/1.09         ((k2_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14))
% 0.91/1.09           = (k2_xboole_0 @ X14 @ X15))),
% 0.91/1.09      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.91/1.09  thf('30', plain,
% 0.91/1.09      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.91/1.09          = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.91/1.09         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.91/1.09      inference('sup+', [status(thm)], ['28', '29'])).
% 0.91/1.09  thf(commutativity_k2_tarski, axiom,
% 0.91/1.09    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.91/1.09  thf('31', plain,
% 0.91/1.09      (![X23 : $i, X24 : $i]:
% 0.91/1.09         ((k2_tarski @ X24 @ X23) = (k2_tarski @ X23 @ X24))),
% 0.91/1.09      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.91/1.09  thf(l51_zfmisc_1, axiom,
% 0.91/1.09    (![A:$i,B:$i]:
% 0.91/1.09     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.91/1.09  thf('32', plain,
% 0.91/1.09      (![X68 : $i, X69 : $i]:
% 0.91/1.09         ((k3_tarski @ (k2_tarski @ X68 @ X69)) = (k2_xboole_0 @ X68 @ X69))),
% 0.91/1.09      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.91/1.09  thf('33', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.09      inference('sup+', [status(thm)], ['31', '32'])).
% 0.91/1.09  thf('34', plain,
% 0.91/1.09      (![X68 : $i, X69 : $i]:
% 0.91/1.09         ((k3_tarski @ (k2_tarski @ X68 @ X69)) = (k2_xboole_0 @ X68 @ X69))),
% 0.91/1.09      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.91/1.09  thf('35', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.09      inference('sup+', [status(thm)], ['33', '34'])).
% 0.91/1.09  thf('36', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.91/1.09      inference('sup+', [status(thm)], ['33', '34'])).
% 0.91/1.09  thf(t1_boole, axiom,
% 0.91/1.09    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.91/1.09  thf('37', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.91/1.09      inference('cnf', [status(esa)], [t1_boole])).
% 0.91/1.09  thf('38', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.91/1.09      inference('sup+', [status(thm)], ['36', '37'])).
% 0.91/1.09  thf('39', plain,
% 0.91/1.09      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.91/1.09         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.91/1.09      inference('demod', [status(thm)], ['30', '35', '38'])).
% 0.91/1.09  thf('40', plain,
% 0.91/1.09      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.91/1.09       ((r2_hidden @ sk_A @ sk_B))),
% 0.91/1.09      inference('split', [status(esa)], ['3'])).
% 0.91/1.09  thf('41', plain,
% 0.91/1.09      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.91/1.09      inference('sat_resolution*', [status(thm)], ['2', '25', '40'])).
% 0.91/1.09  thf('42', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.91/1.09      inference('simpl_trail', [status(thm)], ['39', '41'])).
% 0.91/1.09  thf(t69_enumset1, axiom,
% 0.91/1.09    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.91/1.09  thf('43', plain,
% 0.91/1.09      (![X37 : $i]: ((k2_tarski @ X37 @ X37) = (k1_tarski @ X37))),
% 0.91/1.09      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.91/1.09  thf(t70_enumset1, axiom,
% 0.91/1.09    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.91/1.09  thf('44', plain,
% 0.91/1.09      (![X38 : $i, X39 : $i]:
% 0.91/1.09         ((k1_enumset1 @ X38 @ X38 @ X39) = (k2_tarski @ X38 @ X39))),
% 0.91/1.09      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.91/1.09  thf(d1_enumset1, axiom,
% 0.91/1.09    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.09     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.91/1.09       ( ![E:$i]:
% 0.91/1.09         ( ( r2_hidden @ E @ D ) <=>
% 0.91/1.09           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.91/1.09  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.91/1.09  thf(zf_stmt_2, axiom,
% 0.91/1.09    (![E:$i,C:$i,B:$i,A:$i]:
% 0.91/1.09     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.91/1.09       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.91/1.09  thf(zf_stmt_3, axiom,
% 0.91/1.09    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.09     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.91/1.09       ( ![E:$i]:
% 0.91/1.09         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.91/1.09  thf('45', plain,
% 0.91/1.09      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.91/1.09         ((zip_tseitin_0 @ X30 @ X31 @ X32 @ X33)
% 0.91/1.09          | (r2_hidden @ X30 @ X34)
% 0.91/1.09          | ((X34) != (k1_enumset1 @ X33 @ X32 @ X31)))),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.91/1.09  thf('46', plain,
% 0.91/1.09      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.91/1.09         ((r2_hidden @ X30 @ (k1_enumset1 @ X33 @ X32 @ X31))
% 0.91/1.09          | (zip_tseitin_0 @ X30 @ X31 @ X32 @ X33))),
% 0.91/1.09      inference('simplify', [status(thm)], ['45'])).
% 0.91/1.09  thf('47', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.09         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.91/1.09          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.91/1.09      inference('sup+', [status(thm)], ['44', '46'])).
% 0.91/1.09  thf('48', plain,
% 0.91/1.09      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.91/1.09         (((X26) != (X25)) | ~ (zip_tseitin_0 @ X26 @ X27 @ X28 @ X25))),
% 0.91/1.09      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.91/1.09  thf('49', plain,
% 0.91/1.09      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.91/1.09         ~ (zip_tseitin_0 @ X25 @ X27 @ X28 @ X25)),
% 0.91/1.09      inference('simplify', [status(thm)], ['48'])).
% 0.91/1.09  thf('50', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.91/1.09      inference('sup-', [status(thm)], ['47', '49'])).
% 0.91/1.09  thf('51', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.91/1.09      inference('sup+', [status(thm)], ['43', '50'])).
% 0.91/1.09  thf(d3_xboole_0, axiom,
% 0.91/1.09    (![A:$i,B:$i,C:$i]:
% 0.91/1.09     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.91/1.09       ( ![D:$i]:
% 0.91/1.09         ( ( r2_hidden @ D @ C ) <=>
% 0.91/1.09           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.91/1.09  thf('52', plain,
% 0.91/1.09      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.91/1.09         (~ (r2_hidden @ X2 @ X3)
% 0.91/1.09          | (r2_hidden @ X2 @ X4)
% 0.91/1.09          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 0.91/1.09      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.91/1.09  thf('53', plain,
% 0.91/1.09      (![X2 : $i, X3 : $i, X5 : $i]:
% 0.91/1.09         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 0.91/1.09      inference('simplify', [status(thm)], ['52'])).
% 0.91/1.09  thf('54', plain,
% 0.91/1.09      (![X0 : $i, X1 : $i]:
% 0.91/1.09         (r2_hidden @ X0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))),
% 0.91/1.09      inference('sup-', [status(thm)], ['51', '53'])).
% 0.91/1.09  thf('55', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.91/1.09      inference('sup+', [status(thm)], ['42', '54'])).
% 0.91/1.09  thf('56', plain, ($false), inference('demod', [status(thm)], ['27', '55'])).
% 0.91/1.09  
% 0.91/1.09  % SZS output end Refutation
% 0.91/1.09  
% 0.91/1.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
