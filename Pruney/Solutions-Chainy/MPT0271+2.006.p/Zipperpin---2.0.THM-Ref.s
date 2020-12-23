%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mOqG5CJfmj

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:21 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 262 expanded)
%              Number of leaves         :   32 (  90 expanded)
%              Depth                    :   19
%              Number of atoms          :  760 (2129 expanded)
%              Number of equality atoms :   77 ( 238 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

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
    ! [X63: $i,X65: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X63 ) @ X65 )
      | ~ ( r2_hidden @ X63 @ X65 ) ) ),
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
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
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
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('11',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ) ),
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
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
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
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
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
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('20',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
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

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X35: $i] :
      ( ( k2_tarski @ X35 @ X35 )
      = ( k1_tarski @ X35 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X36: $i,X37: $i] :
      ( ( k1_enumset1 @ X36 @ X36 @ X37 )
      = ( k2_tarski @ X36 @ X37 ) ) ),
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

thf('30',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 )
      | ( r2_hidden @ X28 @ X32 )
      | ( X32
       != ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X28 @ ( k1_enumset1 @ X31 @ X30 @ X29 ) )
      | ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X24 != X23 )
      | ~ ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ~ ( zip_tseitin_0 @ X23 @ X25 @ X26 @ X23 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('37',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['3'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('39',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('40',plain,(
    ! [X11: $i] :
      ( ( k2_xboole_0 @ X11 @ k1_xboole_0 )
      = X11 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('41',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k3_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ ( k2_xboole_0 @ X19 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('43',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('45',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('46',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['43','44','49'])).

thf('51',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['3'])).

thf('52',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['2','25','51'])).

thf('53',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['50','52'])).

thf('54',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('55',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('57',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('58',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('61',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( r2_hidden @ X3 @ ( k5_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('63',plain,(
    ! [X69: $i,X70: $i,X71: $i] :
      ( ( r2_hidden @ X69 @ X70 )
      | ~ ( r2_hidden @ X69 @ ( k4_xboole_0 @ X70 @ ( k1_tarski @ X71 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['59','64'])).

thf('66',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['36','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['27','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.mOqG5CJfmj
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.76/0.93  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.76/0.93  % Solved by: fo/fo7.sh
% 0.76/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.93  % done 874 iterations in 0.477s
% 0.76/0.93  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.76/0.93  % SZS output start Refutation
% 0.76/0.93  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.76/0.93  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.93  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.76/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.93  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.76/0.93  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.76/0.93  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.93  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.76/0.93  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.76/0.93  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.76/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.93  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.76/0.93  thf(t68_zfmisc_1, conjecture,
% 0.76/0.93    (![A:$i,B:$i]:
% 0.76/0.93     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.76/0.93       ( r2_hidden @ A @ B ) ))).
% 0.76/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.93    (~( ![A:$i,B:$i]:
% 0.76/0.93        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.76/0.93          ( r2_hidden @ A @ B ) ) )),
% 0.76/0.93    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 0.76/0.93  thf('0', plain,
% 0.76/0.93      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.76/0.93        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 0.76/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.93  thf('1', plain,
% 0.76/0.93      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.76/0.93      inference('split', [status(esa)], ['0'])).
% 0.76/0.93  thf('2', plain,
% 0.76/0.93      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.76/0.93       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.76/0.93      inference('split', [status(esa)], ['0'])).
% 0.76/0.93  thf('3', plain,
% 0.76/0.93      (((r2_hidden @ sk_A @ sk_B)
% 0.76/0.93        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.76/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.93  thf('4', plain,
% 0.76/0.93      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.76/0.93      inference('split', [status(esa)], ['3'])).
% 0.76/0.93  thf(l1_zfmisc_1, axiom,
% 0.76/0.93    (![A:$i,B:$i]:
% 0.76/0.93     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.76/0.93  thf('5', plain,
% 0.76/0.93      (![X63 : $i, X65 : $i]:
% 0.76/0.93         ((r1_tarski @ (k1_tarski @ X63) @ X65) | ~ (r2_hidden @ X63 @ X65))),
% 0.76/0.93      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.76/0.93  thf('6', plain,
% 0.76/0.93      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 0.76/0.93         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.76/0.93      inference('sup-', [status(thm)], ['4', '5'])).
% 0.76/0.93  thf(t12_xboole_1, axiom,
% 0.76/0.93    (![A:$i,B:$i]:
% 0.76/0.93     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.76/0.93  thf('7', plain,
% 0.76/0.93      (![X9 : $i, X10 : $i]:
% 0.76/0.93         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.76/0.93      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.76/0.93  thf('8', plain,
% 0.76/0.93      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B)))
% 0.76/0.93         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.76/0.93      inference('sup-', [status(thm)], ['6', '7'])).
% 0.76/0.93  thf(t95_xboole_1, axiom,
% 0.76/0.93    (![A:$i,B:$i]:
% 0.76/0.93     ( ( k3_xboole_0 @ A @ B ) =
% 0.76/0.93       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.76/0.93  thf('9', plain,
% 0.76/0.93      (![X19 : $i, X20 : $i]:
% 0.76/0.93         ((k3_xboole_0 @ X19 @ X20)
% 0.76/0.93           = (k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ 
% 0.76/0.93              (k2_xboole_0 @ X19 @ X20)))),
% 0.76/0.93      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.76/0.93  thf(t91_xboole_1, axiom,
% 0.76/0.93    (![A:$i,B:$i,C:$i]:
% 0.76/0.93     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 0.76/0.93       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 0.76/0.93  thf('10', plain,
% 0.76/0.93      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.76/0.93         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.76/0.93           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.76/0.93      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.76/0.93  thf('11', plain,
% 0.76/0.93      (![X19 : $i, X20 : $i]:
% 0.76/0.93         ((k3_xboole_0 @ X19 @ X20)
% 0.76/0.93           = (k5_xboole_0 @ X19 @ 
% 0.76/0.93              (k5_xboole_0 @ X20 @ (k2_xboole_0 @ X19 @ X20))))),
% 0.76/0.93      inference('demod', [status(thm)], ['9', '10'])).
% 0.76/0.93  thf('12', plain,
% 0.76/0.93      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.76/0.93          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k5_xboole_0 @ sk_B @ sk_B))))
% 0.76/0.93         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.76/0.93      inference('sup+', [status(thm)], ['8', '11'])).
% 0.76/0.93  thf(t92_xboole_1, axiom,
% 0.76/0.93    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.76/0.93  thf('13', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.76/0.93      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.76/0.93  thf(commutativity_k5_xboole_0, axiom,
% 0.76/0.93    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.76/0.93  thf('14', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.76/0.93      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.76/0.93  thf('15', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.76/0.93      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.76/0.93  thf(t5_boole, axiom,
% 0.76/0.93    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.76/0.93  thf('16', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 0.76/0.93      inference('cnf', [status(esa)], [t5_boole])).
% 0.76/0.93  thf('17', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.76/0.93      inference('sup+', [status(thm)], ['15', '16'])).
% 0.76/0.93  thf('18', plain,
% 0.76/0.93      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.76/0.93         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.76/0.93      inference('demod', [status(thm)], ['12', '13', '14', '17'])).
% 0.76/0.93  thf(t100_xboole_1, axiom,
% 0.76/0.93    (![A:$i,B:$i]:
% 0.76/0.93     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.76/0.93  thf('19', plain,
% 0.76/0.93      (![X7 : $i, X8 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X7 @ X8)
% 0.76/0.93           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.76/0.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.76/0.93  thf('20', plain,
% 0.76/0.93      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 0.76/0.93          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))
% 0.76/0.93         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.76/0.93      inference('sup+', [status(thm)], ['18', '19'])).
% 0.76/0.93  thf('21', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.76/0.93      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.76/0.93  thf('22', plain,
% 0.76/0.93      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.76/0.93         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.76/0.93      inference('demod', [status(thm)], ['20', '21'])).
% 0.76/0.93  thf('23', plain,
% 0.76/0.93      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 0.76/0.93         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.76/0.93      inference('split', [status(esa)], ['0'])).
% 0.76/0.93  thf('24', plain,
% 0.76/0.93      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.76/0.93         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 0.76/0.93             ((r2_hidden @ sk_A @ sk_B)))),
% 0.76/0.93      inference('sup-', [status(thm)], ['22', '23'])).
% 0.76/0.93  thf('25', plain,
% 0.76/0.93      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.76/0.93       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.76/0.93      inference('simplify', [status(thm)], ['24'])).
% 0.76/0.93  thf('26', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.76/0.93      inference('sat_resolution*', [status(thm)], ['2', '25'])).
% 0.76/0.93  thf('27', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.76/0.93      inference('simpl_trail', [status(thm)], ['1', '26'])).
% 0.76/0.93  thf(t69_enumset1, axiom,
% 0.76/0.93    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.76/0.93  thf('28', plain,
% 0.76/0.93      (![X35 : $i]: ((k2_tarski @ X35 @ X35) = (k1_tarski @ X35))),
% 0.76/0.93      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.76/0.93  thf(t70_enumset1, axiom,
% 0.76/0.93    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.76/0.93  thf('29', plain,
% 0.76/0.93      (![X36 : $i, X37 : $i]:
% 0.76/0.93         ((k1_enumset1 @ X36 @ X36 @ X37) = (k2_tarski @ X36 @ X37))),
% 0.76/0.93      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.76/0.93  thf(d1_enumset1, axiom,
% 0.76/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.93     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.76/0.93       ( ![E:$i]:
% 0.76/0.93         ( ( r2_hidden @ E @ D ) <=>
% 0.76/0.93           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.76/0.93  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.76/0.93  thf(zf_stmt_2, axiom,
% 0.76/0.93    (![E:$i,C:$i,B:$i,A:$i]:
% 0.76/0.93     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.76/0.93       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.76/0.93  thf(zf_stmt_3, axiom,
% 0.76/0.93    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.93     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.76/0.93       ( ![E:$i]:
% 0.76/0.93         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.76/0.93  thf('30', plain,
% 0.76/0.93      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.76/0.93         ((zip_tseitin_0 @ X28 @ X29 @ X30 @ X31)
% 0.76/0.93          | (r2_hidden @ X28 @ X32)
% 0.76/0.93          | ((X32) != (k1_enumset1 @ X31 @ X30 @ X29)))),
% 0.76/0.93      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.76/0.93  thf('31', plain,
% 0.76/0.93      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.76/0.93         ((r2_hidden @ X28 @ (k1_enumset1 @ X31 @ X30 @ X29))
% 0.76/0.93          | (zip_tseitin_0 @ X28 @ X29 @ X30 @ X31))),
% 0.76/0.93      inference('simplify', [status(thm)], ['30'])).
% 0.76/0.93  thf('32', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.93         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.76/0.93          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.76/0.93      inference('sup+', [status(thm)], ['29', '31'])).
% 0.76/0.93  thf('33', plain,
% 0.76/0.93      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.76/0.93         (((X24) != (X23)) | ~ (zip_tseitin_0 @ X24 @ X25 @ X26 @ X23))),
% 0.76/0.93      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/0.93  thf('34', plain,
% 0.76/0.93      (![X23 : $i, X25 : $i, X26 : $i]:
% 0.76/0.93         ~ (zip_tseitin_0 @ X23 @ X25 @ X26 @ X23)),
% 0.76/0.93      inference('simplify', [status(thm)], ['33'])).
% 0.76/0.93  thf('35', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.76/0.93      inference('sup-', [status(thm)], ['32', '34'])).
% 0.76/0.93  thf('36', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.76/0.93      inference('sup+', [status(thm)], ['28', '35'])).
% 0.76/0.93  thf('37', plain,
% 0.76/0.93      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 0.76/0.93         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.76/0.93      inference('split', [status(esa)], ['3'])).
% 0.76/0.93  thf(t39_xboole_1, axiom,
% 0.76/0.93    (![A:$i,B:$i]:
% 0.76/0.93     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.76/0.93  thf('38', plain,
% 0.76/0.93      (![X12 : $i, X13 : $i]:
% 0.76/0.93         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.76/0.93           = (k2_xboole_0 @ X12 @ X13))),
% 0.76/0.93      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.76/0.93  thf('39', plain,
% 0.76/0.93      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 0.76/0.93          = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.76/0.93         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.76/0.93      inference('sup+', [status(thm)], ['37', '38'])).
% 0.76/0.93  thf(t1_boole, axiom,
% 0.76/0.93    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.76/0.93  thf('40', plain, (![X11 : $i]: ((k2_xboole_0 @ X11 @ k1_xboole_0) = (X11))),
% 0.76/0.93      inference('cnf', [status(esa)], [t1_boole])).
% 0.76/0.93  thf('41', plain,
% 0.76/0.93      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 0.76/0.93         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.76/0.93      inference('demod', [status(thm)], ['39', '40'])).
% 0.76/0.93  thf('42', plain,
% 0.76/0.93      (![X19 : $i, X20 : $i]:
% 0.76/0.93         ((k3_xboole_0 @ X19 @ X20)
% 0.76/0.93           = (k5_xboole_0 @ X19 @ 
% 0.76/0.93              (k5_xboole_0 @ X20 @ (k2_xboole_0 @ X19 @ X20))))),
% 0.76/0.93      inference('demod', [status(thm)], ['9', '10'])).
% 0.76/0.93  thf('43', plain,
% 0.76/0.93      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.76/0.93          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))
% 0.76/0.93         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.76/0.93      inference('sup+', [status(thm)], ['41', '42'])).
% 0.76/0.93  thf('44', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.76/0.93      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.76/0.93  thf('45', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 0.76/0.93      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.76/0.93  thf('46', plain,
% 0.76/0.93      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.76/0.93         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 0.76/0.93           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 0.76/0.93      inference('cnf', [status(esa)], [t91_xboole_1])).
% 0.76/0.93  thf('47', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 0.76/0.93           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.76/0.93      inference('sup+', [status(thm)], ['45', '46'])).
% 0.76/0.93  thf('48', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.76/0.93      inference('sup+', [status(thm)], ['15', '16'])).
% 0.76/0.93  thf('49', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.76/0.93      inference('demod', [status(thm)], ['47', '48'])).
% 0.76/0.93  thf('50', plain,
% 0.76/0.93      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 0.76/0.93         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 0.76/0.93      inference('demod', [status(thm)], ['43', '44', '49'])).
% 0.76/0.93  thf('51', plain,
% 0.76/0.93      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 0.76/0.93       ((r2_hidden @ sk_A @ sk_B))),
% 0.76/0.93      inference('split', [status(esa)], ['3'])).
% 0.76/0.93  thf('52', plain,
% 0.76/0.93      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 0.76/0.93      inference('sat_resolution*', [status(thm)], ['2', '25', '51'])).
% 0.76/0.93  thf('53', plain,
% 0.76/0.93      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.76/0.93      inference('simpl_trail', [status(thm)], ['50', '52'])).
% 0.76/0.93  thf('54', plain,
% 0.76/0.93      (![X7 : $i, X8 : $i]:
% 0.76/0.93         ((k4_xboole_0 @ X7 @ X8)
% 0.76/0.93           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.76/0.93      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.76/0.93  thf('55', plain,
% 0.76/0.93      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.76/0.93         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.76/0.93      inference('sup+', [status(thm)], ['53', '54'])).
% 0.76/0.93  thf('56', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 0.76/0.93      inference('demod', [status(thm)], ['47', '48'])).
% 0.76/0.93  thf('57', plain,
% 0.76/0.93      (((k1_tarski @ sk_A)
% 0.76/0.93         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.76/0.93      inference('sup+', [status(thm)], ['55', '56'])).
% 0.76/0.93  thf(t1_xboole_0, axiom,
% 0.76/0.93    (![A:$i,B:$i,C:$i]:
% 0.76/0.93     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 0.76/0.93       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 0.76/0.93  thf('58', plain,
% 0.76/0.93      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.76/0.93         ((r2_hidden @ X3 @ X4)
% 0.76/0.93          | (r2_hidden @ X3 @ X5)
% 0.76/0.93          | ~ (r2_hidden @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 0.76/0.93      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.76/0.93  thf('59', plain,
% 0.76/0.93      (![X0 : $i]:
% 0.76/0.93         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.76/0.93          | (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.76/0.93          | (r2_hidden @ X0 @ sk_B))),
% 0.76/0.93      inference('sup-', [status(thm)], ['57', '58'])).
% 0.76/0.93  thf('60', plain,
% 0.76/0.93      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 0.76/0.93         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.76/0.93      inference('sup+', [status(thm)], ['53', '54'])).
% 0.76/0.93  thf('61', plain,
% 0.76/0.93      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.76/0.93         (~ (r2_hidden @ X3 @ X4)
% 0.76/0.93          | ~ (r2_hidden @ X3 @ X5)
% 0.76/0.93          | ~ (r2_hidden @ X3 @ (k5_xboole_0 @ X4 @ X5)))),
% 0.76/0.93      inference('cnf', [status(esa)], [t1_xboole_0])).
% 0.76/0.93  thf('62', plain,
% 0.76/0.93      (![X0 : $i]:
% 0.76/0.93         (~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.76/0.93          | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.76/0.93          | ~ (r2_hidden @ X0 @ sk_B))),
% 0.76/0.93      inference('sup-', [status(thm)], ['60', '61'])).
% 0.76/0.93  thf(t64_zfmisc_1, axiom,
% 0.76/0.93    (![A:$i,B:$i,C:$i]:
% 0.76/0.93     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.76/0.93       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.76/0.93  thf('63', plain,
% 0.76/0.93      (![X69 : $i, X70 : $i, X71 : $i]:
% 0.76/0.93         ((r2_hidden @ X69 @ X70)
% 0.76/0.93          | ~ (r2_hidden @ X69 @ (k4_xboole_0 @ X70 @ (k1_tarski @ X71))))),
% 0.76/0.93      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.76/0.93  thf('64', plain,
% 0.76/0.93      (![X0 : $i]:
% 0.76/0.93         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.76/0.93          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 0.76/0.93      inference('clc', [status(thm)], ['62', '63'])).
% 0.76/0.93  thf('65', plain,
% 0.76/0.93      (![X0 : $i]:
% 0.76/0.93         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A)))),
% 0.76/0.93      inference('clc', [status(thm)], ['59', '64'])).
% 0.76/0.93  thf('66', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.76/0.93      inference('sup-', [status(thm)], ['36', '65'])).
% 0.76/0.93  thf('67', plain, ($false), inference('demod', [status(thm)], ['27', '66'])).
% 0.76/0.93  
% 0.76/0.93  % SZS output end Refutation
% 0.76/0.93  
% 0.78/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
