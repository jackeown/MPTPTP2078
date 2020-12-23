%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2NSvzCcGFO

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:20 EST 2020

% Result     : Theorem 3.26s
% Output     : Refutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  172 (1844 expanded)
%              Number of leaves         :   37 ( 580 expanded)
%              Depth                    :   29
%              Number of atoms          : 1377 (15935 expanded)
%              Number of equality atoms :  141 (1717 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
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

thf(zf_stmt_0,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X32 )
      | ( X29 = X30 )
      | ( X29 = X31 )
      | ( X29 = X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i,X7: $i] :
      ( ( X7
        = ( k2_xboole_0 @ X5 @ X3 ) )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X3 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X7 @ X3 @ X5 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t1_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) )
    <=> ~ ( ( r2_hidden @ A @ B )
        <=> ( r2_hidden @ A @ C ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X1
        = ( k2_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('10',plain,(
    ! [X17: $i] :
      ( ( k2_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X1 = X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['7'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('15',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X38 @ X37 )
      | ~ ( zip_tseitin_0 @ X38 @ X34 @ X35 @ X36 )
      | ( X37
       != ( k1_enumset1 @ X36 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('17',plain,(
    ! [X34: $i,X35: $i,X36: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X34 @ X35 @ X36 )
      | ~ ( r2_hidden @ X38 @ ( k1_enumset1 @ X36 @ X35 @ X34 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ ( sk_D @ ( k1_tarski @ X0 ) @ k1_xboole_0 @ k1_xboole_0 ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ k1_xboole_0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t68_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = k1_xboole_0 )
      <=> ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t68_zfmisc_1])).

thf('26',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k2_xboole_0 @ X18 @ ( k4_xboole_0 @ X19 @ X18 ) )
      = ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('29',plain,
    ( ( ( k2_xboole_0 @ sk_B @ k1_xboole_0 )
      = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('30',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k2_tarski @ X27 @ X26 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X71: $i,X72: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X71 @ X72 ) )
      = ( k2_xboole_0 @ X71 @ X72 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X71: $i,X72: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X71 @ X72 ) )
      = ( k2_xboole_0 @ X71 @ X72 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('36',plain,(
    ! [X17: $i] :
      ( ( k2_xboole_0 @ X17 @ k1_xboole_0 )
      = X17 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','34','37'])).

thf('39',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('41',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('42',plain,(
    ! [X68: $i,X70: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X68 ) @ X70 )
      | ~ ( r2_hidden @ X68 @ X70 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('43',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_xboole_0 @ X16 @ X15 )
        = X15 )
      | ~ ( r1_tarski @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('45',plain,
    ( ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('46',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X24 @ X25 ) @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('47',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('48',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k5_xboole_0 @ sk_B @ sk_B ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('52',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('54',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X20 @ X21 ) @ X22 )
      = ( k5_xboole_0 @ X20 @ ( k5_xboole_0 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k2_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('58',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ X8 )
      = X8 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('59',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('60',plain,(
    ! [X73: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X73 ) )
      = X73 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X71: $i,X72: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X71 @ X72 ) )
      = ( k2_xboole_0 @ X71 @ X72 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58','63'])).

thf('65',plain,
    ( ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['52','64'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('66',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('67',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X23: $i] :
      ( ( k5_xboole_0 @ X23 @ X23 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('69',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['39'])).

thf('71',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
       != k1_xboole_0 )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('74',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['40','72','73'])).

thf('75',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['38','74'])).

thf('76',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('77',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('79',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','34','37'])).

thf('81',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('82',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('85',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k5_xboole_0 @ k1_xboole_0 @ ( k1_tarski @ sk_A ) ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58','63'])).

thf('87',plain,
    ( ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['40','72','73'])).

thf('89',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['87','88'])).

thf('90',plain,
    ( ( k3_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['87','88'])).

thf('91',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('92',plain,
    ( ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( k1_tarski @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['79','89','92'])).

thf('94',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( r2_hidden @ sk_A @ sk_B )
    | ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','95'])).

thf('97',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['39'])).

thf('98',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['40','72'])).

thf('99',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( r2_hidden @ sk_A @ ( k4_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) ) )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['96','99'])).

thf('101',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k3_xboole_0 @ X24 @ X25 )
      = ( k5_xboole_0 @ X24 @ ( k5_xboole_0 @ X25 @ ( k2_xboole_0 @ X24 @ X25 ) ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('102',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('103',plain,(
    ! [X0: $i] :
      ( X0
      = ( k5_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','58','63'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['101','104'])).

thf('106',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ X14 )
      = ( k5_xboole_0 @ X13 @ ( k3_xboole_0 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('107',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['105','106'])).

thf('108',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( r2_hidden @ X9 @ ( k5_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ( X4
       != ( k2_xboole_0 @ X5 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('111',plain,(
    ! [X2: $i,X3: $i,X5: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X5 @ X3 ) )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['109','111'])).

thf('113',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['100','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('115',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 )
      | ( r2_hidden @ X33 @ X37 )
      | ( X37
       != ( k1_enumset1 @ X36 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('117',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ X33 @ ( k1_enumset1 @ X36 @ X35 @ X34 ) )
      | ( zip_tseitin_0 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,(
    ! [X68: $i,X70: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X68 ) @ X70 )
      | ~ ( r2_hidden @ X68 @ X70 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('119',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 )
      | ( r1_tarski @ ( k1_tarski @ X3 ) @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ sk_A @ X0 @ X1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['115','119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ sk_A @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','120'])).

thf('122',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( X29 != X28 )
      | ~ ( zip_tseitin_0 @ X29 @ X30 @ X31 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ~ ( zip_tseitin_0 @ X28 @ X30 @ X31 @ X28 ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k2_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','123'])).

thf('125',plain,(
    r1_tarski @ k1_xboole_0 @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','124'])).

thf('126',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['113','114'])).

thf('127',plain,(
    r1_tarski @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['113','114'])).

thf('129',plain,(
    ! [X68: $i,X69: $i] :
      ( ( r2_hidden @ X68 @ X69 )
      | ~ ( r1_tarski @ ( k1_tarski @ X68 ) @ X69 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['127','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['7'])).

thf('133',plain,(
    $false ),
    inference('sup-',[status(thm)],['131','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.2NSvzCcGFO
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:50:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 3.26/3.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.26/3.51  % Solved by: fo/fo7.sh
% 3.26/3.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.26/3.51  % done 1999 iterations in 3.062s
% 3.26/3.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.26/3.51  % SZS output start Refutation
% 3.26/3.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 3.26/3.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.26/3.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 3.26/3.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.26/3.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.26/3.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.26/3.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.26/3.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.26/3.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 3.26/3.51  thf(sk_B_type, type, sk_B: $i).
% 3.26/3.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 3.26/3.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.26/3.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.26/3.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 3.26/3.51  thf(sk_A_type, type, sk_A: $i).
% 3.26/3.51  thf(t69_enumset1, axiom,
% 3.26/3.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.26/3.51  thf('0', plain, (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 3.26/3.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.26/3.51  thf(t70_enumset1, axiom,
% 3.26/3.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 3.26/3.51  thf('1', plain,
% 3.26/3.51      (![X41 : $i, X42 : $i]:
% 3.26/3.51         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 3.26/3.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.26/3.51  thf(d1_enumset1, axiom,
% 3.26/3.51    (![A:$i,B:$i,C:$i,D:$i]:
% 3.26/3.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 3.26/3.51       ( ![E:$i]:
% 3.26/3.51         ( ( r2_hidden @ E @ D ) <=>
% 3.26/3.51           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 3.26/3.51  thf(zf_stmt_0, axiom,
% 3.26/3.51    (![E:$i,C:$i,B:$i,A:$i]:
% 3.26/3.51     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 3.26/3.51       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 3.26/3.51  thf('2', plain,
% 3.26/3.51      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 3.26/3.51         ((zip_tseitin_0 @ X29 @ X30 @ X31 @ X32)
% 3.26/3.51          | ((X29) = (X30))
% 3.26/3.51          | ((X29) = (X31))
% 3.26/3.51          | ((X29) = (X32)))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf(d3_xboole_0, axiom,
% 3.26/3.51    (![A:$i,B:$i,C:$i]:
% 3.26/3.51     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 3.26/3.51       ( ![D:$i]:
% 3.26/3.51         ( ( r2_hidden @ D @ C ) <=>
% 3.26/3.51           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 3.26/3.51  thf('3', plain,
% 3.26/3.51      (![X3 : $i, X5 : $i, X7 : $i]:
% 3.26/3.51         (((X7) = (k2_xboole_0 @ X5 @ X3))
% 3.26/3.51          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X3)
% 3.26/3.51          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X5)
% 3.26/3.51          | (r2_hidden @ (sk_D @ X7 @ X3 @ X5) @ X7))),
% 3.26/3.51      inference('cnf', [status(esa)], [d3_xboole_0])).
% 3.26/3.51  thf(t92_xboole_1, axiom,
% 3.26/3.51    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 3.26/3.51  thf('4', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 3.26/3.51      inference('cnf', [status(esa)], [t92_xboole_1])).
% 3.26/3.51  thf(t1_xboole_0, axiom,
% 3.26/3.51    (![A:$i,B:$i,C:$i]:
% 3.26/3.51     ( ( r2_hidden @ A @ ( k5_xboole_0 @ B @ C ) ) <=>
% 3.26/3.51       ( ~( ( r2_hidden @ A @ B ) <=> ( r2_hidden @ A @ C ) ) ) ))).
% 3.26/3.51  thf('5', plain,
% 3.26/3.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.26/3.51         (~ (r2_hidden @ X9 @ X10)
% 3.26/3.51          | ~ (r2_hidden @ X9 @ X11)
% 3.26/3.51          | ~ (r2_hidden @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 3.26/3.51      inference('cnf', [status(esa)], [t1_xboole_0])).
% 3.26/3.51  thf('6', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]:
% 3.26/3.51         (~ (r2_hidden @ X1 @ k1_xboole_0)
% 3.26/3.51          | ~ (r2_hidden @ X1 @ X0)
% 3.26/3.51          | ~ (r2_hidden @ X1 @ X0))),
% 3.26/3.51      inference('sup-', [status(thm)], ['4', '5'])).
% 3.26/3.51  thf('7', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]:
% 3.26/3.51         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 3.26/3.51      inference('simplify', [status(thm)], ['6'])).
% 3.26/3.51  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.26/3.51      inference('condensation', [status(thm)], ['7'])).
% 3.26/3.51  thf('9', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]:
% 3.26/3.51         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 3.26/3.51          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X0)
% 3.26/3.51          | ((X1) = (k2_xboole_0 @ X0 @ k1_xboole_0)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['3', '8'])).
% 3.26/3.51  thf(t1_boole, axiom,
% 3.26/3.51    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 3.26/3.51  thf('10', plain, (![X17 : $i]: ((k2_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 3.26/3.51      inference('cnf', [status(esa)], [t1_boole])).
% 3.26/3.51  thf('11', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]:
% 3.26/3.51         ((r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1)
% 3.26/3.51          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X0)
% 3.26/3.51          | ((X1) = (X0)))),
% 3.26/3.51      inference('demod', [status(thm)], ['9', '10'])).
% 3.26/3.51  thf('12', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.26/3.51      inference('condensation', [status(thm)], ['7'])).
% 3.26/3.51  thf('13', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         (((X0) = (k1_xboole_0))
% 3.26/3.51          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ k1_xboole_0) @ X0))),
% 3.26/3.51      inference('sup-', [status(thm)], ['11', '12'])).
% 3.26/3.51  thf('14', plain,
% 3.26/3.51      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 3.26/3.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.26/3.51  thf('15', plain,
% 3.26/3.51      (![X41 : $i, X42 : $i]:
% 3.26/3.51         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 3.26/3.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 3.26/3.51  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 3.26/3.51  thf(zf_stmt_2, axiom,
% 3.26/3.51    (![A:$i,B:$i,C:$i,D:$i]:
% 3.26/3.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 3.26/3.51       ( ![E:$i]:
% 3.26/3.51         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 3.26/3.51  thf('16', plain,
% 3.26/3.51      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 3.26/3.51         (~ (r2_hidden @ X38 @ X37)
% 3.26/3.51          | ~ (zip_tseitin_0 @ X38 @ X34 @ X35 @ X36)
% 3.26/3.51          | ((X37) != (k1_enumset1 @ X36 @ X35 @ X34)))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.26/3.51  thf('17', plain,
% 3.26/3.51      (![X34 : $i, X35 : $i, X36 : $i, X38 : $i]:
% 3.26/3.51         (~ (zip_tseitin_0 @ X38 @ X34 @ X35 @ X36)
% 3.26/3.51          | ~ (r2_hidden @ X38 @ (k1_enumset1 @ X36 @ X35 @ X34)))),
% 3.26/3.51      inference('simplify', [status(thm)], ['16'])).
% 3.26/3.51  thf('18', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.26/3.51         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 3.26/3.51          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 3.26/3.51      inference('sup-', [status(thm)], ['15', '17'])).
% 3.26/3.51  thf('19', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]:
% 3.26/3.51         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 3.26/3.51          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 3.26/3.51      inference('sup-', [status(thm)], ['14', '18'])).
% 3.26/3.51  thf('20', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         (((k1_tarski @ X0) = (k1_xboole_0))
% 3.26/3.51          | ~ (zip_tseitin_0 @ 
% 3.26/3.51               (sk_D @ (k1_tarski @ X0) @ k1_xboole_0 @ k1_xboole_0) @ X0 @ 
% 3.26/3.51               X0 @ X0))),
% 3.26/3.51      inference('sup-', [status(thm)], ['13', '19'])).
% 3.26/3.51  thf('21', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         (((sk_D @ (k1_tarski @ X0) @ k1_xboole_0 @ k1_xboole_0) = (X0))
% 3.26/3.51          | ((sk_D @ (k1_tarski @ X0) @ k1_xboole_0 @ k1_xboole_0) = (X0))
% 3.26/3.51          | ((sk_D @ (k1_tarski @ X0) @ k1_xboole_0 @ k1_xboole_0) = (X0))
% 3.26/3.51          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['2', '20'])).
% 3.26/3.51  thf('22', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         (((k1_tarski @ X0) = (k1_xboole_0))
% 3.26/3.51          | ((sk_D @ (k1_tarski @ X0) @ k1_xboole_0 @ k1_xboole_0) = (X0)))),
% 3.26/3.51      inference('simplify', [status(thm)], ['21'])).
% 3.26/3.51  thf('23', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         (((X0) = (k1_xboole_0))
% 3.26/3.51          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0 @ k1_xboole_0) @ X0))),
% 3.26/3.51      inference('sup-', [status(thm)], ['11', '12'])).
% 3.26/3.51  thf('24', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 3.26/3.51          | ((k1_tarski @ X0) = (k1_xboole_0))
% 3.26/3.51          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 3.26/3.51      inference('sup+', [status(thm)], ['22', '23'])).
% 3.26/3.51  thf('25', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         (((k1_tarski @ X0) = (k1_xboole_0))
% 3.26/3.51          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 3.26/3.51      inference('simplify', [status(thm)], ['24'])).
% 3.26/3.51  thf(t68_zfmisc_1, conjecture,
% 3.26/3.51    (![A:$i,B:$i]:
% 3.26/3.51     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 3.26/3.51       ( r2_hidden @ A @ B ) ))).
% 3.26/3.51  thf(zf_stmt_3, negated_conjecture,
% 3.26/3.51    (~( ![A:$i,B:$i]:
% 3.26/3.51        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 3.26/3.51          ( r2_hidden @ A @ B ) ) )),
% 3.26/3.51    inference('cnf.neg', [status(esa)], [t68_zfmisc_1])).
% 3.26/3.51  thf('26', plain,
% 3.26/3.51      (((r2_hidden @ sk_A @ sk_B)
% 3.26/3.51        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.26/3.51  thf('27', plain,
% 3.26/3.51      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 3.26/3.51         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 3.26/3.51      inference('split', [status(esa)], ['26'])).
% 3.26/3.51  thf(t39_xboole_1, axiom,
% 3.26/3.51    (![A:$i,B:$i]:
% 3.26/3.51     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.26/3.51  thf('28', plain,
% 3.26/3.51      (![X18 : $i, X19 : $i]:
% 3.26/3.51         ((k2_xboole_0 @ X18 @ (k4_xboole_0 @ X19 @ X18))
% 3.26/3.51           = (k2_xboole_0 @ X18 @ X19))),
% 3.26/3.51      inference('cnf', [status(esa)], [t39_xboole_1])).
% 3.26/3.51  thf('29', plain,
% 3.26/3.51      ((((k2_xboole_0 @ sk_B @ k1_xboole_0)
% 3.26/3.51          = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 3.26/3.51         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 3.26/3.51      inference('sup+', [status(thm)], ['27', '28'])).
% 3.26/3.51  thf(commutativity_k2_tarski, axiom,
% 3.26/3.51    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 3.26/3.51  thf('30', plain,
% 3.26/3.51      (![X26 : $i, X27 : $i]:
% 3.26/3.51         ((k2_tarski @ X27 @ X26) = (k2_tarski @ X26 @ X27))),
% 3.26/3.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 3.26/3.51  thf(l51_zfmisc_1, axiom,
% 3.26/3.51    (![A:$i,B:$i]:
% 3.26/3.51     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 3.26/3.51  thf('31', plain,
% 3.26/3.51      (![X71 : $i, X72 : $i]:
% 3.26/3.51         ((k3_tarski @ (k2_tarski @ X71 @ X72)) = (k2_xboole_0 @ X71 @ X72))),
% 3.26/3.51      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.26/3.51  thf('32', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]:
% 3.26/3.51         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 3.26/3.51      inference('sup+', [status(thm)], ['30', '31'])).
% 3.26/3.51  thf('33', plain,
% 3.26/3.51      (![X71 : $i, X72 : $i]:
% 3.26/3.51         ((k3_tarski @ (k2_tarski @ X71 @ X72)) = (k2_xboole_0 @ X71 @ X72))),
% 3.26/3.51      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.26/3.51  thf('34', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.26/3.51      inference('sup+', [status(thm)], ['32', '33'])).
% 3.26/3.51  thf('35', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.26/3.51      inference('sup+', [status(thm)], ['32', '33'])).
% 3.26/3.51  thf('36', plain, (![X17 : $i]: ((k2_xboole_0 @ X17 @ k1_xboole_0) = (X17))),
% 3.26/3.51      inference('cnf', [status(esa)], [t1_boole])).
% 3.26/3.51  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.26/3.51      inference('sup+', [status(thm)], ['35', '36'])).
% 3.26/3.51  thf('38', plain,
% 3.26/3.51      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 3.26/3.51         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 3.26/3.51      inference('demod', [status(thm)], ['29', '34', '37'])).
% 3.26/3.51  thf('39', plain,
% 3.26/3.51      ((~ (r2_hidden @ sk_A @ sk_B)
% 3.26/3.51        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 3.26/3.51  thf('40', plain,
% 3.26/3.51      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 3.26/3.51       ~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 3.26/3.51      inference('split', [status(esa)], ['39'])).
% 3.26/3.51  thf('41', plain,
% 3.26/3.51      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 3.26/3.51      inference('split', [status(esa)], ['26'])).
% 3.26/3.51  thf(l1_zfmisc_1, axiom,
% 3.26/3.51    (![A:$i,B:$i]:
% 3.26/3.51     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 3.26/3.51  thf('42', plain,
% 3.26/3.51      (![X68 : $i, X70 : $i]:
% 3.26/3.51         ((r1_tarski @ (k1_tarski @ X68) @ X70) | ~ (r2_hidden @ X68 @ X70))),
% 3.26/3.51      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 3.26/3.51  thf('43', plain,
% 3.26/3.51      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_B))
% 3.26/3.51         <= (((r2_hidden @ sk_A @ sk_B)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['41', '42'])).
% 3.26/3.51  thf(t12_xboole_1, axiom,
% 3.26/3.51    (![A:$i,B:$i]:
% 3.26/3.51     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 3.26/3.51  thf('44', plain,
% 3.26/3.51      (![X15 : $i, X16 : $i]:
% 3.26/3.51         (((k2_xboole_0 @ X16 @ X15) = (X15)) | ~ (r1_tarski @ X16 @ X15))),
% 3.26/3.51      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.26/3.51  thf('45', plain,
% 3.26/3.51      ((((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (sk_B)))
% 3.26/3.51         <= (((r2_hidden @ sk_A @ sk_B)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['43', '44'])).
% 3.26/3.51  thf(t95_xboole_1, axiom,
% 3.26/3.51    (![A:$i,B:$i]:
% 3.26/3.51     ( ( k3_xboole_0 @ A @ B ) =
% 3.26/3.51       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 3.26/3.51  thf('46', plain,
% 3.26/3.51      (![X24 : $i, X25 : $i]:
% 3.26/3.51         ((k3_xboole_0 @ X24 @ X25)
% 3.26/3.51           = (k5_xboole_0 @ (k5_xboole_0 @ X24 @ X25) @ 
% 3.26/3.51              (k2_xboole_0 @ X24 @ X25)))),
% 3.26/3.51      inference('cnf', [status(esa)], [t95_xboole_1])).
% 3.26/3.51  thf(t91_xboole_1, axiom,
% 3.26/3.51    (![A:$i,B:$i,C:$i]:
% 3.26/3.51     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 3.26/3.51       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 3.26/3.51  thf('47', plain,
% 3.26/3.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.26/3.51         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 3.26/3.51           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 3.26/3.51      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.26/3.51  thf('48', plain,
% 3.26/3.51      (![X24 : $i, X25 : $i]:
% 3.26/3.51         ((k3_xboole_0 @ X24 @ X25)
% 3.26/3.51           = (k5_xboole_0 @ X24 @ 
% 3.26/3.51              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 3.26/3.51      inference('demod', [status(thm)], ['46', '47'])).
% 3.26/3.51  thf('49', plain,
% 3.26/3.51      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 3.26/3.51          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k5_xboole_0 @ sk_B @ sk_B))))
% 3.26/3.51         <= (((r2_hidden @ sk_A @ sk_B)))),
% 3.26/3.51      inference('sup+', [status(thm)], ['45', '48'])).
% 3.26/3.51  thf('50', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 3.26/3.51      inference('cnf', [status(esa)], [t92_xboole_1])).
% 3.26/3.51  thf(commutativity_k5_xboole_0, axiom,
% 3.26/3.51    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 3.26/3.51  thf('51', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 3.26/3.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 3.26/3.51  thf('52', plain,
% 3.26/3.51      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 3.26/3.51          = (k5_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A))))
% 3.26/3.51         <= (((r2_hidden @ sk_A @ sk_B)))),
% 3.26/3.51      inference('demod', [status(thm)], ['49', '50', '51'])).
% 3.26/3.51  thf('53', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 3.26/3.51      inference('cnf', [status(esa)], [t92_xboole_1])).
% 3.26/3.51  thf('54', plain,
% 3.26/3.51      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.26/3.51         ((k5_xboole_0 @ (k5_xboole_0 @ X20 @ X21) @ X22)
% 3.26/3.51           = (k5_xboole_0 @ X20 @ (k5_xboole_0 @ X21 @ X22)))),
% 3.26/3.51      inference('cnf', [status(esa)], [t91_xboole_1])).
% 3.26/3.51  thf('55', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]:
% 3.26/3.51         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 3.26/3.51           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.26/3.51      inference('sup+', [status(thm)], ['53', '54'])).
% 3.26/3.51  thf('56', plain,
% 3.26/3.51      (![X24 : $i, X25 : $i]:
% 3.26/3.51         ((k3_xboole_0 @ X24 @ X25)
% 3.26/3.51           = (k5_xboole_0 @ X24 @ 
% 3.26/3.51              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 3.26/3.51      inference('demod', [status(thm)], ['46', '47'])).
% 3.26/3.51  thf('57', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         ((k3_xboole_0 @ X0 @ X0)
% 3.26/3.51           = (k5_xboole_0 @ k1_xboole_0 @ (k2_xboole_0 @ X0 @ X0)))),
% 3.26/3.51      inference('sup+', [status(thm)], ['55', '56'])).
% 3.26/3.51  thf(idempotence_k3_xboole_0, axiom,
% 3.26/3.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 3.26/3.51  thf('58', plain, (![X8 : $i]: ((k3_xboole_0 @ X8 @ X8) = (X8))),
% 3.26/3.51      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 3.26/3.51  thf('59', plain,
% 3.26/3.51      (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 3.26/3.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.26/3.51  thf(t31_zfmisc_1, axiom,
% 3.26/3.51    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 3.26/3.51  thf('60', plain, (![X73 : $i]: ((k3_tarski @ (k1_tarski @ X73)) = (X73))),
% 3.26/3.51      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 3.26/3.51  thf('61', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 3.26/3.51      inference('sup+', [status(thm)], ['59', '60'])).
% 3.26/3.51  thf('62', plain,
% 3.26/3.51      (![X71 : $i, X72 : $i]:
% 3.26/3.51         ((k3_tarski @ (k2_tarski @ X71 @ X72)) = (k2_xboole_0 @ X71 @ X72))),
% 3.26/3.51      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 3.26/3.51  thf('63', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 3.26/3.51      inference('demod', [status(thm)], ['61', '62'])).
% 3.26/3.51  thf('64', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 3.26/3.51      inference('demod', [status(thm)], ['57', '58', '63'])).
% 3.26/3.51  thf('65', plain,
% 3.26/3.51      ((((k3_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 3.26/3.51         <= (((r2_hidden @ sk_A @ sk_B)))),
% 3.26/3.51      inference('demod', [status(thm)], ['52', '64'])).
% 3.26/3.51  thf(t100_xboole_1, axiom,
% 3.26/3.51    (![A:$i,B:$i]:
% 3.26/3.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 3.26/3.51  thf('66', plain,
% 3.26/3.51      (![X13 : $i, X14 : $i]:
% 3.26/3.51         ((k4_xboole_0 @ X13 @ X14)
% 3.26/3.51           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 3.26/3.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.26/3.51  thf('67', plain,
% 3.26/3.51      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)
% 3.26/3.51          = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))))
% 3.26/3.51         <= (((r2_hidden @ sk_A @ sk_B)))),
% 3.26/3.51      inference('sup+', [status(thm)], ['65', '66'])).
% 3.26/3.51  thf('68', plain, (![X23 : $i]: ((k5_xboole_0 @ X23 @ X23) = (k1_xboole_0))),
% 3.26/3.51      inference('cnf', [status(esa)], [t92_xboole_1])).
% 3.26/3.51  thf('69', plain,
% 3.26/3.51      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))
% 3.26/3.51         <= (((r2_hidden @ sk_A @ sk_B)))),
% 3.26/3.51      inference('demod', [status(thm)], ['67', '68'])).
% 3.26/3.51  thf('70', plain,
% 3.26/3.51      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_xboole_0)))
% 3.26/3.51         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 3.26/3.51      inference('split', [status(esa)], ['39'])).
% 3.26/3.51  thf('71', plain,
% 3.26/3.51      ((((k1_xboole_0) != (k1_xboole_0)))
% 3.26/3.51         <= (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) & 
% 3.26/3.51             ((r2_hidden @ sk_A @ sk_B)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['69', '70'])).
% 3.26/3.51  thf('72', plain,
% 3.26/3.51      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 3.26/3.51       ~ ((r2_hidden @ sk_A @ sk_B))),
% 3.26/3.51      inference('simplify', [status(thm)], ['71'])).
% 3.26/3.51  thf('73', plain,
% 3.26/3.51      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))) | 
% 3.26/3.51       ((r2_hidden @ sk_A @ sk_B))),
% 3.26/3.51      inference('split', [status(esa)], ['26'])).
% 3.26/3.51  thf('74', plain,
% 3.26/3.51      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 3.26/3.51      inference('sat_resolution*', [status(thm)], ['40', '72', '73'])).
% 3.26/3.51  thf('75', plain, (((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 3.26/3.51      inference('simpl_trail', [status(thm)], ['38', '74'])).
% 3.26/3.51  thf('76', plain,
% 3.26/3.51      (![X24 : $i, X25 : $i]:
% 3.26/3.51         ((k3_xboole_0 @ X24 @ X25)
% 3.26/3.51           = (k5_xboole_0 @ X24 @ 
% 3.26/3.51              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 3.26/3.51      inference('demod', [status(thm)], ['46', '47'])).
% 3.26/3.51  thf('77', plain,
% 3.26/3.51      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 3.26/3.51         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 3.26/3.51      inference('sup+', [status(thm)], ['75', '76'])).
% 3.26/3.51  thf('78', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 3.26/3.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 3.26/3.51  thf('79', plain,
% 3.26/3.51      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 3.26/3.51         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 3.26/3.51      inference('demod', [status(thm)], ['77', '78'])).
% 3.26/3.51  thf('80', plain,
% 3.26/3.51      ((((sk_B) = (k2_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))
% 3.26/3.51         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 3.26/3.51      inference('demod', [status(thm)], ['29', '34', '37'])).
% 3.26/3.51  thf('81', plain,
% 3.26/3.51      (![X24 : $i, X25 : $i]:
% 3.26/3.51         ((k3_xboole_0 @ X24 @ X25)
% 3.26/3.51           = (k5_xboole_0 @ X24 @ 
% 3.26/3.51              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 3.26/3.51      inference('demod', [status(thm)], ['46', '47'])).
% 3.26/3.51  thf('82', plain,
% 3.26/3.51      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 3.26/3.51          = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))))
% 3.26/3.51         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 3.26/3.51      inference('sup+', [status(thm)], ['80', '81'])).
% 3.26/3.51  thf('83', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 3.26/3.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 3.26/3.51  thf('84', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]:
% 3.26/3.51         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 3.26/3.51           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.26/3.51      inference('sup+', [status(thm)], ['53', '54'])).
% 3.26/3.51  thf('85', plain,
% 3.26/3.51      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 3.26/3.51          = (k5_xboole_0 @ k1_xboole_0 @ (k1_tarski @ sk_A))))
% 3.26/3.51         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 3.26/3.51      inference('demod', [status(thm)], ['82', '83', '84'])).
% 3.26/3.51  thf('86', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 3.26/3.51      inference('demod', [status(thm)], ['57', '58', '63'])).
% 3.26/3.51  thf('87', plain,
% 3.26/3.51      ((((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A)))
% 3.26/3.51         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))))),
% 3.26/3.51      inference('demod', [status(thm)], ['85', '86'])).
% 3.26/3.51  thf('88', plain,
% 3.26/3.51      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0)))),
% 3.26/3.51      inference('sat_resolution*', [status(thm)], ['40', '72', '73'])).
% 3.26/3.51  thf('89', plain,
% 3.26/3.51      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 3.26/3.51      inference('simpl_trail', [status(thm)], ['87', '88'])).
% 3.26/3.51  thf('90', plain,
% 3.26/3.51      (((k3_xboole_0 @ sk_B @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 3.26/3.51      inference('simpl_trail', [status(thm)], ['87', '88'])).
% 3.26/3.51  thf('91', plain,
% 3.26/3.51      (![X13 : $i, X14 : $i]:
% 3.26/3.51         ((k4_xboole_0 @ X13 @ X14)
% 3.26/3.51           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 3.26/3.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.26/3.51  thf('92', plain,
% 3.26/3.51      (((k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))
% 3.26/3.51         = (k5_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 3.26/3.51      inference('sup+', [status(thm)], ['90', '91'])).
% 3.26/3.51  thf('93', plain,
% 3.26/3.51      (((k1_tarski @ sk_A)
% 3.26/3.51         = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 3.26/3.51      inference('demod', [status(thm)], ['79', '89', '92'])).
% 3.26/3.51  thf('94', plain,
% 3.26/3.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.26/3.51         ((r2_hidden @ X9 @ X10)
% 3.26/3.51          | (r2_hidden @ X9 @ X11)
% 3.26/3.51          | ~ (r2_hidden @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 3.26/3.51      inference('cnf', [status(esa)], [t1_xboole_0])).
% 3.26/3.51  thf('95', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 3.26/3.51          | (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 3.26/3.51          | (r2_hidden @ X0 @ sk_B))),
% 3.26/3.51      inference('sup-', [status(thm)], ['93', '94'])).
% 3.26/3.51  thf('96', plain,
% 3.26/3.51      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 3.26/3.51        | (r2_hidden @ sk_A @ sk_B)
% 3.26/3.51        | (r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A))))),
% 3.26/3.51      inference('sup-', [status(thm)], ['25', '95'])).
% 3.26/3.51  thf('97', plain,
% 3.26/3.51      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 3.26/3.51      inference('split', [status(esa)], ['39'])).
% 3.26/3.51  thf('98', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 3.26/3.51      inference('sat_resolution*', [status(thm)], ['40', '72'])).
% 3.26/3.51  thf('99', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 3.26/3.51      inference('simpl_trail', [status(thm)], ['97', '98'])).
% 3.26/3.51  thf('100', plain,
% 3.26/3.51      (((r2_hidden @ sk_A @ (k4_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 3.26/3.51        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 3.26/3.51      inference('clc', [status(thm)], ['96', '99'])).
% 3.26/3.51  thf('101', plain,
% 3.26/3.51      (![X24 : $i, X25 : $i]:
% 3.26/3.51         ((k3_xboole_0 @ X24 @ X25)
% 3.26/3.51           = (k5_xboole_0 @ X24 @ 
% 3.26/3.51              (k5_xboole_0 @ X25 @ (k2_xboole_0 @ X24 @ X25))))),
% 3.26/3.51      inference('demod', [status(thm)], ['46', '47'])).
% 3.26/3.51  thf('102', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]:
% 3.26/3.51         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 3.26/3.51           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.26/3.51      inference('sup+', [status(thm)], ['53', '54'])).
% 3.26/3.51  thf('103', plain, (![X0 : $i]: ((X0) = (k5_xboole_0 @ k1_xboole_0 @ X0))),
% 3.26/3.51      inference('demod', [status(thm)], ['57', '58', '63'])).
% 3.26/3.51  thf('104', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]:
% 3.26/3.51         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 3.26/3.51      inference('demod', [status(thm)], ['102', '103'])).
% 3.26/3.51  thf('105', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]:
% 3.26/3.51         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 3.26/3.51           = (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)))),
% 3.26/3.51      inference('sup+', [status(thm)], ['101', '104'])).
% 3.26/3.51  thf('106', plain,
% 3.26/3.51      (![X13 : $i, X14 : $i]:
% 3.26/3.51         ((k4_xboole_0 @ X13 @ X14)
% 3.26/3.51           = (k5_xboole_0 @ X13 @ (k3_xboole_0 @ X13 @ X14)))),
% 3.26/3.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 3.26/3.51  thf('107', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]:
% 3.26/3.51         ((k5_xboole_0 @ X0 @ (k2_xboole_0 @ X1 @ X0))
% 3.26/3.51           = (k4_xboole_0 @ X1 @ X0))),
% 3.26/3.51      inference('demod', [status(thm)], ['105', '106'])).
% 3.26/3.51  thf('108', plain,
% 3.26/3.51      (![X9 : $i, X10 : $i, X11 : $i]:
% 3.26/3.51         (~ (r2_hidden @ X9 @ X10)
% 3.26/3.51          | ~ (r2_hidden @ X9 @ X11)
% 3.26/3.51          | ~ (r2_hidden @ X9 @ (k5_xboole_0 @ X10 @ X11)))),
% 3.26/3.51      inference('cnf', [status(esa)], [t1_xboole_0])).
% 3.26/3.51  thf('109', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.26/3.51         (~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0))
% 3.26/3.51          | ~ (r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 3.26/3.51          | ~ (r2_hidden @ X2 @ X0))),
% 3.26/3.51      inference('sup-', [status(thm)], ['107', '108'])).
% 3.26/3.51  thf('110', plain,
% 3.26/3.51      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 3.26/3.51         (~ (r2_hidden @ X2 @ X3)
% 3.26/3.51          | (r2_hidden @ X2 @ X4)
% 3.26/3.51          | ((X4) != (k2_xboole_0 @ X5 @ X3)))),
% 3.26/3.51      inference('cnf', [status(esa)], [d3_xboole_0])).
% 3.26/3.51  thf('111', plain,
% 3.26/3.51      (![X2 : $i, X3 : $i, X5 : $i]:
% 3.26/3.51         ((r2_hidden @ X2 @ (k2_xboole_0 @ X5 @ X3)) | ~ (r2_hidden @ X2 @ X3))),
% 3.26/3.51      inference('simplify', [status(thm)], ['110'])).
% 3.26/3.51  thf('112', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.26/3.51         (~ (r2_hidden @ X2 @ X0)
% 3.26/3.51          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.26/3.51      inference('clc', [status(thm)], ['109', '111'])).
% 3.26/3.51  thf('113', plain,
% 3.26/3.51      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 3.26/3.51        | ~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['100', '112'])).
% 3.26/3.51  thf('114', plain,
% 3.26/3.51      (![X0 : $i]:
% 3.26/3.51         (((k1_tarski @ X0) = (k1_xboole_0))
% 3.26/3.51          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 3.26/3.51      inference('simplify', [status(thm)], ['24'])).
% 3.26/3.51  thf('115', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 3.26/3.51      inference('clc', [status(thm)], ['113', '114'])).
% 3.26/3.51  thf('116', plain,
% 3.26/3.51      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 3.26/3.51         ((zip_tseitin_0 @ X33 @ X34 @ X35 @ X36)
% 3.26/3.51          | (r2_hidden @ X33 @ X37)
% 3.26/3.51          | ((X37) != (k1_enumset1 @ X36 @ X35 @ X34)))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.26/3.51  thf('117', plain,
% 3.26/3.51      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 3.26/3.51         ((r2_hidden @ X33 @ (k1_enumset1 @ X36 @ X35 @ X34))
% 3.26/3.51          | (zip_tseitin_0 @ X33 @ X34 @ X35 @ X36))),
% 3.26/3.51      inference('simplify', [status(thm)], ['116'])).
% 3.26/3.51  thf('118', plain,
% 3.26/3.51      (![X68 : $i, X70 : $i]:
% 3.26/3.51         ((r1_tarski @ (k1_tarski @ X68) @ X70) | ~ (r2_hidden @ X68 @ X70))),
% 3.26/3.51      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 3.26/3.51  thf('119', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 3.26/3.51         ((zip_tseitin_0 @ X3 @ X0 @ X1 @ X2)
% 3.26/3.51          | (r1_tarski @ (k1_tarski @ X3) @ (k1_enumset1 @ X2 @ X1 @ X0)))),
% 3.26/3.51      inference('sup-', [status(thm)], ['117', '118'])).
% 3.26/3.51  thf('120', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.26/3.51         ((r1_tarski @ k1_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 3.26/3.51          | (zip_tseitin_0 @ sk_A @ X0 @ X1 @ X2))),
% 3.26/3.51      inference('sup+', [status(thm)], ['115', '119'])).
% 3.26/3.51  thf('121', plain,
% 3.26/3.51      (![X0 : $i, X1 : $i]:
% 3.26/3.51         ((r1_tarski @ k1_xboole_0 @ (k2_tarski @ X1 @ X0))
% 3.26/3.51          | (zip_tseitin_0 @ sk_A @ X0 @ X1 @ X1))),
% 3.26/3.51      inference('sup+', [status(thm)], ['1', '120'])).
% 3.26/3.51  thf('122', plain,
% 3.26/3.51      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 3.26/3.51         (((X29) != (X28)) | ~ (zip_tseitin_0 @ X29 @ X30 @ X31 @ X28))),
% 3.26/3.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.26/3.51  thf('123', plain,
% 3.26/3.51      (![X28 : $i, X30 : $i, X31 : $i]:
% 3.26/3.51         ~ (zip_tseitin_0 @ X28 @ X30 @ X31 @ X28)),
% 3.26/3.51      inference('simplify', [status(thm)], ['122'])).
% 3.26/3.51  thf('124', plain,
% 3.26/3.51      (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ (k2_tarski @ sk_A @ X0))),
% 3.26/3.51      inference('sup-', [status(thm)], ['121', '123'])).
% 3.26/3.51  thf('125', plain, ((r1_tarski @ k1_xboole_0 @ (k1_tarski @ sk_A))),
% 3.26/3.51      inference('sup+', [status(thm)], ['0', '124'])).
% 3.26/3.51  thf('126', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 3.26/3.51      inference('clc', [status(thm)], ['113', '114'])).
% 3.26/3.51  thf('127', plain, ((r1_tarski @ k1_xboole_0 @ k1_xboole_0)),
% 3.26/3.51      inference('demod', [status(thm)], ['125', '126'])).
% 3.26/3.51  thf('128', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 3.26/3.51      inference('clc', [status(thm)], ['113', '114'])).
% 3.26/3.51  thf('129', plain,
% 3.26/3.51      (![X68 : $i, X69 : $i]:
% 3.26/3.51         ((r2_hidden @ X68 @ X69) | ~ (r1_tarski @ (k1_tarski @ X68) @ X69))),
% 3.26/3.51      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 3.26/3.51  thf('130', plain,
% 3.26/3.51      (![X0 : $i]: (~ (r1_tarski @ k1_xboole_0 @ X0) | (r2_hidden @ sk_A @ X0))),
% 3.26/3.51      inference('sup-', [status(thm)], ['128', '129'])).
% 3.26/3.51  thf('131', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 3.26/3.51      inference('sup-', [status(thm)], ['127', '130'])).
% 3.26/3.51  thf('132', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 3.26/3.51      inference('condensation', [status(thm)], ['7'])).
% 3.26/3.51  thf('133', plain, ($false), inference('sup-', [status(thm)], ['131', '132'])).
% 3.26/3.51  
% 3.26/3.51  % SZS output end Refutation
% 3.26/3.51  
% 3.26/3.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
