%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wz3T7ZlI9G

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:12 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 583 expanded)
%              Number of leaves         :   34 ( 187 expanded)
%              Depth                    :   24
%              Number of atoms          :  971 (5348 expanded)
%              Number of equality atoms :   88 ( 430 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(t67_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = ( k1_tarski @ A ) )
    <=> ~ ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
          = ( k1_tarski @ A ) )
      <=> ~ ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t67_zfmisc_1])).

thf('0',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
   <= ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('3',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('5',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ~ ( r1_xboole_0 @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('7',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X66: $i] :
      ( ( k2_tarski @ X66 @ X66 )
      = ( k1_tarski @ X66 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X67: $i,X68: $i] :
      ( ( k1_enumset1 @ X67 @ X67 @ X68 )
      = ( k2_tarski @ X67 @ X68 ) ) ),
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

thf('10',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X36 @ X37 @ X38 @ X39 )
      | ( r2_hidden @ X36 @ X40 )
      | ( X40
       != ( k1_enumset1 @ X39 @ X38 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('11',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( r2_hidden @ X36 @ ( k1_enumset1 @ X39 @ X38 @ X37 ) )
      | ( zip_tseitin_0 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X66: $i] :
      ( ( k2_tarski @ X66 @ X66 )
      = ( k1_tarski @ X66 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('13',plain,(
    ! [X98: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X98 ) )
      = X98 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('15',plain,(
    ! [X96: $i,X97: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X96 @ X97 ) )
      = ( k2_xboole_0 @ X96 @ X97 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['14','15'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('17',plain,(
    ! [X94: $i,X95: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X94 ) @ X95 )
      | ( r2_hidden @ X94 @ X95 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('26',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('29',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_B @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ X0 )
        = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['16','33'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('35',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ X10 )
      = ( k5_xboole_0 @ X9 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('38',plain,(
    ! [X26: $i] :
      ( ( k5_xboole_0 @ X26 @ X26 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X98: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X98 ) )
      = X98 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('42',plain,
    ( ( ( k3_tarski @ k1_xboole_0 )
      = sk_A )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('44',plain,
    ( ( r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ sk_B )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X7 @ X5 )
      | ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_xboole_0 @ X5 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_B @ X0 )
        | ~ ( r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ ( k3_tarski @ k1_xboole_0 ) @ X0 @ X1 @ X2 )
        | ~ ( r1_xboole_0 @ sk_B @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','46'])).

thf('48',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_xboole_0 @ sk_B @ ( k2_tarski @ X1 @ X0 ) )
        | ( zip_tseitin_0 @ ( k3_tarski @ k1_xboole_0 ) @ X0 @ X1 @ X1 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['9','47'])).

thf('49',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
        | ( zip_tseitin_0 @ ( k3_tarski @ k1_xboole_0 ) @ X0 @ X0 @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['8','48'])).

thf('50',plain,
    ( ( zip_tseitin_0 @ ( k3_tarski @ k1_xboole_0 ) @ sk_A @ sk_A @ sk_A )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','49'])).

thf('51',plain,
    ( ( ( k3_tarski @ k1_xboole_0 )
      = sk_A )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('52',plain,
    ( ( ( k3_tarski @ k1_xboole_0 )
      = sk_A )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('53',plain,
    ( ( ( k3_tarski @ k1_xboole_0 )
      = sk_A )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('54',plain,
    ( ( zip_tseitin_0 @ ( k3_tarski @ k1_xboole_0 ) @ ( k3_tarski @ k1_xboole_0 ) @ ( k3_tarski @ k1_xboole_0 ) @ ( k3_tarski @ k1_xboole_0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( X32 != X31 )
      | ~ ( zip_tseitin_0 @ X32 @ X33 @ X34 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('56',plain,(
    ! [X31: $i,X33: $i,X34: $i] :
      ~ ( zip_tseitin_0 @ X31 @ X33 @ X34 @ X31 ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','57'])).

thf('59',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','58'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('60',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k2_tarski @ X30 @ X29 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('61',plain,(
    ! [X96: $i,X97: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X96 @ X97 ) )
      = ( k2_xboole_0 @ X96 @ X97 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X96: $i,X97: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X96 @ X97 ) )
      = ( k2_xboole_0 @ X96 @ X97 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X94: $i,X95: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X94 ) @ X95 )
      | ( r2_hidden @ X94 @ X95 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('66',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X19: $i,X20: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X19 @ X20 ) @ X20 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('70',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X21 @ X22 ) @ X22 )
        = X21 )
      | ~ ( r1_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('73',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k2_xboole_0 @ X12 @ ( k4_xboole_0 @ X13 @ X12 ) )
      = ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['68','74'])).

thf('76',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['26'])).

thf('77',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['26'])).

thf('78',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','57','77'])).

thf('79',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['76','78'])).

thf('80',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['75','79'])).

thf('81',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['59','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wz3T7ZlI9G
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.62  % Solved by: fo/fo7.sh
% 0.43/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.62  % done 498 iterations in 0.171s
% 0.43/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.62  % SZS output start Refutation
% 0.43/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.43/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.43/0.62  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.43/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.43/0.62  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.43/0.62  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.43/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.62  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.43/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.62  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.43/0.62  thf(t67_zfmisc_1, conjecture,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.43/0.62       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.43/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.62    (~( ![A:$i,B:$i]:
% 0.43/0.62        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.43/0.62          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.43/0.62    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.43/0.62  thf('0', plain,
% 0.43/0.62      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.43/0.62        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('1', plain,
% 0.43/0.62      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['0'])).
% 0.43/0.62  thf('2', plain,
% 0.43/0.62      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.43/0.62       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.43/0.62      inference('split', [status(esa)], ['0'])).
% 0.43/0.62  thf('3', plain,
% 0.43/0.62      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.43/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.43/0.62      inference('split', [status(esa)], ['0'])).
% 0.43/0.62  thf(t79_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.43/0.62  thf('4', plain,
% 0.43/0.62      (![X19 : $i, X20 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X20)),
% 0.43/0.62      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.43/0.62  thf('5', plain,
% 0.43/0.62      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.43/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.43/0.62      inference('sup+', [status(thm)], ['3', '4'])).
% 0.43/0.62  thf(symmetry_r1_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.43/0.62  thf('6', plain,
% 0.43/0.62      (![X3 : $i, X4 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ X3 @ X4) | ~ (r1_xboole_0 @ X4 @ X3))),
% 0.43/0.62      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.43/0.62  thf('7', plain,
% 0.43/0.62      (((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.43/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf(t69_enumset1, axiom,
% 0.43/0.62    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.43/0.62  thf('8', plain, (![X66 : $i]: ((k2_tarski @ X66 @ X66) = (k1_tarski @ X66))),
% 0.43/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.62  thf(t70_enumset1, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.43/0.62  thf('9', plain,
% 0.43/0.62      (![X67 : $i, X68 : $i]:
% 0.43/0.62         ((k1_enumset1 @ X67 @ X67 @ X68) = (k2_tarski @ X67 @ X68))),
% 0.43/0.62      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.43/0.62  thf(d1_enumset1, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.43/0.62       ( ![E:$i]:
% 0.43/0.62         ( ( r2_hidden @ E @ D ) <=>
% 0.43/0.62           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.43/0.62  thf(zf_stmt_2, axiom,
% 0.43/0.62    (![E:$i,C:$i,B:$i,A:$i]:
% 0.43/0.62     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.43/0.62       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.43/0.62  thf(zf_stmt_3, axiom,
% 0.43/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.62     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.43/0.62       ( ![E:$i]:
% 0.43/0.62         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.43/0.62  thf('10', plain,
% 0.43/0.62      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.43/0.62         ((zip_tseitin_0 @ X36 @ X37 @ X38 @ X39)
% 0.43/0.62          | (r2_hidden @ X36 @ X40)
% 0.43/0.62          | ((X40) != (k1_enumset1 @ X39 @ X38 @ X37)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.43/0.62  thf('11', plain,
% 0.43/0.62      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.43/0.62         ((r2_hidden @ X36 @ (k1_enumset1 @ X39 @ X38 @ X37))
% 0.43/0.62          | (zip_tseitin_0 @ X36 @ X37 @ X38 @ X39))),
% 0.43/0.62      inference('simplify', [status(thm)], ['10'])).
% 0.43/0.62  thf('12', plain,
% 0.43/0.62      (![X66 : $i]: ((k2_tarski @ X66 @ X66) = (k1_tarski @ X66))),
% 0.43/0.62      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.43/0.62  thf(t31_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.43/0.62  thf('13', plain, (![X98 : $i]: ((k3_tarski @ (k1_tarski @ X98)) = (X98))),
% 0.43/0.62      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.43/0.62  thf('14', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['12', '13'])).
% 0.43/0.62  thf(l51_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.43/0.62  thf('15', plain,
% 0.43/0.62      (![X96 : $i, X97 : $i]:
% 0.43/0.62         ((k3_tarski @ (k2_tarski @ X96 @ X97)) = (k2_xboole_0 @ X96 @ X97))),
% 0.43/0.62      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.43/0.62  thf('16', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.43/0.62      inference('demod', [status(thm)], ['14', '15'])).
% 0.43/0.62  thf(l27_zfmisc_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.43/0.62  thf('17', plain,
% 0.43/0.62      (![X94 : $i, X95 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ (k1_tarski @ X94) @ X95) | (r2_hidden @ X94 @ X95))),
% 0.43/0.62      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.43/0.62  thf(t3_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.43/0.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.43/0.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.43/0.62            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.43/0.62  thf('18', plain,
% 0.43/0.62      (![X5 : $i, X6 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.43/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.43/0.62  thf('19', plain,
% 0.43/0.62      (![X5 : $i, X6 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 0.43/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.43/0.62  thf('20', plain,
% 0.43/0.62      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X7 @ X5)
% 0.43/0.62          | ~ (r2_hidden @ X7 @ X8)
% 0.43/0.62          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.43/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.43/0.62  thf('21', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ X0 @ X1)
% 0.43/0.62          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.43/0.62          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.43/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.43/0.62  thf('22', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((r1_xboole_0 @ X0 @ X1)
% 0.43/0.62          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.43/0.62          | (r1_xboole_0 @ X0 @ X1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['18', '21'])).
% 0.43/0.62  thf('23', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.43/0.62      inference('simplify', [status(thm)], ['22'])).
% 0.43/0.62  thf('24', plain,
% 0.43/0.62      (![X0 : $i, X1 : $i]:
% 0.43/0.62         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.43/0.62          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.43/0.62      inference('sup-', [status(thm)], ['17', '23'])).
% 0.43/0.62  thf('25', plain,
% 0.43/0.62      (((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.43/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.43/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.43/0.62  thf('26', plain,
% 0.43/0.62      (((r2_hidden @ sk_A @ sk_B)
% 0.43/0.62        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))),
% 0.43/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.62  thf('27', plain,
% 0.43/0.62      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['26'])).
% 0.43/0.62  thf('28', plain,
% 0.43/0.62      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X7 @ X5)
% 0.43/0.62          | ~ (r2_hidden @ X7 @ X8)
% 0.43/0.62          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.43/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.43/0.62  thf('29', plain,
% 0.43/0.62      ((![X0 : $i]: (~ (r1_xboole_0 @ sk_B @ X0) | ~ (r2_hidden @ sk_A @ X0)))
% 0.43/0.62         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['27', '28'])).
% 0.43/0.62  thf('30', plain,
% 0.43/0.62      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 0.43/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.43/0.62             ((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['25', '29'])).
% 0.43/0.62  thf('31', plain,
% 0.43/0.62      ((![X0 : $i]: (r1_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.43/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.43/0.62             ((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['24', '30'])).
% 0.43/0.62  thf(t88_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( r1_xboole_0 @ A @ B ) =>
% 0.43/0.62       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.43/0.62  thf('32', plain,
% 0.43/0.62      (![X21 : $i, X22 : $i]:
% 0.43/0.62         (((k4_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X22) = (X21))
% 0.43/0.62          | ~ (r1_xboole_0 @ X21 @ X22))),
% 0.43/0.62      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.43/0.62  thf('33', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          ((k4_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ X0)
% 0.43/0.62            = (k1_tarski @ sk_A)))
% 0.43/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.43/0.62             ((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['31', '32'])).
% 0.43/0.62  thf('34', plain,
% 0.43/0.62      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.43/0.62          = (k1_tarski @ sk_A)))
% 0.43/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.43/0.62             ((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['16', '33'])).
% 0.43/0.62  thf(idempotence_k3_xboole_0, axiom,
% 0.43/0.62    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.43/0.62  thf('35', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.43/0.62      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.43/0.62  thf(t100_xboole_1, axiom,
% 0.43/0.62    (![A:$i,B:$i]:
% 0.43/0.62     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.43/0.62  thf('36', plain,
% 0.43/0.62      (![X9 : $i, X10 : $i]:
% 0.43/0.62         ((k4_xboole_0 @ X9 @ X10)
% 0.43/0.62           = (k5_xboole_0 @ X9 @ (k3_xboole_0 @ X9 @ X10)))),
% 0.43/0.62      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.43/0.62  thf('37', plain,
% 0.43/0.62      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['35', '36'])).
% 0.43/0.62  thf(t92_xboole_1, axiom,
% 0.43/0.62    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.43/0.62  thf('38', plain, (![X26 : $i]: ((k5_xboole_0 @ X26 @ X26) = (k1_xboole_0))),
% 0.43/0.62      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.43/0.62  thf('39', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.43/0.62      inference('sup+', [status(thm)], ['37', '38'])).
% 0.43/0.62  thf('40', plain,
% 0.43/0.62      ((((k1_xboole_0) = (k1_tarski @ sk_A)))
% 0.43/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.43/0.62             ((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('demod', [status(thm)], ['34', '39'])).
% 0.43/0.62  thf('41', plain, (![X98 : $i]: ((k3_tarski @ (k1_tarski @ X98)) = (X98))),
% 0.43/0.62      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.43/0.62  thf('42', plain,
% 0.43/0.62      ((((k3_tarski @ k1_xboole_0) = (sk_A)))
% 0.43/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.43/0.62             ((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['40', '41'])).
% 0.43/0.62  thf('43', plain,
% 0.43/0.62      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('split', [status(esa)], ['26'])).
% 0.43/0.62  thf('44', plain,
% 0.43/0.62      (((r2_hidden @ (k3_tarski @ k1_xboole_0) @ sk_B))
% 0.43/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.43/0.62             ((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['42', '43'])).
% 0.43/0.62  thf('45', plain,
% 0.43/0.62      (![X5 : $i, X7 : $i, X8 : $i]:
% 0.43/0.62         (~ (r2_hidden @ X7 @ X5)
% 0.43/0.62          | ~ (r2_hidden @ X7 @ X8)
% 0.43/0.62          | ~ (r1_xboole_0 @ X5 @ X8))),
% 0.43/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.43/0.62  thf('46', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          (~ (r1_xboole_0 @ sk_B @ X0)
% 0.43/0.62           | ~ (r2_hidden @ (k3_tarski @ k1_xboole_0) @ X0)))
% 0.43/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.43/0.62             ((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['44', '45'])).
% 0.43/0.62  thf('47', plain,
% 0.43/0.62      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.62          ((zip_tseitin_0 @ (k3_tarski @ k1_xboole_0) @ X0 @ X1 @ X2)
% 0.43/0.62           | ~ (r1_xboole_0 @ sk_B @ (k1_enumset1 @ X2 @ X1 @ X0))))
% 0.43/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.43/0.62             ((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['11', '46'])).
% 0.43/0.62  thf('48', plain,
% 0.43/0.62      ((![X0 : $i, X1 : $i]:
% 0.43/0.62          (~ (r1_xboole_0 @ sk_B @ (k2_tarski @ X1 @ X0))
% 0.43/0.62           | (zip_tseitin_0 @ (k3_tarski @ k1_xboole_0) @ X0 @ X1 @ X1)))
% 0.43/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.43/0.62             ((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['9', '47'])).
% 0.43/0.62  thf('49', plain,
% 0.43/0.62      ((![X0 : $i]:
% 0.43/0.62          (~ (r1_xboole_0 @ sk_B @ (k1_tarski @ X0))
% 0.43/0.62           | (zip_tseitin_0 @ (k3_tarski @ k1_xboole_0) @ X0 @ X0 @ X0)))
% 0.43/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.43/0.62             ((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['8', '48'])).
% 0.43/0.62  thf('50', plain,
% 0.43/0.62      (((zip_tseitin_0 @ (k3_tarski @ k1_xboole_0) @ sk_A @ sk_A @ sk_A))
% 0.43/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.43/0.62             ((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup-', [status(thm)], ['7', '49'])).
% 0.43/0.62  thf('51', plain,
% 0.43/0.62      ((((k3_tarski @ k1_xboole_0) = (sk_A)))
% 0.43/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.43/0.62             ((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['40', '41'])).
% 0.43/0.62  thf('52', plain,
% 0.43/0.62      ((((k3_tarski @ k1_xboole_0) = (sk_A)))
% 0.43/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.43/0.62             ((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.62      inference('sup+', [status(thm)], ['40', '41'])).
% 0.43/0.62  thf('53', plain,
% 0.43/0.62      ((((k3_tarski @ k1_xboole_0) = (sk_A)))
% 0.43/0.62         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.43/0.62             ((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.63      inference('sup+', [status(thm)], ['40', '41'])).
% 0.43/0.63  thf('54', plain,
% 0.43/0.63      (((zip_tseitin_0 @ (k3_tarski @ k1_xboole_0) @ 
% 0.43/0.63         (k3_tarski @ k1_xboole_0) @ (k3_tarski @ k1_xboole_0) @ 
% 0.43/0.63         (k3_tarski @ k1_xboole_0)))
% 0.43/0.63         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.43/0.63             ((r2_hidden @ sk_A @ sk_B)))),
% 0.43/0.63      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.43/0.63  thf('55', plain,
% 0.43/0.63      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.43/0.63         (((X32) != (X31)) | ~ (zip_tseitin_0 @ X32 @ X33 @ X34 @ X31))),
% 0.43/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.43/0.63  thf('56', plain,
% 0.43/0.63      (![X31 : $i, X33 : $i, X34 : $i]:
% 0.43/0.63         ~ (zip_tseitin_0 @ X31 @ X33 @ X34 @ X31)),
% 0.43/0.63      inference('simplify', [status(thm)], ['55'])).
% 0.43/0.63  thf('57', plain,
% 0.43/0.63      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.43/0.63       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.43/0.63      inference('sup-', [status(thm)], ['54', '56'])).
% 0.43/0.63  thf('58', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.43/0.63      inference('sat_resolution*', [status(thm)], ['2', '57'])).
% 0.43/0.63  thf('59', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.43/0.63      inference('simpl_trail', [status(thm)], ['1', '58'])).
% 0.43/0.63  thf(commutativity_k2_tarski, axiom,
% 0.43/0.63    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.43/0.63  thf('60', plain,
% 0.43/0.63      (![X29 : $i, X30 : $i]:
% 0.43/0.63         ((k2_tarski @ X30 @ X29) = (k2_tarski @ X29 @ X30))),
% 0.43/0.63      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.43/0.63  thf('61', plain,
% 0.43/0.63      (![X96 : $i, X97 : $i]:
% 0.43/0.63         ((k3_tarski @ (k2_tarski @ X96 @ X97)) = (k2_xboole_0 @ X96 @ X97))),
% 0.43/0.63      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.43/0.63  thf('62', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.63      inference('sup+', [status(thm)], ['60', '61'])).
% 0.43/0.63  thf('63', plain,
% 0.43/0.63      (![X96 : $i, X97 : $i]:
% 0.43/0.63         ((k3_tarski @ (k2_tarski @ X96 @ X97)) = (k2_xboole_0 @ X96 @ X97))),
% 0.43/0.63      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.43/0.63  thf('64', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.63      inference('sup+', [status(thm)], ['62', '63'])).
% 0.43/0.63  thf('65', plain,
% 0.43/0.63      (![X94 : $i, X95 : $i]:
% 0.43/0.63         ((r1_xboole_0 @ (k1_tarski @ X94) @ X95) | (r2_hidden @ X94 @ X95))),
% 0.43/0.63      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.43/0.63  thf('66', plain,
% 0.43/0.63      (![X21 : $i, X22 : $i]:
% 0.43/0.63         (((k4_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X22) = (X21))
% 0.43/0.63          | ~ (r1_xboole_0 @ X21 @ X22))),
% 0.43/0.63      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.43/0.63  thf('67', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         ((r2_hidden @ X1 @ X0)
% 0.43/0.63          | ((k4_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0) @ X0)
% 0.43/0.63              = (k1_tarski @ X1)))),
% 0.43/0.63      inference('sup-', [status(thm)], ['65', '66'])).
% 0.43/0.63  thf('68', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         (((k4_xboole_0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X1)
% 0.43/0.63            = (k1_tarski @ X0))
% 0.43/0.63          | (r2_hidden @ X0 @ X1))),
% 0.43/0.63      inference('sup+', [status(thm)], ['64', '67'])).
% 0.43/0.63  thf('69', plain,
% 0.43/0.63      (![X19 : $i, X20 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X19 @ X20) @ X20)),
% 0.43/0.63      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.43/0.63  thf('70', plain,
% 0.43/0.63      (![X21 : $i, X22 : $i]:
% 0.43/0.63         (((k4_xboole_0 @ (k2_xboole_0 @ X21 @ X22) @ X22) = (X21))
% 0.43/0.63          | ~ (r1_xboole_0 @ X21 @ X22))),
% 0.43/0.63      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.43/0.63  thf('71', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         ((k4_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) @ X0)
% 0.43/0.63           = (k4_xboole_0 @ X1 @ X0))),
% 0.43/0.63      inference('sup-', [status(thm)], ['69', '70'])).
% 0.43/0.63  thf('72', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.43/0.63      inference('sup+', [status(thm)], ['62', '63'])).
% 0.43/0.63  thf(t39_xboole_1, axiom,
% 0.43/0.63    (![A:$i,B:$i]:
% 0.43/0.63     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.43/0.63  thf('73', plain,
% 0.43/0.63      (![X12 : $i, X13 : $i]:
% 0.43/0.63         ((k2_xboole_0 @ X12 @ (k4_xboole_0 @ X13 @ X12))
% 0.43/0.63           = (k2_xboole_0 @ X12 @ X13))),
% 0.43/0.63      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.43/0.63  thf('74', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.43/0.63           = (k4_xboole_0 @ X1 @ X0))),
% 0.43/0.63      inference('demod', [status(thm)], ['71', '72', '73'])).
% 0.43/0.63  thf('75', plain,
% 0.43/0.63      (![X0 : $i, X1 : $i]:
% 0.43/0.63         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.43/0.63          | (r2_hidden @ X0 @ X1))),
% 0.43/0.63      inference('demod', [status(thm)], ['68', '74'])).
% 0.43/0.63  thf('76', plain,
% 0.43/0.63      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))
% 0.43/0.63         <= (~
% 0.43/0.63             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.43/0.63      inference('split', [status(esa)], ['26'])).
% 0.43/0.63  thf('77', plain,
% 0.43/0.63      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.43/0.63       ((r2_hidden @ sk_A @ sk_B))),
% 0.43/0.63      inference('split', [status(esa)], ['26'])).
% 0.43/0.63  thf('78', plain,
% 0.43/0.63      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.43/0.63      inference('sat_resolution*', [status(thm)], ['2', '57', '77'])).
% 0.43/0.63  thf('79', plain,
% 0.43/0.63      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.43/0.63      inference('simpl_trail', [status(thm)], ['76', '78'])).
% 0.43/0.63  thf('80', plain,
% 0.43/0.63      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.43/0.63      inference('sup-', [status(thm)], ['75', '79'])).
% 0.43/0.63  thf('81', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.43/0.63      inference('simplify', [status(thm)], ['80'])).
% 0.43/0.63  thf('82', plain, ($false), inference('demod', [status(thm)], ['59', '81'])).
% 0.43/0.63  
% 0.43/0.63  % SZS output end Refutation
% 0.43/0.63  
% 0.50/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
