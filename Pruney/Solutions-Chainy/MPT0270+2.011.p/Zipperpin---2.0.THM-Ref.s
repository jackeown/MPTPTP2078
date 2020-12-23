%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SsuyXbfMEx

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:34:13 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  122 ( 653 expanded)
%              Number of leaves         :   33 ( 207 expanded)
%              Depth                    :   24
%              Number of atoms          : 1010 (6278 expanded)
%              Number of equality atoms :   88 ( 430 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

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
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('5',plain,
    ( ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

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

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X60: $i] :
      ( ( k2_tarski @ X60 @ X60 )
      = ( k1_tarski @ X60 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X61: $i,X62: $i] :
      ( ( k1_enumset1 @ X61 @ X61 @ X62 )
      = ( k2_tarski @ X61 @ X62 ) ) ),
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

thf('15',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X37 )
      | ( r2_hidden @ X34 @ X38 )
      | ( X38
       != ( k1_enumset1 @ X37 @ X36 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('16',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ X34 @ ( k1_enumset1 @ X37 @ X36 @ X35 ) )
      | ( zip_tseitin_0 @ X34 @ X35 @ X36 @ X37 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X60: $i] :
      ( ( k2_tarski @ X60 @ X60 )
      = ( k1_tarski @ X60 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('18',plain,(
    ! [X92: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X92 ) )
      = X92 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X90: $i,X91: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X90 @ X91 ) )
      = ( k2_xboole_0 @ X90 @ X91 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('22',plain,(
    ! [X88: $i,X89: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X88 ) @ X89 )
      | ( r2_hidden @ X88 @ X89 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('23',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,
    ( ( r1_xboole_0 @ sk_B @ ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['5','11'])).

thf('31',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
    | ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('34',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_B @ X0 )
        | ~ ( r2_hidden @ sk_A @ X0 ) )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['30','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['29','35'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('37',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ X0 )
        = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['21','38'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('40',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k4_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k3_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('43',plain,(
    ! [X24: $i] :
      ( ( k5_xboole_0 @ X24 @ X24 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( k1_xboole_0
      = ( k1_tarski @ sk_A ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X92: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X92 ) )
      = X92 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf('47',plain,
    ( ( ( k3_tarski @ k1_xboole_0 )
      = sk_A )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( r2_hidden @ sk_A @ sk_B )
   <= ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['31'])).

thf('49',plain,
    ( ( r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ sk_B )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('51',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_B @ X0 )
        | ~ ( r2_hidden @ ( k3_tarski @ k1_xboole_0 ) @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( zip_tseitin_0 @ ( k3_tarski @ k1_xboole_0 ) @ X0 @ X1 @ X2 )
        | ~ ( r1_xboole_0 @ sk_B @ ( k1_enumset1 @ X2 @ X1 @ X0 ) ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','51'])).

thf('53',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_xboole_0 @ sk_B @ ( k2_tarski @ X1 @ X0 ) )
        | ( zip_tseitin_0 @ ( k3_tarski @ k1_xboole_0 ) @ X0 @ X1 @ X1 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['14','52'])).

thf('54',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_xboole_0 @ sk_B @ ( k1_tarski @ X0 ) )
        | ( zip_tseitin_0 @ ( k3_tarski @ k1_xboole_0 ) @ X0 @ X0 @ X0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','53'])).

thf('55',plain,
    ( ( zip_tseitin_0 @ ( k3_tarski @ k1_xboole_0 ) @ sk_A @ sk_A @ sk_A )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','54'])).

thf('56',plain,
    ( ( ( k3_tarski @ k1_xboole_0 )
      = sk_A )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('57',plain,
    ( ( ( k3_tarski @ k1_xboole_0 )
      = sk_A )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('58',plain,
    ( ( ( k3_tarski @ k1_xboole_0 )
      = sk_A )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('59',plain,
    ( ( zip_tseitin_0 @ ( k3_tarski @ k1_xboole_0 ) @ ( k3_tarski @ k1_xboole_0 ) @ ( k3_tarski @ k1_xboole_0 ) @ ( k3_tarski @ k1_xboole_0 ) )
   <= ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
        = ( k1_tarski @ sk_A ) )
      & ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X30 != X29 )
      | ~ ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('61',plain,(
    ! [X29: $i,X31: $i,X32: $i] :
      ~ ( zip_tseitin_0 @ X29 @ X31 @ X32 @ X29 ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sat_resolution*',[status(thm)],['2','62'])).

thf('64',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(simpl_trail,[status(thm)],['1','63'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('65',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k2_tarski @ X28 @ X27 )
      = ( k2_tarski @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('66',plain,(
    ! [X90: $i,X91: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X90 @ X91 ) )
      = ( k2_xboole_0 @ X90 @ X91 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X90: $i,X91: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X90 @ X91 ) )
      = ( k2_xboole_0 @ X90 @ X91 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X88: $i,X89: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X88 ) @ X89 )
      | ( r2_hidden @ X88 @ X89 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('71',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ X0 ) @ X0 )
        = ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','72'])).

thf('74',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf('75',plain,(
    ! [X19: $i,X20: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X19 @ X20 ) @ X20 )
        = X19 )
      | ~ ( r1_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('78',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_xboole_0 @ X10 @ ( k4_xboole_0 @ X11 @ X10 ) )
      = ( k2_xboole_0 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['73','79'])).

thf('81',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
   <= ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['31'])).

thf('82',plain,
    ( ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference(split,[status(esa)],['31'])).

thf('83',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['2','62','82'])).

thf('84',plain,(
    ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
 != ( k1_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['81','83'])).

thf('85',plain,
    ( ( ( k1_tarski @ sk_A )
     != ( k1_tarski @ sk_A ) )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['80','84'])).

thf('86',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['64','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SsuyXbfMEx
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.58/0.79  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.58/0.79  % Solved by: fo/fo7.sh
% 0.58/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.79  % done 513 iterations in 0.330s
% 0.58/0.79  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.58/0.79  % SZS output start Refutation
% 0.58/0.79  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.58/0.79  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.58/0.79  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.58/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.79  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.79  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.58/0.79  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.79  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.79  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.58/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.79  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.79  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.58/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.79  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.58/0.79  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.58/0.79  thf(t67_zfmisc_1, conjecture,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.58/0.79       ( ~( r2_hidden @ A @ B ) ) ))).
% 0.58/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.79    (~( ![A:$i,B:$i]:
% 0.58/0.79        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_tarski @ A ) ) <=>
% 0.58/0.79          ( ~( r2_hidden @ A @ B ) ) ) )),
% 0.58/0.79    inference('cnf.neg', [status(esa)], [t67_zfmisc_1])).
% 0.58/0.79  thf('0', plain,
% 0.58/0.79      ((~ (r2_hidden @ sk_A @ sk_B)
% 0.58/0.79        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('1', plain,
% 0.58/0.79      ((~ (r2_hidden @ sk_A @ sk_B)) <= (~ ((r2_hidden @ sk_A @ sk_B)))),
% 0.58/0.79      inference('split', [status(esa)], ['0'])).
% 0.58/0.79  thf('2', plain,
% 0.58/0.79      (~ ((r2_hidden @ sk_A @ sk_B)) | 
% 0.58/0.79       (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.58/0.79      inference('split', [status(esa)], ['0'])).
% 0.58/0.79  thf('3', plain,
% 0.58/0.79      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))
% 0.58/0.79         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.58/0.79      inference('split', [status(esa)], ['0'])).
% 0.58/0.79  thf(t79_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.58/0.79  thf('4', plain,
% 0.58/0.79      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 0.58/0.79      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.58/0.79  thf('5', plain,
% 0.58/0.79      (((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_B))
% 0.58/0.79         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.58/0.79      inference('sup+', [status(thm)], ['3', '4'])).
% 0.58/0.79  thf(t3_xboole_0, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.58/0.79            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.58/0.79       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.58/0.79            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.58/0.79  thf('6', plain,
% 0.58/0.79      (![X3 : $i, X4 : $i]:
% 0.58/0.79         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.58/0.79      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.79  thf('7', plain,
% 0.58/0.79      (![X3 : $i, X4 : $i]:
% 0.58/0.79         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.58/0.79      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.79  thf('8', plain,
% 0.58/0.79      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X5 @ X3)
% 0.58/0.79          | ~ (r2_hidden @ X5 @ X6)
% 0.58/0.79          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.58/0.79      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.79  thf('9', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.79         ((r1_xboole_0 @ X1 @ X0)
% 0.58/0.79          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.58/0.79          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.58/0.79      inference('sup-', [status(thm)], ['7', '8'])).
% 0.58/0.79  thf('10', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((r1_xboole_0 @ X0 @ X1)
% 0.58/0.79          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.58/0.79          | (r1_xboole_0 @ X0 @ X1))),
% 0.58/0.79      inference('sup-', [status(thm)], ['6', '9'])).
% 0.58/0.79  thf('11', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.58/0.79      inference('simplify', [status(thm)], ['10'])).
% 0.58/0.79  thf('12', plain,
% 0.58/0.79      (((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.58/0.79         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.58/0.79      inference('sup-', [status(thm)], ['5', '11'])).
% 0.58/0.79  thf(t69_enumset1, axiom,
% 0.58/0.79    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.58/0.79  thf('13', plain,
% 0.58/0.79      (![X60 : $i]: ((k2_tarski @ X60 @ X60) = (k1_tarski @ X60))),
% 0.58/0.79      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.79  thf(t70_enumset1, axiom,
% 0.58/0.79    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.58/0.79  thf('14', plain,
% 0.58/0.79      (![X61 : $i, X62 : $i]:
% 0.58/0.79         ((k1_enumset1 @ X61 @ X61 @ X62) = (k2_tarski @ X61 @ X62))),
% 0.58/0.79      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.79  thf(d1_enumset1, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.79     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.58/0.79       ( ![E:$i]:
% 0.58/0.79         ( ( r2_hidden @ E @ D ) <=>
% 0.58/0.79           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.58/0.79  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.58/0.79  thf(zf_stmt_2, axiom,
% 0.58/0.79    (![E:$i,C:$i,B:$i,A:$i]:
% 0.58/0.79     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.58/0.79       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.58/0.79  thf(zf_stmt_3, axiom,
% 0.58/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.79     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.58/0.79       ( ![E:$i]:
% 0.58/0.79         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.58/0.79  thf('15', plain,
% 0.58/0.79      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.58/0.79         ((zip_tseitin_0 @ X34 @ X35 @ X36 @ X37)
% 0.58/0.79          | (r2_hidden @ X34 @ X38)
% 0.58/0.79          | ((X38) != (k1_enumset1 @ X37 @ X36 @ X35)))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.79  thf('16', plain,
% 0.58/0.79      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.58/0.79         ((r2_hidden @ X34 @ (k1_enumset1 @ X37 @ X36 @ X35))
% 0.58/0.79          | (zip_tseitin_0 @ X34 @ X35 @ X36 @ X37))),
% 0.58/0.79      inference('simplify', [status(thm)], ['15'])).
% 0.58/0.79  thf('17', plain,
% 0.58/0.79      (![X60 : $i]: ((k2_tarski @ X60 @ X60) = (k1_tarski @ X60))),
% 0.58/0.79      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.58/0.79  thf(t31_zfmisc_1, axiom,
% 0.58/0.79    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.58/0.79  thf('18', plain, (![X92 : $i]: ((k3_tarski @ (k1_tarski @ X92)) = (X92))),
% 0.58/0.79      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.58/0.79  thf('19', plain, (![X0 : $i]: ((k3_tarski @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.58/0.79      inference('sup+', [status(thm)], ['17', '18'])).
% 0.58/0.79  thf(l51_zfmisc_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.79  thf('20', plain,
% 0.58/0.79      (![X90 : $i, X91 : $i]:
% 0.58/0.79         ((k3_tarski @ (k2_tarski @ X90 @ X91)) = (k2_xboole_0 @ X90 @ X91))),
% 0.58/0.79      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.58/0.79  thf('21', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ X0) = (X0))),
% 0.58/0.79      inference('demod', [status(thm)], ['19', '20'])).
% 0.58/0.79  thf(l27_zfmisc_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.58/0.79  thf('22', plain,
% 0.58/0.79      (![X88 : $i, X89 : $i]:
% 0.58/0.79         ((r1_xboole_0 @ (k1_tarski @ X88) @ X89) | (r2_hidden @ X88 @ X89))),
% 0.58/0.79      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.58/0.79  thf('23', plain,
% 0.58/0.79      (![X3 : $i, X4 : $i]:
% 0.58/0.79         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.58/0.79      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.79  thf('24', plain,
% 0.58/0.79      (![X3 : $i, X4 : $i]:
% 0.58/0.79         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.58/0.79      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.79  thf('25', plain,
% 0.58/0.79      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X5 @ X3)
% 0.58/0.79          | ~ (r2_hidden @ X5 @ X6)
% 0.58/0.79          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.58/0.79      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.79  thf('26', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.79         ((r1_xboole_0 @ X0 @ X1)
% 0.58/0.79          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.58/0.79          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.58/0.79      inference('sup-', [status(thm)], ['24', '25'])).
% 0.58/0.79  thf('27', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((r1_xboole_0 @ X0 @ X1)
% 0.58/0.79          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.58/0.79          | (r1_xboole_0 @ X0 @ X1))),
% 0.58/0.79      inference('sup-', [status(thm)], ['23', '26'])).
% 0.58/0.79  thf('28', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.58/0.79      inference('simplify', [status(thm)], ['27'])).
% 0.58/0.79  thf('29', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.58/0.79          | (r1_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.58/0.79      inference('sup-', [status(thm)], ['22', '28'])).
% 0.58/0.79  thf('30', plain,
% 0.58/0.79      (((r1_xboole_0 @ sk_B @ (k1_tarski @ sk_A)))
% 0.58/0.79         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.58/0.79      inference('sup-', [status(thm)], ['5', '11'])).
% 0.58/0.79  thf('31', plain,
% 0.58/0.79      (((r2_hidden @ sk_A @ sk_B)
% 0.58/0.79        | ((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.79  thf('32', plain,
% 0.58/0.79      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.58/0.79      inference('split', [status(esa)], ['31'])).
% 0.58/0.79  thf('33', plain,
% 0.58/0.79      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X5 @ X3)
% 0.58/0.79          | ~ (r2_hidden @ X5 @ X6)
% 0.58/0.79          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.58/0.79      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.79  thf('34', plain,
% 0.58/0.79      ((![X0 : $i]: (~ (r1_xboole_0 @ sk_B @ X0) | ~ (r2_hidden @ sk_A @ X0)))
% 0.58/0.79         <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['32', '33'])).
% 0.58/0.79  thf('35', plain,
% 0.58/0.79      ((~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A)))
% 0.58/0.79         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.58/0.79             ((r2_hidden @ sk_A @ sk_B)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['30', '34'])).
% 0.58/0.79  thf('36', plain,
% 0.58/0.79      ((![X0 : $i]: (r1_xboole_0 @ (k1_tarski @ sk_A) @ X0))
% 0.58/0.79         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.58/0.79             ((r2_hidden @ sk_A @ sk_B)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['29', '35'])).
% 0.58/0.79  thf(t88_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( r1_xboole_0 @ A @ B ) =>
% 0.58/0.79       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.58/0.79  thf('37', plain,
% 0.58/0.79      (![X19 : $i, X20 : $i]:
% 0.58/0.79         (((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X20) = (X19))
% 0.58/0.79          | ~ (r1_xboole_0 @ X19 @ X20))),
% 0.58/0.79      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.58/0.79  thf('38', plain,
% 0.58/0.79      ((![X0 : $i]:
% 0.58/0.79          ((k4_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ X0)
% 0.58/0.79            = (k1_tarski @ sk_A)))
% 0.58/0.79         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.58/0.79             ((r2_hidden @ sk_A @ sk_B)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['36', '37'])).
% 0.58/0.79  thf('39', plain,
% 0.58/0.79      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A))
% 0.58/0.79          = (k1_tarski @ sk_A)))
% 0.58/0.79         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.58/0.79             ((r2_hidden @ sk_A @ sk_B)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['21', '38'])).
% 0.58/0.79  thf(idempotence_k3_xboole_0, axiom,
% 0.58/0.79    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.58/0.79  thf('40', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.58/0.79      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.58/0.79  thf(t100_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.58/0.79  thf('41', plain,
% 0.58/0.79      (![X7 : $i, X8 : $i]:
% 0.58/0.79         ((k4_xboole_0 @ X7 @ X8)
% 0.58/0.79           = (k5_xboole_0 @ X7 @ (k3_xboole_0 @ X7 @ X8)))),
% 0.58/0.79      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.58/0.79  thf('42', plain,
% 0.58/0.79      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.58/0.79      inference('sup+', [status(thm)], ['40', '41'])).
% 0.58/0.79  thf(t92_xboole_1, axiom,
% 0.58/0.79    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.58/0.79  thf('43', plain, (![X24 : $i]: ((k5_xboole_0 @ X24 @ X24) = (k1_xboole_0))),
% 0.58/0.79      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.58/0.79  thf('44', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.58/0.79      inference('sup+', [status(thm)], ['42', '43'])).
% 0.58/0.79  thf('45', plain,
% 0.58/0.79      ((((k1_xboole_0) = (k1_tarski @ sk_A)))
% 0.58/0.79         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.58/0.79             ((r2_hidden @ sk_A @ sk_B)))),
% 0.58/0.79      inference('demod', [status(thm)], ['39', '44'])).
% 0.58/0.79  thf('46', plain, (![X92 : $i]: ((k3_tarski @ (k1_tarski @ X92)) = (X92))),
% 0.58/0.79      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.58/0.79  thf('47', plain,
% 0.58/0.79      ((((k3_tarski @ k1_xboole_0) = (sk_A)))
% 0.58/0.79         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.58/0.79             ((r2_hidden @ sk_A @ sk_B)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['45', '46'])).
% 0.58/0.79  thf('48', plain,
% 0.58/0.79      (((r2_hidden @ sk_A @ sk_B)) <= (((r2_hidden @ sk_A @ sk_B)))),
% 0.58/0.79      inference('split', [status(esa)], ['31'])).
% 0.58/0.79  thf('49', plain,
% 0.58/0.79      (((r2_hidden @ (k3_tarski @ k1_xboole_0) @ sk_B))
% 0.58/0.79         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.58/0.79             ((r2_hidden @ sk_A @ sk_B)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['47', '48'])).
% 0.58/0.79  thf('50', plain,
% 0.58/0.79      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.58/0.79         (~ (r2_hidden @ X5 @ X3)
% 0.58/0.79          | ~ (r2_hidden @ X5 @ X6)
% 0.58/0.79          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.58/0.79      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.58/0.79  thf('51', plain,
% 0.58/0.79      ((![X0 : $i]:
% 0.58/0.79          (~ (r1_xboole_0 @ sk_B @ X0)
% 0.58/0.79           | ~ (r2_hidden @ (k3_tarski @ k1_xboole_0) @ X0)))
% 0.58/0.79         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.58/0.79             ((r2_hidden @ sk_A @ sk_B)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['49', '50'])).
% 0.58/0.79  thf('52', plain,
% 0.58/0.79      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.79          ((zip_tseitin_0 @ (k3_tarski @ k1_xboole_0) @ X0 @ X1 @ X2)
% 0.58/0.79           | ~ (r1_xboole_0 @ sk_B @ (k1_enumset1 @ X2 @ X1 @ X0))))
% 0.58/0.79         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.58/0.79             ((r2_hidden @ sk_A @ sk_B)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['16', '51'])).
% 0.58/0.79  thf('53', plain,
% 0.58/0.79      ((![X0 : $i, X1 : $i]:
% 0.58/0.79          (~ (r1_xboole_0 @ sk_B @ (k2_tarski @ X1 @ X0))
% 0.58/0.79           | (zip_tseitin_0 @ (k3_tarski @ k1_xboole_0) @ X0 @ X1 @ X1)))
% 0.58/0.79         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.58/0.79             ((r2_hidden @ sk_A @ sk_B)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['14', '52'])).
% 0.58/0.79  thf('54', plain,
% 0.58/0.79      ((![X0 : $i]:
% 0.58/0.79          (~ (r1_xboole_0 @ sk_B @ (k1_tarski @ X0))
% 0.58/0.79           | (zip_tseitin_0 @ (k3_tarski @ k1_xboole_0) @ X0 @ X0 @ X0)))
% 0.58/0.79         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.58/0.79             ((r2_hidden @ sk_A @ sk_B)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['13', '53'])).
% 0.58/0.79  thf('55', plain,
% 0.58/0.79      (((zip_tseitin_0 @ (k3_tarski @ k1_xboole_0) @ sk_A @ sk_A @ sk_A))
% 0.58/0.79         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.58/0.79             ((r2_hidden @ sk_A @ sk_B)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['12', '54'])).
% 0.58/0.79  thf('56', plain,
% 0.58/0.79      ((((k3_tarski @ k1_xboole_0) = (sk_A)))
% 0.58/0.79         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.58/0.79             ((r2_hidden @ sk_A @ sk_B)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['45', '46'])).
% 0.58/0.79  thf('57', plain,
% 0.58/0.79      ((((k3_tarski @ k1_xboole_0) = (sk_A)))
% 0.58/0.79         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.58/0.79             ((r2_hidden @ sk_A @ sk_B)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['45', '46'])).
% 0.58/0.79  thf('58', plain,
% 0.58/0.79      ((((k3_tarski @ k1_xboole_0) = (sk_A)))
% 0.58/0.79         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.58/0.79             ((r2_hidden @ sk_A @ sk_B)))),
% 0.58/0.79      inference('sup+', [status(thm)], ['45', '46'])).
% 0.58/0.79  thf('59', plain,
% 0.58/0.79      (((zip_tseitin_0 @ (k3_tarski @ k1_xboole_0) @ 
% 0.58/0.79         (k3_tarski @ k1_xboole_0) @ (k3_tarski @ k1_xboole_0) @ 
% 0.58/0.79         (k3_tarski @ k1_xboole_0)))
% 0.58/0.79         <= ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) & 
% 0.58/0.79             ((r2_hidden @ sk_A @ sk_B)))),
% 0.58/0.79      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.58/0.79  thf('60', plain,
% 0.58/0.79      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.58/0.79         (((X30) != (X29)) | ~ (zip_tseitin_0 @ X30 @ X31 @ X32 @ X29))),
% 0.58/0.79      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.79  thf('61', plain,
% 0.58/0.79      (![X29 : $i, X31 : $i, X32 : $i]:
% 0.58/0.79         ~ (zip_tseitin_0 @ X29 @ X31 @ X32 @ X29)),
% 0.58/0.79      inference('simplify', [status(thm)], ['60'])).
% 0.58/0.79  thf('62', plain,
% 0.58/0.79      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.58/0.79       ~ ((r2_hidden @ sk_A @ sk_B))),
% 0.58/0.79      inference('sup-', [status(thm)], ['59', '61'])).
% 0.58/0.79  thf('63', plain, (~ ((r2_hidden @ sk_A @ sk_B))),
% 0.58/0.79      inference('sat_resolution*', [status(thm)], ['2', '62'])).
% 0.58/0.79  thf('64', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.58/0.79      inference('simpl_trail', [status(thm)], ['1', '63'])).
% 0.58/0.79  thf(commutativity_k2_tarski, axiom,
% 0.58/0.79    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.58/0.79  thf('65', plain,
% 0.58/0.79      (![X27 : $i, X28 : $i]:
% 0.58/0.79         ((k2_tarski @ X28 @ X27) = (k2_tarski @ X27 @ X28))),
% 0.58/0.79      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.58/0.79  thf('66', plain,
% 0.58/0.79      (![X90 : $i, X91 : $i]:
% 0.58/0.79         ((k3_tarski @ (k2_tarski @ X90 @ X91)) = (k2_xboole_0 @ X90 @ X91))),
% 0.58/0.79      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.58/0.79  thf('67', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.79      inference('sup+', [status(thm)], ['65', '66'])).
% 0.58/0.79  thf('68', plain,
% 0.58/0.79      (![X90 : $i, X91 : $i]:
% 0.58/0.79         ((k3_tarski @ (k2_tarski @ X90 @ X91)) = (k2_xboole_0 @ X90 @ X91))),
% 0.58/0.79      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.58/0.79  thf('69', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.79      inference('sup+', [status(thm)], ['67', '68'])).
% 0.58/0.79  thf('70', plain,
% 0.58/0.79      (![X88 : $i, X89 : $i]:
% 0.58/0.79         ((r1_xboole_0 @ (k1_tarski @ X88) @ X89) | (r2_hidden @ X88 @ X89))),
% 0.58/0.79      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.58/0.79  thf('71', plain,
% 0.58/0.79      (![X19 : $i, X20 : $i]:
% 0.58/0.79         (((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X20) = (X19))
% 0.58/0.79          | ~ (r1_xboole_0 @ X19 @ X20))),
% 0.58/0.79      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.58/0.79  thf('72', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((r2_hidden @ X1 @ X0)
% 0.58/0.79          | ((k4_xboole_0 @ (k2_xboole_0 @ (k1_tarski @ X1) @ X0) @ X0)
% 0.58/0.79              = (k1_tarski @ X1)))),
% 0.58/0.79      inference('sup-', [status(thm)], ['70', '71'])).
% 0.58/0.79  thf('73', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (((k4_xboole_0 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)) @ X1)
% 0.58/0.79            = (k1_tarski @ X0))
% 0.58/0.79          | (r2_hidden @ X0 @ X1))),
% 0.58/0.79      inference('sup+', [status(thm)], ['69', '72'])).
% 0.58/0.79  thf('74', plain,
% 0.58/0.79      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 0.58/0.79      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.58/0.79  thf('75', plain,
% 0.58/0.79      (![X19 : $i, X20 : $i]:
% 0.58/0.79         (((k4_xboole_0 @ (k2_xboole_0 @ X19 @ X20) @ X20) = (X19))
% 0.58/0.79          | ~ (r1_xboole_0 @ X19 @ X20))),
% 0.58/0.79      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.58/0.79  thf('76', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((k4_xboole_0 @ (k2_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0) @ X0)
% 0.58/0.79           = (k4_xboole_0 @ X1 @ X0))),
% 0.58/0.79      inference('sup-', [status(thm)], ['74', '75'])).
% 0.58/0.79  thf('77', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.58/0.79      inference('sup+', [status(thm)], ['67', '68'])).
% 0.58/0.79  thf(t39_xboole_1, axiom,
% 0.58/0.79    (![A:$i,B:$i]:
% 0.58/0.79     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.58/0.79  thf('78', plain,
% 0.58/0.79      (![X10 : $i, X11 : $i]:
% 0.58/0.79         ((k2_xboole_0 @ X10 @ (k4_xboole_0 @ X11 @ X10))
% 0.58/0.79           = (k2_xboole_0 @ X10 @ X11))),
% 0.58/0.79      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.58/0.79  thf('79', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.58/0.79           = (k4_xboole_0 @ X1 @ X0))),
% 0.58/0.79      inference('demod', [status(thm)], ['76', '77', '78'])).
% 0.58/0.79  thf('80', plain,
% 0.58/0.79      (![X0 : $i, X1 : $i]:
% 0.58/0.79         (((k4_xboole_0 @ (k1_tarski @ X0) @ X1) = (k1_tarski @ X0))
% 0.58/0.79          | (r2_hidden @ X0 @ X1))),
% 0.58/0.79      inference('demod', [status(thm)], ['73', '79'])).
% 0.58/0.79  thf('81', plain,
% 0.58/0.79      ((((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A)))
% 0.58/0.79         <= (~
% 0.58/0.79             (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))))),
% 0.58/0.79      inference('split', [status(esa)], ['31'])).
% 0.58/0.79  thf('82', plain,
% 0.58/0.79      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A))) | 
% 0.58/0.79       ((r2_hidden @ sk_A @ sk_B))),
% 0.58/0.79      inference('split', [status(esa)], ['31'])).
% 0.58/0.79  thf('83', plain,
% 0.58/0.79      (~ (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_tarski @ sk_A)))),
% 0.58/0.79      inference('sat_resolution*', [status(thm)], ['2', '62', '82'])).
% 0.58/0.79  thf('84', plain,
% 0.58/0.79      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) != (k1_tarski @ sk_A))),
% 0.58/0.79      inference('simpl_trail', [status(thm)], ['81', '83'])).
% 0.58/0.79  thf('85', plain,
% 0.58/0.79      ((((k1_tarski @ sk_A) != (k1_tarski @ sk_A)) | (r2_hidden @ sk_A @ sk_B))),
% 0.58/0.79      inference('sup-', [status(thm)], ['80', '84'])).
% 0.58/0.79  thf('86', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.58/0.79      inference('simplify', [status(thm)], ['85'])).
% 0.58/0.79  thf('87', plain, ($false), inference('demod', [status(thm)], ['64', '86'])).
% 0.58/0.79  
% 0.58/0.79  % SZS output end Refutation
% 0.58/0.79  
% 0.58/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
