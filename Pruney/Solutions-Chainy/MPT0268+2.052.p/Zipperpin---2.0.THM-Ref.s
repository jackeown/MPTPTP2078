%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RFoLZi9evb

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:59 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 153 expanded)
%              Number of leaves         :   27 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  903 (1520 expanded)
%              Number of equality atoms :   85 ( 145 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(t65_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
          = A )
      <=> ~ ( r2_hidden @ B @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t65_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
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

thf('3',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( r2_hidden @ X21 @ X25 )
      | ( X25
       != ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X21 @ ( k1_enumset1 @ X24 @ X23 @ X22 ) )
      | ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X16 )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ~ ( zip_tseitin_0 @ X16 @ X18 @ X19 @ X16 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 )
      | ( X17 = X18 )
      | ( X17 = X19 )
      | ( X17 = X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('12',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X28: $i] :
      ( ( k2_tarski @ X28 @ X28 )
      = ( k1_tarski @ X28 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('16',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k1_enumset1 @ X29 @ X29 @ X30 )
      = ( k2_tarski @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('17',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X26 @ X25 )
      | ~ ( zip_tseitin_0 @ X26 @ X22 @ X23 @ X24 )
      | ( X25
       != ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('18',plain,(
    ! [X22: $i,X23: $i,X24: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X22 @ X23 @ X24 )
      | ~ ( r2_hidden @ X26 @ ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ~ ( zip_tseitin_0 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 ) @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k4_xboole_0 @ X0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ X0 ) @ X1 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference(condensation,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
        = ( k4_xboole_0 @ X1 @ X1 ) )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ X1 @ X1 )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('35',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['37'])).

thf('39',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_A )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ! [X0: $i] :
        ( ( ( k1_tarski @ sk_B )
          = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) )
        | ~ ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_B ) @ X0 @ ( k1_tarski @ sk_B ) ) @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['36','40'])).

thf('42',plain,
    ( ( ~ ( r2_hidden @ sk_B @ sk_A )
      | ( ( k1_tarski @ sk_B )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
      | ( ( k1_tarski @ sk_B )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,
    ( ( ( ( k1_tarski @ sk_B )
        = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
      | ~ ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','43'])).

thf('45',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
        | ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_B ) )
   <= ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
        = sk_A )
      & ( r2_hidden @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['32','47'])).

thf('49',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference(split,[status(esa)],['37'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('50',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X38 ) @ X39 )
      | ( r2_hidden @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('51',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('53',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k5_xboole_0 @ ( k1_tarski @ X1 ) @ k1_xboole_0 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('55',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ X1 ) @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('57',plain,(
    ! [X14: $i,X15: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X14 @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('58',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ~ ( r1_xboole_0 @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ X12 )
      = ( k5_xboole_0 @ X11 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X13: $i] :
      ( ( k5_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k1_tarski @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['56','65'])).

thf('67',plain,
    ( ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('68',plain,
    ( ( ( sk_A != sk_A )
      | ( r2_hidden @ sk_B @ sk_A ) )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
   <= ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
     != sk_A ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_A )
   <= ~ ( r2_hidden @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['37'])).

thf('71',plain,
    ( ( r2_hidden @ sk_B @ sk_A )
    | ( ( k4_xboole_0 @ sk_A @ ( k1_tarski @ sk_B ) )
      = sk_A ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','48','49','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RFoLZi9evb
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:11:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.70/0.86  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.86  % Solved by: fo/fo7.sh
% 0.70/0.86  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.86  % done 608 iterations in 0.407s
% 0.70/0.86  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.86  % SZS output start Refutation
% 0.70/0.86  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.86  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.70/0.86  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.70/0.86  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.86  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.70/0.86  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.70/0.86  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.70/0.86  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.70/0.86  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.86  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.70/0.86  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.86  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.70/0.86  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.70/0.86  thf(t65_zfmisc_1, conjecture,
% 0.70/0.86    (![A:$i,B:$i]:
% 0.70/0.86     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.70/0.86       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.70/0.86  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.86    (~( ![A:$i,B:$i]:
% 0.70/0.86        ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.70/0.86          ( ~( r2_hidden @ B @ A ) ) ) )),
% 0.70/0.86    inference('cnf.neg', [status(esa)], [t65_zfmisc_1])).
% 0.70/0.86  thf('0', plain,
% 0.70/0.86      (((r2_hidden @ sk_B @ sk_A)
% 0.70/0.86        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))),
% 0.70/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.86  thf('1', plain,
% 0.70/0.86      (((r2_hidden @ sk_B @ sk_A)) | 
% 0.70/0.86       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.70/0.86      inference('split', [status(esa)], ['0'])).
% 0.70/0.86  thf(t70_enumset1, axiom,
% 0.70/0.86    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.70/0.86  thf('2', plain,
% 0.70/0.86      (![X29 : $i, X30 : $i]:
% 0.70/0.86         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.70/0.86      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.70/0.86  thf(d1_enumset1, axiom,
% 0.70/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.86     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.70/0.86       ( ![E:$i]:
% 0.70/0.86         ( ( r2_hidden @ E @ D ) <=>
% 0.70/0.86           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.70/0.86  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.70/0.86  thf(zf_stmt_2, axiom,
% 0.70/0.86    (![E:$i,C:$i,B:$i,A:$i]:
% 0.70/0.86     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.70/0.86       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.70/0.86  thf(zf_stmt_3, axiom,
% 0.70/0.86    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.86     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.70/0.86       ( ![E:$i]:
% 0.70/0.86         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.70/0.86  thf('3', plain,
% 0.70/0.86      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.70/0.86         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 0.70/0.86          | (r2_hidden @ X21 @ X25)
% 0.70/0.86          | ((X25) != (k1_enumset1 @ X24 @ X23 @ X22)))),
% 0.70/0.86      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.70/0.86  thf('4', plain,
% 0.70/0.86      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.70/0.86         ((r2_hidden @ X21 @ (k1_enumset1 @ X24 @ X23 @ X22))
% 0.70/0.86          | (zip_tseitin_0 @ X21 @ X22 @ X23 @ X24))),
% 0.70/0.86      inference('simplify', [status(thm)], ['3'])).
% 0.70/0.86  thf('5', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.86         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.70/0.86          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.70/0.86      inference('sup+', [status(thm)], ['2', '4'])).
% 0.70/0.86  thf('6', plain,
% 0.70/0.86      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.70/0.86         (((X17) != (X16)) | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X16))),
% 0.70/0.86      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.70/0.86  thf('7', plain,
% 0.70/0.86      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.70/0.86         ~ (zip_tseitin_0 @ X16 @ X18 @ X19 @ X16)),
% 0.70/0.86      inference('simplify', [status(thm)], ['6'])).
% 0.70/0.86  thf('8', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.70/0.86      inference('sup-', [status(thm)], ['5', '7'])).
% 0.70/0.86  thf(t69_enumset1, axiom,
% 0.70/0.86    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.70/0.86  thf('9', plain, (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.70/0.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.70/0.86  thf('10', plain,
% 0.70/0.86      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.70/0.86         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 0.70/0.86          | ((X17) = (X18))
% 0.70/0.86          | ((X17) = (X19))
% 0.70/0.86          | ((X17) = (X20)))),
% 0.70/0.86      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.70/0.86  thf(d5_xboole_0, axiom,
% 0.70/0.86    (![A:$i,B:$i,C:$i]:
% 0.70/0.86     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.70/0.86       ( ![D:$i]:
% 0.70/0.86         ( ( r2_hidden @ D @ C ) <=>
% 0.70/0.86           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.70/0.86  thf('11', plain,
% 0.70/0.86      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.70/0.86         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.70/0.86          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.70/0.86          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.70/0.86      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.70/0.86  thf('12', plain,
% 0.70/0.86      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.70/0.86         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.70/0.86          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.70/0.86          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.70/0.86      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.70/0.86  thf('13', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]:
% 0.70/0.86         ((r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.70/0.86          | ((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.70/0.86          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1)
% 0.70/0.86          | ((X1) = (k4_xboole_0 @ X0 @ X0)))),
% 0.70/0.86      inference('sup-', [status(thm)], ['11', '12'])).
% 0.70/0.86  thf('14', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]:
% 0.70/0.86         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.70/0.86          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.70/0.86      inference('simplify', [status(thm)], ['13'])).
% 0.70/0.86  thf('15', plain,
% 0.70/0.86      (![X28 : $i]: ((k2_tarski @ X28 @ X28) = (k1_tarski @ X28))),
% 0.70/0.86      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.70/0.86  thf('16', plain,
% 0.70/0.86      (![X29 : $i, X30 : $i]:
% 0.70/0.86         ((k1_enumset1 @ X29 @ X29 @ X30) = (k2_tarski @ X29 @ X30))),
% 0.70/0.86      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.70/0.86  thf('17', plain,
% 0.70/0.86      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.70/0.86         (~ (r2_hidden @ X26 @ X25)
% 0.70/0.86          | ~ (zip_tseitin_0 @ X26 @ X22 @ X23 @ X24)
% 0.70/0.86          | ((X25) != (k1_enumset1 @ X24 @ X23 @ X22)))),
% 0.70/0.86      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.70/0.86  thf('18', plain,
% 0.70/0.86      (![X22 : $i, X23 : $i, X24 : $i, X26 : $i]:
% 0.70/0.86         (~ (zip_tseitin_0 @ X26 @ X22 @ X23 @ X24)
% 0.70/0.86          | ~ (r2_hidden @ X26 @ (k1_enumset1 @ X24 @ X23 @ X22)))),
% 0.70/0.86      inference('simplify', [status(thm)], ['17'])).
% 0.70/0.86  thf('19', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.86         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.70/0.86          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.70/0.86      inference('sup-', [status(thm)], ['16', '18'])).
% 0.70/0.86  thf('20', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]:
% 0.70/0.86         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.70/0.86          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.70/0.86      inference('sup-', [status(thm)], ['15', '19'])).
% 0.70/0.86  thf('21', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]:
% 0.70/0.86         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 0.70/0.86          | ~ (zip_tseitin_0 @ (sk_D @ (k1_tarski @ X0) @ X1 @ X1) @ X0 @ X0 @ 
% 0.70/0.86               X0))),
% 0.70/0.86      inference('sup-', [status(thm)], ['14', '20'])).
% 0.70/0.86  thf('22', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]:
% 0.70/0.86         (((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))
% 0.70/0.86          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))
% 0.70/0.86          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0))
% 0.70/0.86          | ((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 0.70/0.86      inference('sup-', [status(thm)], ['10', '21'])).
% 0.70/0.86  thf('23', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]:
% 0.70/0.86         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 0.70/0.86          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0)))),
% 0.70/0.86      inference('simplify', [status(thm)], ['22'])).
% 0.70/0.86  thf('24', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]:
% 0.70/0.86         (((X1) = (k4_xboole_0 @ X0 @ X0))
% 0.70/0.86          | (r2_hidden @ (sk_D @ X1 @ X0 @ X0) @ X1))),
% 0.70/0.86      inference('simplify', [status(thm)], ['13'])).
% 0.70/0.86  thf('25', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]:
% 0.70/0.86         ((r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.70/0.86          | ((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 0.70/0.86          | ((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1)))),
% 0.70/0.86      inference('sup+', [status(thm)], ['23', '24'])).
% 0.70/0.86  thf('26', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]:
% 0.70/0.86         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 0.70/0.86          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.70/0.86      inference('simplify', [status(thm)], ['25'])).
% 0.70/0.86  thf('27', plain,
% 0.70/0.86      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.70/0.86         (~ (r2_hidden @ X4 @ X3)
% 0.70/0.86          | ~ (r2_hidden @ X4 @ X2)
% 0.70/0.86          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.70/0.86      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.70/0.86  thf('28', plain,
% 0.70/0.86      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.70/0.86         (~ (r2_hidden @ X4 @ X2)
% 0.70/0.86          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.70/0.86      inference('simplify', [status(thm)], ['27'])).
% 0.70/0.86  thf('29', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.86         (~ (r2_hidden @ X2 @ (k1_tarski @ X0))
% 0.70/0.86          | (r2_hidden @ X0 @ (k1_tarski @ X0))
% 0.70/0.86          | ~ (r2_hidden @ X2 @ X1))),
% 0.70/0.86      inference('sup-', [status(thm)], ['26', '28'])).
% 0.70/0.86  thf('30', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]:
% 0.70/0.86         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.70/0.86          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.70/0.86      inference('condensation', [status(thm)], ['29'])).
% 0.70/0.86  thf('31', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]:
% 0.70/0.86         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0))
% 0.70/0.86          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.70/0.86      inference('sup-', [status(thm)], ['9', '30'])).
% 0.70/0.86  thf('32', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.70/0.86      inference('sup-', [status(thm)], ['8', '31'])).
% 0.70/0.86  thf('33', plain,
% 0.70/0.86      (((r2_hidden @ sk_B @ sk_A)) <= (((r2_hidden @ sk_B @ sk_A)))),
% 0.70/0.86      inference('split', [status(esa)], ['0'])).
% 0.70/0.86  thf('34', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]:
% 0.70/0.86         (((k1_tarski @ X0) = (k4_xboole_0 @ X1 @ X1))
% 0.70/0.86          | ((sk_D @ (k1_tarski @ X0) @ X1 @ X1) = (X0)))),
% 0.70/0.86      inference('simplify', [status(thm)], ['22'])).
% 0.70/0.86  thf('35', plain,
% 0.70/0.86      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.70/0.86         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.70/0.86          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.70/0.86          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.70/0.86      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.70/0.86  thf('36', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]:
% 0.70/0.86         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 0.70/0.86          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.70/0.86      inference('eq_fact', [status(thm)], ['35'])).
% 0.70/0.86  thf('37', plain,
% 0.70/0.86      ((~ (r2_hidden @ sk_B @ sk_A)
% 0.70/0.86        | ((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.70/0.86      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.86  thf('38', plain,
% 0.70/0.86      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))
% 0.70/0.86         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.70/0.86      inference('split', [status(esa)], ['37'])).
% 0.70/0.86  thf('39', plain,
% 0.70/0.86      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.70/0.86         (~ (r2_hidden @ X4 @ X2)
% 0.70/0.86          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.70/0.86      inference('simplify', [status(thm)], ['27'])).
% 0.70/0.86  thf('40', plain,
% 0.70/0.86      ((![X0 : $i]:
% 0.70/0.86          (~ (r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 0.70/0.86         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.70/0.86      inference('sup-', [status(thm)], ['38', '39'])).
% 0.70/0.86  thf('41', plain,
% 0.70/0.86      ((![X0 : $i]:
% 0.70/0.86          (((k1_tarski @ sk_B) = (k4_xboole_0 @ (k1_tarski @ sk_B) @ X0))
% 0.70/0.86           | ~ (r2_hidden @ 
% 0.70/0.86                (sk_D @ (k1_tarski @ sk_B) @ X0 @ (k1_tarski @ sk_B)) @ sk_A)))
% 0.70/0.86         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.70/0.86      inference('sup-', [status(thm)], ['36', '40'])).
% 0.70/0.86  thf('42', plain,
% 0.70/0.86      (((~ (r2_hidden @ sk_B @ sk_A)
% 0.70/0.86         | ((k1_tarski @ sk_B)
% 0.70/0.86             = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))
% 0.70/0.86         | ((k1_tarski @ sk_B)
% 0.70/0.86             = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))))
% 0.70/0.86         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.70/0.86      inference('sup-', [status(thm)], ['34', '41'])).
% 0.70/0.86  thf('43', plain,
% 0.70/0.86      (((((k1_tarski @ sk_B)
% 0.70/0.86           = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B)))
% 0.70/0.86         | ~ (r2_hidden @ sk_B @ sk_A)))
% 0.70/0.86         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.70/0.86      inference('simplify', [status(thm)], ['42'])).
% 0.70/0.86  thf('44', plain,
% 0.70/0.86      ((((k1_tarski @ sk_B)
% 0.70/0.86          = (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_B))))
% 0.70/0.86         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.70/0.86             ((r2_hidden @ sk_B @ sk_A)))),
% 0.70/0.86      inference('sup-', [status(thm)], ['33', '43'])).
% 0.70/0.86  thf('45', plain,
% 0.70/0.86      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.70/0.86         (~ (r2_hidden @ X4 @ X2)
% 0.70/0.86          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.70/0.86      inference('simplify', [status(thm)], ['27'])).
% 0.70/0.86  thf('46', plain,
% 0.70/0.86      ((![X0 : $i]:
% 0.70/0.86          (~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))
% 0.70/0.86           | ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B))))
% 0.70/0.86         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.70/0.86             ((r2_hidden @ sk_B @ sk_A)))),
% 0.70/0.86      inference('sup-', [status(thm)], ['44', '45'])).
% 0.70/0.86  thf('47', plain,
% 0.70/0.86      ((![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_B)))
% 0.70/0.86         <= ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))) & 
% 0.70/0.86             ((r2_hidden @ sk_B @ sk_A)))),
% 0.70/0.86      inference('simplify', [status(thm)], ['46'])).
% 0.70/0.86  thf('48', plain,
% 0.70/0.86      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.70/0.86       ~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.70/0.86      inference('sup-', [status(thm)], ['32', '47'])).
% 0.70/0.86  thf('49', plain,
% 0.70/0.86      (~ ((r2_hidden @ sk_B @ sk_A)) | 
% 0.70/0.86       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.70/0.86      inference('split', [status(esa)], ['37'])).
% 0.70/0.86  thf(l27_zfmisc_1, axiom,
% 0.70/0.86    (![A:$i,B:$i]:
% 0.70/0.86     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.70/0.86  thf('50', plain,
% 0.70/0.86      (![X38 : $i, X39 : $i]:
% 0.70/0.86         ((r1_xboole_0 @ (k1_tarski @ X38) @ X39) | (r2_hidden @ X38 @ X39))),
% 0.70/0.86      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.70/0.86  thf(d7_xboole_0, axiom,
% 0.70/0.86    (![A:$i,B:$i]:
% 0.70/0.86     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.70/0.86       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.70/0.86  thf('51', plain,
% 0.70/0.86      (![X6 : $i, X7 : $i]:
% 0.70/0.86         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.70/0.86      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.70/0.86  thf('52', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]:
% 0.70/0.86         ((r2_hidden @ X1 @ X0)
% 0.70/0.86          | ((k3_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_xboole_0)))),
% 0.70/0.86      inference('sup-', [status(thm)], ['50', '51'])).
% 0.70/0.86  thf(t100_xboole_1, axiom,
% 0.70/0.86    (![A:$i,B:$i]:
% 0.70/0.86     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.70/0.86  thf('53', plain,
% 0.70/0.86      (![X11 : $i, X12 : $i]:
% 0.70/0.86         ((k4_xboole_0 @ X11 @ X12)
% 0.70/0.86           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.70/0.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.70/0.86  thf('54', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]:
% 0.70/0.86         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0)
% 0.70/0.86            = (k5_xboole_0 @ (k1_tarski @ X1) @ k1_xboole_0))
% 0.70/0.86          | (r2_hidden @ X1 @ X0))),
% 0.70/0.86      inference('sup+', [status(thm)], ['52', '53'])).
% 0.70/0.86  thf(t5_boole, axiom,
% 0.70/0.86    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.70/0.86  thf('55', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.70/0.86      inference('cnf', [status(esa)], [t5_boole])).
% 0.70/0.86  thf('56', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]:
% 0.70/0.86         (((k4_xboole_0 @ (k1_tarski @ X1) @ X0) = (k1_tarski @ X1))
% 0.70/0.86          | (r2_hidden @ X1 @ X0))),
% 0.70/0.86      inference('demod', [status(thm)], ['54', '55'])).
% 0.70/0.86  thf(t79_xboole_1, axiom,
% 0.70/0.86    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.70/0.86  thf('57', plain,
% 0.70/0.86      (![X14 : $i, X15 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X14 @ X15) @ X15)),
% 0.70/0.86      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.70/0.86  thf(symmetry_r1_xboole_0, axiom,
% 0.70/0.86    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.70/0.86  thf('58', plain,
% 0.70/0.86      (![X9 : $i, X10 : $i]:
% 0.70/0.86         ((r1_xboole_0 @ X9 @ X10) | ~ (r1_xboole_0 @ X10 @ X9))),
% 0.70/0.86      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.70/0.86  thf('59', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 0.70/0.86      inference('sup-', [status(thm)], ['57', '58'])).
% 0.70/0.86  thf('60', plain,
% 0.70/0.86      (![X6 : $i, X7 : $i]:
% 0.70/0.86         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.70/0.86      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.70/0.86  thf('61', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]:
% 0.70/0.86         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.70/0.86      inference('sup-', [status(thm)], ['59', '60'])).
% 0.70/0.86  thf('62', plain,
% 0.70/0.86      (![X11 : $i, X12 : $i]:
% 0.70/0.86         ((k4_xboole_0 @ X11 @ X12)
% 0.70/0.86           = (k5_xboole_0 @ X11 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.70/0.86      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.70/0.86  thf('63', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]:
% 0.70/0.86         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))
% 0.70/0.86           = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.70/0.86      inference('sup+', [status(thm)], ['61', '62'])).
% 0.70/0.86  thf('64', plain, (![X13 : $i]: ((k5_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.70/0.86      inference('cnf', [status(esa)], [t5_boole])).
% 0.70/0.86  thf('65', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]:
% 0.70/0.86         ((k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X0))),
% 0.70/0.86      inference('demod', [status(thm)], ['63', '64'])).
% 0.70/0.86  thf('66', plain,
% 0.70/0.86      (![X0 : $i, X1 : $i]:
% 0.70/0.86         (((k4_xboole_0 @ X1 @ (k1_tarski @ X0)) = (X1))
% 0.70/0.86          | (r2_hidden @ X0 @ X1))),
% 0.70/0.86      inference('sup+', [status(thm)], ['56', '65'])).
% 0.70/0.86  thf('67', plain,
% 0.70/0.86      ((((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) != (sk_A)))
% 0.70/0.86         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.70/0.86      inference('split', [status(esa)], ['0'])).
% 0.70/0.86  thf('68', plain,
% 0.70/0.86      (((((sk_A) != (sk_A)) | (r2_hidden @ sk_B @ sk_A)))
% 0.70/0.86         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.70/0.86      inference('sup-', [status(thm)], ['66', '67'])).
% 0.70/0.86  thf('69', plain,
% 0.70/0.86      (((r2_hidden @ sk_B @ sk_A))
% 0.70/0.86         <= (~ (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A))))),
% 0.70/0.86      inference('simplify', [status(thm)], ['68'])).
% 0.70/0.86  thf('70', plain,
% 0.70/0.86      ((~ (r2_hidden @ sk_B @ sk_A)) <= (~ ((r2_hidden @ sk_B @ sk_A)))),
% 0.70/0.86      inference('split', [status(esa)], ['37'])).
% 0.70/0.86  thf('71', plain,
% 0.70/0.86      (((r2_hidden @ sk_B @ sk_A)) | 
% 0.70/0.86       (((k4_xboole_0 @ sk_A @ (k1_tarski @ sk_B)) = (sk_A)))),
% 0.70/0.86      inference('sup-', [status(thm)], ['69', '70'])).
% 0.70/0.86  thf('72', plain, ($false),
% 0.70/0.86      inference('sat_resolution*', [status(thm)], ['1', '48', '49', '71'])).
% 0.70/0.86  
% 0.70/0.86  % SZS output end Refutation
% 0.70/0.86  
% 0.70/0.87  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
