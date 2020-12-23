%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UOwp3sDOak

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:23 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 157 expanded)
%              Number of leaves         :   36 (  64 expanded)
%              Depth                    :   17
%              Number of atoms          :  662 (1134 expanded)
%              Number of equality atoms :   72 ( 133 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf('0',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 )
      | ( X17 = X18 )
      | ( X17 = X19 )
      | ( X17 = X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
        & ( A != B )
        & ( A != C ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) )
          & ( A != B )
          & ( A != C ) ) ),
    inference('cnf.neg',[status(esa)],[t25_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_xboole_0 @ X8 @ X9 )
        = X8 )
      | ~ ( r1_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('6',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ X11 @ ( k4_xboole_0 @ X11 @ X12 ) )
      = ( k3_xboole_0 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','12'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('17',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('19',plain,(
    ! [X13: $i] :
      ( r1_xboole_0 @ X13 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['13','22'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k2_xboole_0 @ X14 @ X15 )
      = ( k5_xboole_0 @ X14 @ ( k4_xboole_0 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('25',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('27',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k4_xboole_0 @ X6 @ X7 )
      = ( k5_xboole_0 @ X6 @ ( k3_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X10: $i] :
      ( ( k4_xboole_0 @ X10 @ k1_xboole_0 )
      = X10 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['25','30'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('32',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42 )
      = ( k2_enumset1 @ X39 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('33',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0 )
      = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( k2_enumset1 @ X36 @ X36 @ X37 @ X38 )
      = ( k1_enumset1 @ X36 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t50_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k3_enumset1 @ A @ B @ C @ D @ E )
      = ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ) )).

thf('36',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( k3_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X28 @ X29 @ X30 @ X31 ) @ ( k1_tarski @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t50_enumset1])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X3 ) ) ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X2 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['34','37'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( k1_enumset1 @ sk_B_1 @ sk_C_1 @ sk_A )
    = ( k2_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['31','40'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 )
      | ( r2_hidden @ X21 @ X25 )
      | ( X25
       != ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('43',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X21 @ ( k1_enumset1 @ X24 @ X23 @ X22 ) )
      | ( zip_tseitin_0 @ X21 @ X22 @ X23 @ X24 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) )
      | ( zip_tseitin_0 @ X0 @ sk_A @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( X17 != X18 )
      | ~ ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X16: $i,X18: $i,X19: $i] :
      ~ ( zip_tseitin_0 @ X18 @ X18 @ X19 @ X16 ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    r2_hidden @ sk_A @ ( k2_tarski @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X34: $i,X35: $i] :
      ( ( k1_enumset1 @ X34 @ X34 @ X35 )
      = ( k2_tarski @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('49',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X26 @ X25 )
      | ~ ( zip_tseitin_0 @ X26 @ X22 @ X23 @ X24 )
      | ( X25
       != ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('50',plain,(
    ! [X22: $i,X23: $i,X24: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X22 @ X23 @ X24 )
      | ~ ( r2_hidden @ X26 @ ( k1_enumset1 @ X24 @ X23 @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','50'])).

thf('52',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_C_1 @ sk_B_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['47','51'])).

thf('53',plain,
    ( ( sk_A = sk_B_1 )
    | ( sk_A = sk_B_1 )
    | ( sk_A = sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','52'])).

thf('54',plain,
    ( ( sk_A = sk_C_1 )
    | ( sk_A = sk_B_1 ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    sk_A != sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('56',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('57',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UOwp3sDOak
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:03:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.68  % Solved by: fo/fo7.sh
% 0.44/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.68  % done 497 iterations in 0.231s
% 0.44/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.68  % SZS output start Refutation
% 0.44/0.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.68  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.44/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.44/0.68  thf(sk_B_type, type, sk_B: $i > $i).
% 0.44/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.44/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.68  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.44/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.68  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.44/0.68  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.44/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.68  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.44/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.68  thf(d1_enumset1, axiom,
% 0.44/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.68     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.44/0.68       ( ![E:$i]:
% 0.44/0.68         ( ( r2_hidden @ E @ D ) <=>
% 0.44/0.68           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.44/0.68  thf(zf_stmt_0, axiom,
% 0.44/0.68    (![E:$i,C:$i,B:$i,A:$i]:
% 0.44/0.68     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.44/0.68       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.44/0.68  thf('0', plain,
% 0.44/0.68      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.44/0.68         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 0.44/0.68          | ((X17) = (X18))
% 0.44/0.68          | ((X17) = (X19))
% 0.44/0.68          | ((X17) = (X20)))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.68  thf(t25_zfmisc_1, conjecture,
% 0.44/0.68    (![A:$i,B:$i,C:$i]:
% 0.44/0.68     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.44/0.68          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.44/0.68  thf(zf_stmt_1, negated_conjecture,
% 0.44/0.68    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.68        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.44/0.68             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.44/0.68    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.44/0.68  thf('1', plain,
% 0.44/0.68      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C_1))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.68  thf(t28_xboole_1, axiom,
% 0.44/0.68    (![A:$i,B:$i]:
% 0.44/0.68     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.44/0.68  thf('2', plain,
% 0.44/0.68      (![X8 : $i, X9 : $i]:
% 0.44/0.68         (((k3_xboole_0 @ X8 @ X9) = (X8)) | ~ (r1_tarski @ X8 @ X9))),
% 0.44/0.68      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.44/0.68  thf('3', plain,
% 0.44/0.68      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.44/0.68         = (k1_tarski @ sk_A))),
% 0.44/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.68  thf(t100_xboole_1, axiom,
% 0.44/0.68    (![A:$i,B:$i]:
% 0.44/0.68     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.44/0.68  thf('4', plain,
% 0.44/0.68      (![X6 : $i, X7 : $i]:
% 0.44/0.68         ((k4_xboole_0 @ X6 @ X7)
% 0.44/0.68           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.44/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.68  thf('5', plain,
% 0.44/0.68      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.44/0.68         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.44/0.68      inference('sup+', [status(thm)], ['3', '4'])).
% 0.44/0.68  thf(t3_boole, axiom,
% 0.44/0.68    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.44/0.68  thf('6', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.44/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.68  thf(t48_xboole_1, axiom,
% 0.44/0.68    (![A:$i,B:$i]:
% 0.44/0.68     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.44/0.68  thf('7', plain,
% 0.44/0.68      (![X11 : $i, X12 : $i]:
% 0.44/0.68         ((k4_xboole_0 @ X11 @ (k4_xboole_0 @ X11 @ X12))
% 0.44/0.68           = (k3_xboole_0 @ X11 @ X12))),
% 0.44/0.68      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.44/0.68  thf('8', plain,
% 0.44/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.44/0.68  thf(idempotence_k3_xboole_0, axiom,
% 0.44/0.68    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.44/0.68  thf('9', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.44/0.68      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.44/0.68  thf('10', plain,
% 0.44/0.68      (![X6 : $i, X7 : $i]:
% 0.44/0.68         ((k4_xboole_0 @ X6 @ X7)
% 0.44/0.68           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.44/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.68  thf('11', plain,
% 0.44/0.68      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.68      inference('sup+', [status(thm)], ['9', '10'])).
% 0.44/0.68  thf('12', plain,
% 0.44/0.68      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.68      inference('demod', [status(thm)], ['8', '11'])).
% 0.44/0.68  thf('13', plain,
% 0.44/0.68      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.44/0.68         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.44/0.68      inference('demod', [status(thm)], ['5', '12'])).
% 0.44/0.68  thf(t7_xboole_0, axiom,
% 0.44/0.68    (![A:$i]:
% 0.44/0.68     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.44/0.68          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.44/0.68  thf('14', plain,
% 0.44/0.68      (![X5 : $i]: (((X5) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X5) @ X5))),
% 0.44/0.68      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.44/0.68  thf('15', plain,
% 0.44/0.68      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.68      inference('demod', [status(thm)], ['8', '11'])).
% 0.44/0.68  thf('16', plain,
% 0.44/0.68      (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.68      inference('demod', [status(thm)], ['8', '11'])).
% 0.44/0.68  thf(t4_xboole_0, axiom,
% 0.44/0.68    (![A:$i,B:$i]:
% 0.44/0.68     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.44/0.68            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.44/0.68       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.44/0.68            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.44/0.68  thf('17', plain,
% 0.44/0.68      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.44/0.68         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.44/0.68          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.44/0.68      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.44/0.68  thf('18', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         (~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))
% 0.44/0.68          | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.44/0.68  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.44/0.68  thf('19', plain, (![X13 : $i]: (r1_xboole_0 @ X13 @ k1_xboole_0)),
% 0.44/0.68      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.44/0.68  thf('20', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k5_xboole_0 @ X0 @ X0))),
% 0.44/0.68      inference('demod', [status(thm)], ['18', '19'])).
% 0.44/0.68  thf('21', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i]:
% 0.44/0.68         ~ (r2_hidden @ X1 @ (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.68      inference('sup-', [status(thm)], ['15', '20'])).
% 0.44/0.68  thf('22', plain,
% 0.44/0.68      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.68      inference('sup-', [status(thm)], ['14', '21'])).
% 0.44/0.68  thf('23', plain,
% 0.44/0.68      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.44/0.68         = (k1_xboole_0))),
% 0.44/0.68      inference('demod', [status(thm)], ['13', '22'])).
% 0.44/0.68  thf(t98_xboole_1, axiom,
% 0.44/0.68    (![A:$i,B:$i]:
% 0.44/0.68     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.44/0.68  thf('24', plain,
% 0.44/0.68      (![X14 : $i, X15 : $i]:
% 0.44/0.68         ((k2_xboole_0 @ X14 @ X15)
% 0.44/0.68           = (k5_xboole_0 @ X14 @ (k4_xboole_0 @ X15 @ X14)))),
% 0.44/0.68      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.44/0.68  thf('25', plain,
% 0.44/0.68      (((k2_xboole_0 @ (k2_tarski @ sk_B_1 @ sk_C_1) @ (k1_tarski @ sk_A))
% 0.44/0.68         = (k5_xboole_0 @ (k2_tarski @ sk_B_1 @ sk_C_1) @ k1_xboole_0))),
% 0.44/0.68      inference('sup+', [status(thm)], ['23', '24'])).
% 0.44/0.68  thf('26', plain,
% 0.44/0.68      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.44/0.68      inference('sup-', [status(thm)], ['14', '21'])).
% 0.44/0.68  thf('27', plain,
% 0.44/0.68      (![X6 : $i, X7 : $i]:
% 0.44/0.68         ((k4_xboole_0 @ X6 @ X7)
% 0.44/0.68           = (k5_xboole_0 @ X6 @ (k3_xboole_0 @ X6 @ X7)))),
% 0.44/0.68      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.44/0.68  thf('28', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.44/0.68      inference('sup+', [status(thm)], ['26', '27'])).
% 0.44/0.68  thf('29', plain, (![X10 : $i]: ((k4_xboole_0 @ X10 @ k1_xboole_0) = (X10))),
% 0.44/0.68      inference('cnf', [status(esa)], [t3_boole])).
% 0.44/0.68  thf('30', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.44/0.68      inference('sup+', [status(thm)], ['28', '29'])).
% 0.44/0.68  thf('31', plain,
% 0.44/0.68      (((k2_xboole_0 @ (k2_tarski @ sk_B_1 @ sk_C_1) @ (k1_tarski @ sk_A))
% 0.44/0.68         = (k2_tarski @ sk_B_1 @ sk_C_1))),
% 0.44/0.68      inference('demod', [status(thm)], ['25', '30'])).
% 0.44/0.68  thf(t72_enumset1, axiom,
% 0.44/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.68     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.44/0.68  thf('32', plain,
% 0.44/0.68      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.44/0.68         ((k3_enumset1 @ X39 @ X39 @ X40 @ X41 @ X42)
% 0.44/0.68           = (k2_enumset1 @ X39 @ X40 @ X41 @ X42))),
% 0.44/0.68      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.44/0.68  thf(t71_enumset1, axiom,
% 0.44/0.68    (![A:$i,B:$i,C:$i]:
% 0.44/0.68     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.44/0.68  thf('33', plain,
% 0.44/0.68      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 0.44/0.68           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 0.44/0.68      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.44/0.68  thf('34', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.68         ((k3_enumset1 @ X2 @ X2 @ X2 @ X1 @ X0) = (k1_enumset1 @ X2 @ X1 @ X0))),
% 0.44/0.68      inference('sup+', [status(thm)], ['32', '33'])).
% 0.44/0.68  thf('35', plain,
% 0.44/0.68      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.44/0.68         ((k2_enumset1 @ X36 @ X36 @ X37 @ X38)
% 0.44/0.68           = (k1_enumset1 @ X36 @ X37 @ X38))),
% 0.44/0.68      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.44/0.68  thf(t50_enumset1, axiom,
% 0.44/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.44/0.68     ( ( k3_enumset1 @ A @ B @ C @ D @ E ) =
% 0.44/0.68       ( k2_xboole_0 @ ( k2_enumset1 @ A @ B @ C @ D ) @ ( k1_tarski @ E ) ) ))).
% 0.44/0.68  thf('36', plain,
% 0.44/0.68      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.44/0.68         ((k3_enumset1 @ X28 @ X29 @ X30 @ X31 @ X32)
% 0.44/0.68           = (k2_xboole_0 @ (k2_enumset1 @ X28 @ X29 @ X30 @ X31) @ 
% 0.44/0.68              (k1_tarski @ X32)))),
% 0.44/0.68      inference('cnf', [status(esa)], [t50_enumset1])).
% 0.44/0.68  thf('37', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.68         ((k3_enumset1 @ X2 @ X2 @ X1 @ X0 @ X3)
% 0.44/0.68           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X1 @ X0) @ (k1_tarski @ X3)))),
% 0.44/0.68      inference('sup+', [status(thm)], ['35', '36'])).
% 0.44/0.68  thf('38', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.68         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.44/0.68           = (k2_xboole_0 @ (k1_enumset1 @ X2 @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.44/0.68      inference('sup+', [status(thm)], ['34', '37'])).
% 0.44/0.68  thf(t70_enumset1, axiom,
% 0.44/0.68    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.44/0.68  thf('39', plain,
% 0.44/0.68      (![X34 : $i, X35 : $i]:
% 0.44/0.68         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.44/0.68      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.44/0.68  thf('40', plain,
% 0.44/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.68         ((k1_enumset1 @ X2 @ X1 @ X0)
% 0.44/0.68           = (k2_xboole_0 @ (k2_tarski @ X2 @ X1) @ (k1_tarski @ X0)))),
% 0.44/0.68      inference('demod', [status(thm)], ['38', '39'])).
% 0.44/0.68  thf('41', plain,
% 0.44/0.68      (((k1_enumset1 @ sk_B_1 @ sk_C_1 @ sk_A) = (k2_tarski @ sk_B_1 @ sk_C_1))),
% 0.44/0.68      inference('demod', [status(thm)], ['31', '40'])).
% 0.44/0.68  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.44/0.68  thf(zf_stmt_3, axiom,
% 0.44/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.68     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.44/0.68       ( ![E:$i]:
% 0.44/0.68         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.44/0.68  thf('42', plain,
% 0.44/0.68      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.44/0.68         ((zip_tseitin_0 @ X21 @ X22 @ X23 @ X24)
% 0.44/0.68          | (r2_hidden @ X21 @ X25)
% 0.44/0.68          | ((X25) != (k1_enumset1 @ X24 @ X23 @ X22)))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.68  thf('43', plain,
% 0.44/0.68      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.44/0.68         ((r2_hidden @ X21 @ (k1_enumset1 @ X24 @ X23 @ X22))
% 0.44/0.68          | (zip_tseitin_0 @ X21 @ X22 @ X23 @ X24))),
% 0.44/0.68      inference('simplify', [status(thm)], ['42'])).
% 0.44/0.68  thf('44', plain,
% 0.44/0.68      (![X0 : $i]:
% 0.44/0.68         ((r2_hidden @ X0 @ (k2_tarski @ sk_B_1 @ sk_C_1))
% 0.44/0.68          | (zip_tseitin_0 @ X0 @ sk_A @ sk_C_1 @ sk_B_1))),
% 0.44/0.68      inference('sup+', [status(thm)], ['41', '43'])).
% 0.44/0.68  thf('45', plain,
% 0.44/0.68      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.44/0.68         (((X17) != (X18)) | ~ (zip_tseitin_0 @ X17 @ X18 @ X19 @ X16))),
% 0.44/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.69  thf('46', plain,
% 0.44/0.69      (![X16 : $i, X18 : $i, X19 : $i]:
% 0.44/0.69         ~ (zip_tseitin_0 @ X18 @ X18 @ X19 @ X16)),
% 0.44/0.69      inference('simplify', [status(thm)], ['45'])).
% 0.44/0.69  thf('47', plain, ((r2_hidden @ sk_A @ (k2_tarski @ sk_B_1 @ sk_C_1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['44', '46'])).
% 0.44/0.69  thf('48', plain,
% 0.44/0.69      (![X34 : $i, X35 : $i]:
% 0.44/0.69         ((k1_enumset1 @ X34 @ X34 @ X35) = (k2_tarski @ X34 @ X35))),
% 0.44/0.69      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.44/0.69  thf('49', plain,
% 0.44/0.69      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.44/0.69         (~ (r2_hidden @ X26 @ X25)
% 0.44/0.69          | ~ (zip_tseitin_0 @ X26 @ X22 @ X23 @ X24)
% 0.44/0.69          | ((X25) != (k1_enumset1 @ X24 @ X23 @ X22)))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.69  thf('50', plain,
% 0.44/0.69      (![X22 : $i, X23 : $i, X24 : $i, X26 : $i]:
% 0.44/0.69         (~ (zip_tseitin_0 @ X26 @ X22 @ X23 @ X24)
% 0.44/0.69          | ~ (r2_hidden @ X26 @ (k1_enumset1 @ X24 @ X23 @ X22)))),
% 0.44/0.69      inference('simplify', [status(thm)], ['49'])).
% 0.44/0.69  thf('51', plain,
% 0.44/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.69         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.44/0.69          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.44/0.69      inference('sup-', [status(thm)], ['48', '50'])).
% 0.44/0.69  thf('52', plain, (~ (zip_tseitin_0 @ sk_A @ sk_C_1 @ sk_B_1 @ sk_B_1)),
% 0.44/0.69      inference('sup-', [status(thm)], ['47', '51'])).
% 0.44/0.69  thf('53', plain,
% 0.44/0.69      ((((sk_A) = (sk_B_1)) | ((sk_A) = (sk_B_1)) | ((sk_A) = (sk_C_1)))),
% 0.44/0.69      inference('sup-', [status(thm)], ['0', '52'])).
% 0.44/0.69  thf('54', plain, ((((sk_A) = (sk_C_1)) | ((sk_A) = (sk_B_1)))),
% 0.44/0.69      inference('simplify', [status(thm)], ['53'])).
% 0.44/0.69  thf('55', plain, (((sk_A) != (sk_B_1))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.69  thf('56', plain, (((sk_A) != (sk_C_1))),
% 0.44/0.69      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.69  thf('57', plain, ($false),
% 0.44/0.69      inference('simplify_reflect-', [status(thm)], ['54', '55', '56'])).
% 0.44/0.69  
% 0.44/0.69  % SZS output end Refutation
% 0.44/0.69  
% 0.44/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
