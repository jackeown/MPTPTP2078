%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8o8L6OQkNF

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:47 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 122 expanded)
%              Number of leaves         :   37 (  52 expanded)
%              Depth                    :   15
%              Number of atoms          :  636 ( 841 expanded)
%              Number of equality atoms :   76 ( 103 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X57: $i,X58: $i] :
      ( r1_tarski @ ( k1_tarski @ X57 ) @ ( k2_tarski @ X57 @ X58 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(t28_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
        & ( A != C )
        & ( A != D ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ~ ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) )
          & ( A != C )
          & ( A != D ) ) ),
    inference('cnf.neg',[status(esa)],[t28_zfmisc_1])).

thf('1',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k2_tarski @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ ( k3_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B_1 ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('13',plain,(
    ! [X16: $i] :
      ( r1_tarski @ k1_xboole_0 @ X16 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X17 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X19: $i] :
      ( ( X19 = k1_xboole_0 )
      | ~ ( r1_tarski @ X19 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','26'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k4_xboole_0 @ X20 @ ( k4_xboole_0 @ X20 @ X21 ) )
      = ( k3_xboole_0 @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('30',plain,(
    ! [X2: $i] :
      ( ( k3_xboole_0 @ X2 @ X2 )
      = X2 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('31',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k4_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','32','33'])).

thf('35',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['12','34'])).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_xboole_0 @ X23 @ X24 )
      = ( k5_xboole_0 @ X23 @ ( k4_xboole_0 @ X24 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('37',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('39',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('40',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k1_enumset1 @ X48 @ X48 @ X49 )
      = ( k2_tarski @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('41',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ( k2_enumset1 @ X43 @ X44 @ X45 @ X46 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X43 @ X44 @ X45 ) @ ( k1_tarski @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('43',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( k2_enumset1 @ X50 @ X50 @ X51 @ X52 )
      = ( k1_enumset1 @ X50 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('44',plain,
    ( ( k1_enumset1 @ sk_C_1 @ sk_D_1 @ sk_A )
    = ( k2_tarski @ sk_C_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['39','42','43'])).

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
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_C_1 @ sk_D_1 ) )
      | ( zip_tseitin_0 @ X0 @ sk_A @ sk_D_1 @ sk_C_1 ) ) ),
    inference('sup+',[status(thm)],['44','46'])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('48',plain,(
    ! [X37: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X41 @ X39 )
      | ( X41 = X40 )
      | ( X41 = X37 )
      | ( X39
       != ( k2_tarski @ X40 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('49',plain,(
    ! [X37: $i,X40: $i,X41: $i] :
      ( ( X41 = X37 )
      | ( X41 = X40 )
      | ~ ( r2_hidden @ X41 @ ( k2_tarski @ X40 @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_A @ sk_D_1 @ sk_C_1 )
      | ( X0 = sk_C_1 )
      | ( X0 = sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( X26 != X27 )
      | ~ ( zip_tseitin_0 @ X26 @ X27 @ X28 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('52',plain,(
    ! [X25: $i,X27: $i,X28: $i] :
      ~ ( zip_tseitin_0 @ X27 @ X27 @ X28 @ X25 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( sk_A = sk_D_1 )
    | ( sk_A = sk_C_1 ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8o8L6OQkNF
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:25:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.71/0.90  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.71/0.90  % Solved by: fo/fo7.sh
% 0.71/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.90  % done 1634 iterations in 0.441s
% 0.71/0.90  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.71/0.90  % SZS output start Refutation
% 0.71/0.90  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.71/0.90  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.71/0.90  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.71/0.90  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.71/0.90  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.71/0.90  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.71/0.90  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.71/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.90  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.71/0.90  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.71/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.71/0.90  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.71/0.90  thf(t12_zfmisc_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.71/0.90  thf('0', plain,
% 0.71/0.90      (![X57 : $i, X58 : $i]:
% 0.71/0.90         (r1_tarski @ (k1_tarski @ X57) @ (k2_tarski @ X57 @ X58))),
% 0.71/0.90      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.71/0.90  thf(t28_zfmisc_1, conjecture,
% 0.71/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.90     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.71/0.90          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.71/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.90    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.90        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.71/0.90             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.71/0.90    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.71/0.90  thf('1', plain,
% 0.71/0.90      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_1) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf(t28_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.71/0.90  thf('2', plain,
% 0.71/0.90      (![X14 : $i, X15 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.71/0.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.71/0.90  thf('3', plain,
% 0.71/0.90      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B_1) @ 
% 0.71/0.90         (k2_tarski @ sk_C_1 @ sk_D_1)) = (k2_tarski @ sk_A @ sk_B_1))),
% 0.71/0.90      inference('sup-', [status(thm)], ['1', '2'])).
% 0.71/0.90  thf(commutativity_k3_xboole_0, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.71/0.90  thf('4', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.71/0.90  thf(t18_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.71/0.90  thf('5', plain,
% 0.71/0.90      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.71/0.90         ((r1_tarski @ X10 @ X11)
% 0.71/0.90          | ~ (r1_tarski @ X10 @ (k3_xboole_0 @ X11 @ X12)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.71/0.90  thf('6', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['4', '5'])).
% 0.71/0.90  thf('7', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B_1))
% 0.71/0.90          | (r1_tarski @ X0 @ (k2_tarski @ sk_C_1 @ sk_D_1)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['3', '6'])).
% 0.71/0.90  thf('8', plain,
% 0.71/0.90      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.71/0.90      inference('sup-', [status(thm)], ['0', '7'])).
% 0.71/0.90  thf('9', plain,
% 0.71/0.90      (![X14 : $i, X15 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.71/0.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.71/0.90  thf('10', plain,
% 0.71/0.90      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))
% 0.71/0.90         = (k1_tarski @ sk_A))),
% 0.71/0.90      inference('sup-', [status(thm)], ['8', '9'])).
% 0.71/0.90  thf(t100_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.71/0.90  thf('11', plain,
% 0.71/0.90      (![X8 : $i, X9 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X8 @ X9)
% 0.71/0.90           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.71/0.90  thf('12', plain,
% 0.71/0.90      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))
% 0.71/0.90         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['10', '11'])).
% 0.71/0.90  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.71/0.90  thf('13', plain, (![X16 : $i]: (r1_tarski @ k1_xboole_0 @ X16)),
% 0.71/0.90      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.71/0.90  thf('14', plain,
% 0.71/0.90      (![X14 : $i, X15 : $i]:
% 0.71/0.90         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.71/0.90      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.71/0.90  thf('15', plain,
% 0.71/0.90      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['13', '14'])).
% 0.71/0.90  thf('16', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.71/0.90      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.71/0.90  thf('17', plain,
% 0.71/0.90      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['15', '16'])).
% 0.71/0.90  thf('18', plain,
% 0.71/0.90      (![X8 : $i, X9 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X8 @ X9)
% 0.71/0.90           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.71/0.90  thf('19', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['17', '18'])).
% 0.71/0.90  thf(t36_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.71/0.90  thf('20', plain,
% 0.71/0.90      (![X17 : $i, X18 : $i]: (r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X17)),
% 0.71/0.90      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.71/0.90  thf(t3_xboole_1, axiom,
% 0.71/0.90    (![A:$i]:
% 0.71/0.90     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.71/0.90  thf('21', plain,
% 0.71/0.90      (![X19 : $i]:
% 0.71/0.90         (((X19) = (k1_xboole_0)) | ~ (r1_tarski @ X19 @ k1_xboole_0))),
% 0.71/0.90      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.71/0.90  thf('22', plain,
% 0.71/0.90      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.71/0.90      inference('sup-', [status(thm)], ['20', '21'])).
% 0.71/0.90  thf(t98_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.71/0.90  thf('23', plain,
% 0.71/0.90      (![X23 : $i, X24 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ X23 @ X24)
% 0.71/0.90           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.71/0.90  thf('24', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['22', '23'])).
% 0.71/0.90  thf(t1_boole, axiom,
% 0.71/0.90    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.71/0.90  thf('25', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.71/0.90      inference('cnf', [status(esa)], [t1_boole])).
% 0.71/0.90  thf('26', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['24', '25'])).
% 0.71/0.90  thf('27', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.71/0.90      inference('demod', [status(thm)], ['19', '26'])).
% 0.71/0.90  thf(t48_xboole_1, axiom,
% 0.71/0.90    (![A:$i,B:$i]:
% 0.71/0.90     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.71/0.90  thf('28', plain,
% 0.71/0.90      (![X20 : $i, X21 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X20 @ (k4_xboole_0 @ X20 @ X21))
% 0.71/0.90           = (k3_xboole_0 @ X20 @ X21))),
% 0.71/0.90      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.71/0.90  thf('29', plain,
% 0.71/0.90      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['27', '28'])).
% 0.71/0.90  thf(idempotence_k3_xboole_0, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.71/0.90  thf('30', plain, (![X2 : $i]: ((k3_xboole_0 @ X2 @ X2) = (X2))),
% 0.71/0.90      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.71/0.90  thf('31', plain,
% 0.71/0.90      (![X8 : $i, X9 : $i]:
% 0.71/0.90         ((k4_xboole_0 @ X8 @ X9)
% 0.71/0.90           = (k5_xboole_0 @ X8 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.71/0.90  thf('32', plain,
% 0.71/0.90      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['30', '31'])).
% 0.71/0.90  thf('33', plain,
% 0.71/0.90      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['15', '16'])).
% 0.71/0.90  thf('34', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['29', '32', '33'])).
% 0.71/0.90  thf('35', plain,
% 0.71/0.90      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C_1 @ sk_D_1))
% 0.71/0.90         = (k1_xboole_0))),
% 0.71/0.90      inference('demod', [status(thm)], ['12', '34'])).
% 0.71/0.90  thf('36', plain,
% 0.71/0.90      (![X23 : $i, X24 : $i]:
% 0.71/0.90         ((k2_xboole_0 @ X23 @ X24)
% 0.71/0.90           = (k5_xboole_0 @ X23 @ (k4_xboole_0 @ X24 @ X23)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.71/0.90  thf('37', plain,
% 0.71/0.90      (((k2_xboole_0 @ (k2_tarski @ sk_C_1 @ sk_D_1) @ (k1_tarski @ sk_A))
% 0.71/0.90         = (k5_xboole_0 @ (k2_tarski @ sk_C_1 @ sk_D_1) @ k1_xboole_0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['35', '36'])).
% 0.71/0.90  thf('38', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.71/0.90      inference('sup+', [status(thm)], ['24', '25'])).
% 0.71/0.90  thf('39', plain,
% 0.71/0.90      (((k2_xboole_0 @ (k2_tarski @ sk_C_1 @ sk_D_1) @ (k1_tarski @ sk_A))
% 0.71/0.90         = (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.71/0.90      inference('demod', [status(thm)], ['37', '38'])).
% 0.71/0.90  thf(t70_enumset1, axiom,
% 0.71/0.90    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.71/0.90  thf('40', plain,
% 0.71/0.90      (![X48 : $i, X49 : $i]:
% 0.71/0.90         ((k1_enumset1 @ X48 @ X48 @ X49) = (k2_tarski @ X48 @ X49))),
% 0.71/0.90      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.71/0.90  thf(t46_enumset1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.90     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.71/0.90       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.71/0.90  thf('41', plain,
% 0.71/0.90      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.71/0.90         ((k2_enumset1 @ X43 @ X44 @ X45 @ X46)
% 0.71/0.90           = (k2_xboole_0 @ (k1_enumset1 @ X43 @ X44 @ X45) @ (k1_tarski @ X46)))),
% 0.71/0.90      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.71/0.90  thf('42', plain,
% 0.71/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.90         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.71/0.90           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.71/0.90      inference('sup+', [status(thm)], ['40', '41'])).
% 0.71/0.90  thf(t71_enumset1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.71/0.90  thf('43', plain,
% 0.71/0.90      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.71/0.90         ((k2_enumset1 @ X50 @ X50 @ X51 @ X52)
% 0.71/0.90           = (k1_enumset1 @ X50 @ X51 @ X52))),
% 0.71/0.90      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.71/0.90  thf('44', plain,
% 0.71/0.90      (((k1_enumset1 @ sk_C_1 @ sk_D_1 @ sk_A) = (k2_tarski @ sk_C_1 @ sk_D_1))),
% 0.71/0.90      inference('demod', [status(thm)], ['39', '42', '43'])).
% 0.71/0.90  thf(d1_enumset1, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.90     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.71/0.90       ( ![E:$i]:
% 0.71/0.90         ( ( r2_hidden @ E @ D ) <=>
% 0.71/0.90           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.71/0.90  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.71/0.90  thf(zf_stmt_2, axiom,
% 0.71/0.90    (![E:$i,C:$i,B:$i,A:$i]:
% 0.71/0.90     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.71/0.90       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.71/0.90  thf(zf_stmt_3, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.90     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.71/0.90       ( ![E:$i]:
% 0.71/0.90         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.71/0.90  thf('45', plain,
% 0.71/0.90      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.71/0.90         ((zip_tseitin_0 @ X30 @ X31 @ X32 @ X33)
% 0.71/0.90          | (r2_hidden @ X30 @ X34)
% 0.71/0.90          | ((X34) != (k1_enumset1 @ X33 @ X32 @ X31)))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.71/0.90  thf('46', plain,
% 0.71/0.90      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.71/0.90         ((r2_hidden @ X30 @ (k1_enumset1 @ X33 @ X32 @ X31))
% 0.71/0.90          | (zip_tseitin_0 @ X30 @ X31 @ X32 @ X33))),
% 0.71/0.90      inference('simplify', [status(thm)], ['45'])).
% 0.71/0.90  thf('47', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((r2_hidden @ X0 @ (k2_tarski @ sk_C_1 @ sk_D_1))
% 0.71/0.90          | (zip_tseitin_0 @ X0 @ sk_A @ sk_D_1 @ sk_C_1))),
% 0.71/0.90      inference('sup+', [status(thm)], ['44', '46'])).
% 0.71/0.90  thf(d2_tarski, axiom,
% 0.71/0.90    (![A:$i,B:$i,C:$i]:
% 0.71/0.90     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.71/0.90       ( ![D:$i]:
% 0.71/0.90         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.71/0.90  thf('48', plain,
% 0.71/0.90      (![X37 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.71/0.90         (~ (r2_hidden @ X41 @ X39)
% 0.71/0.90          | ((X41) = (X40))
% 0.71/0.90          | ((X41) = (X37))
% 0.71/0.90          | ((X39) != (k2_tarski @ X40 @ X37)))),
% 0.71/0.90      inference('cnf', [status(esa)], [d2_tarski])).
% 0.71/0.90  thf('49', plain,
% 0.71/0.90      (![X37 : $i, X40 : $i, X41 : $i]:
% 0.71/0.90         (((X41) = (X37))
% 0.71/0.90          | ((X41) = (X40))
% 0.71/0.90          | ~ (r2_hidden @ X41 @ (k2_tarski @ X40 @ X37)))),
% 0.71/0.90      inference('simplify', [status(thm)], ['48'])).
% 0.71/0.90  thf('50', plain,
% 0.71/0.90      (![X0 : $i]:
% 0.71/0.90         ((zip_tseitin_0 @ X0 @ sk_A @ sk_D_1 @ sk_C_1)
% 0.71/0.90          | ((X0) = (sk_C_1))
% 0.71/0.90          | ((X0) = (sk_D_1)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['47', '49'])).
% 0.71/0.90  thf('51', plain,
% 0.71/0.90      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.71/0.90         (((X26) != (X27)) | ~ (zip_tseitin_0 @ X26 @ X27 @ X28 @ X25))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.71/0.90  thf('52', plain,
% 0.71/0.90      (![X25 : $i, X27 : $i, X28 : $i]:
% 0.71/0.90         ~ (zip_tseitin_0 @ X27 @ X27 @ X28 @ X25)),
% 0.71/0.90      inference('simplify', [status(thm)], ['51'])).
% 0.71/0.90  thf('53', plain, ((((sk_A) = (sk_D_1)) | ((sk_A) = (sk_C_1)))),
% 0.71/0.90      inference('sup-', [status(thm)], ['50', '52'])).
% 0.71/0.90  thf('54', plain, (((sk_A) != (sk_C_1))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('55', plain, (((sk_A) != (sk_D_1))),
% 0.71/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.90  thf('56', plain, ($false),
% 0.71/0.90      inference('simplify_reflect-', [status(thm)], ['53', '54', '55'])).
% 0.71/0.90  
% 0.71/0.90  % SZS output end Refutation
% 0.71/0.90  
% 0.71/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
