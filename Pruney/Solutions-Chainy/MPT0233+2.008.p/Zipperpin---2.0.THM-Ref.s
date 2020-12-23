%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yocz1UUW3W

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:38 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 111 expanded)
%              Number of leaves         :   37 (  49 expanded)
%              Depth                    :   15
%              Number of atoms          :  651 ( 787 expanded)
%              Number of equality atoms :   78 (  96 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('0',plain,(
    ! [X68: $i,X69: $i] :
      ( r1_tarski @ ( k1_tarski @ X68 ) @ ( k2_tarski @ X68 @ X69 ) ) ),
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
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( r1_tarski @ X7 @ ( k3_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_tarski @ sk_A @ sk_B ) )
      | ( r1_tarski @ X0 @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('10',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('13',plain,(
    ! [X12: $i] :
      ( r1_tarski @ k1_xboole_0 @ X12 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('14',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k5_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['15','18'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('20',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['19','20'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k4_xboole_0 @ X13 @ ( k4_xboole_0 @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('24',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('25',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('28',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k3_xboole_0 @ X3 @ X2 )
      = ( k3_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','26','29'])).

thf('31',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['12','30'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ X17 )
      = ( k5_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('33',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_C @ sk_D_1 ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_C @ sk_D_1 ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['31','32'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    ! [X15: $i] :
      ( ( k5_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('36',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_C @ sk_D_1 ) )
    = ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('37',plain,(
    ! [X44: $i] :
      ( ( k2_tarski @ X44 @ X44 )
      = ( k1_tarski @ X44 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('38',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_xboole_0 @ ( k2_tarski @ X36 @ X37 ) @ ( k2_tarski @ X38 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('40',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( k2_enumset1 @ X47 @ X47 @ X48 @ X49 )
      = ( k1_enumset1 @ X47 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t98_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k1_enumset1 @ A @ B @ C )
      = ( k1_enumset1 @ A @ C @ B ) ) )).

thf('41',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( k1_enumset1 @ X65 @ X67 @ X66 )
      = ( k1_enumset1 @ X65 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_enumset1 @ X2 @ X0 @ X1 )
      = ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( k1_enumset1 @ X65 @ X67 @ X66 )
      = ( k1_enumset1 @ X65 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t98_enumset1])).

thf('44',plain,
    ( ( k1_enumset1 @ sk_A @ sk_C @ sk_D_1 )
    = ( k2_tarski @ sk_C @ sk_D_1 ) ),
    inference(demod,[status(thm)],['36','39','42','43'])).

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
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 )
      | ( r2_hidden @ X23 @ X27 )
      | ( X27
       != ( k1_enumset1 @ X26 @ X25 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('46',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X23 @ ( k1_enumset1 @ X26 @ X25 @ X24 ) )
      | ( zip_tseitin_0 @ X23 @ X24 @ X25 @ X26 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_C @ sk_D_1 ) )
      | ( zip_tseitin_0 @ X0 @ sk_D_1 @ sk_C @ sk_A ) ) ),
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
    ! [X30: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X34 @ X32 )
      | ( X34 = X33 )
      | ( X34 = X30 )
      | ( X32
       != ( k2_tarski @ X33 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('49',plain,(
    ! [X30: $i,X33: $i,X34: $i] :
      ( ( X34 = X30 )
      | ( X34 = X33 )
      | ~ ( r2_hidden @ X34 @ ( k2_tarski @ X33 @ X30 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_D_1 @ sk_C @ sk_A )
      | ( X0 = sk_C )
      | ( X0 = sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19 != X18 )
      | ~ ( zip_tseitin_0 @ X19 @ X20 @ X21 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('52',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ~ ( zip_tseitin_0 @ X18 @ X20 @ X21 @ X18 ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( sk_A = sk_D_1 )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_A != sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.yocz1UUW3W
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.69  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.48/0.69  % Solved by: fo/fo7.sh
% 0.48/0.69  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.69  % done 800 iterations in 0.242s
% 0.48/0.69  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.48/0.69  % SZS output start Refutation
% 0.48/0.69  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.48/0.69  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.48/0.69  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.48/0.69  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.48/0.69  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.48/0.69  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.48/0.69  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.69  thf(sk_C_type, type, sk_C: $i).
% 0.48/0.69  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.48/0.69  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.69  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.69  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.48/0.69  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.69  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.48/0.69  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.48/0.69  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.69  thf(t12_zfmisc_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.48/0.69  thf('0', plain,
% 0.48/0.69      (![X68 : $i, X69 : $i]:
% 0.48/0.69         (r1_tarski @ (k1_tarski @ X68) @ (k2_tarski @ X68 @ X69))),
% 0.48/0.69      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.48/0.69  thf(t28_zfmisc_1, conjecture,
% 0.48/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.69     ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.48/0.69          ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ))).
% 0.48/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.48/0.69    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.69        ( ~( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) & 
% 0.48/0.69             ( ( A ) != ( C ) ) & ( ( A ) != ( D ) ) ) ) )),
% 0.48/0.69    inference('cnf.neg', [status(esa)], [t28_zfmisc_1])).
% 0.48/0.69  thf('1', plain,
% 0.48/0.69      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf(t28_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.48/0.69  thf('2', plain,
% 0.48/0.69      (![X10 : $i, X11 : $i]:
% 0.48/0.69         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.48/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.48/0.69  thf('3', plain,
% 0.48/0.69      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1))
% 0.48/0.69         = (k2_tarski @ sk_A @ sk_B))),
% 0.48/0.69      inference('sup-', [status(thm)], ['1', '2'])).
% 0.48/0.69  thf(commutativity_k3_xboole_0, axiom,
% 0.48/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.48/0.69  thf('4', plain,
% 0.48/0.69      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.48/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.69  thf(t18_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i]:
% 0.48/0.69     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.48/0.69  thf('5', plain,
% 0.48/0.69      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.48/0.69         ((r1_tarski @ X7 @ X8) | ~ (r1_tarski @ X7 @ (k3_xboole_0 @ X8 @ X9)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.48/0.69  thf('6', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         (~ (r1_tarski @ X2 @ (k3_xboole_0 @ X1 @ X0)) | (r1_tarski @ X2 @ X0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['4', '5'])).
% 0.48/0.69  thf('7', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         (~ (r1_tarski @ X0 @ (k2_tarski @ sk_A @ sk_B))
% 0.48/0.69          | (r1_tarski @ X0 @ (k2_tarski @ sk_C @ sk_D_1)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['3', '6'])).
% 0.48/0.69  thf('8', plain,
% 0.48/0.69      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))),
% 0.48/0.69      inference('sup-', [status(thm)], ['0', '7'])).
% 0.48/0.69  thf('9', plain,
% 0.48/0.69      (![X10 : $i, X11 : $i]:
% 0.48/0.69         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.48/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.48/0.69  thf('10', plain,
% 0.48/0.69      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))
% 0.48/0.69         = (k1_tarski @ sk_A))),
% 0.48/0.69      inference('sup-', [status(thm)], ['8', '9'])).
% 0.48/0.69  thf(t100_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.48/0.69  thf('11', plain,
% 0.48/0.69      (![X5 : $i, X6 : $i]:
% 0.48/0.69         ((k4_xboole_0 @ X5 @ X6)
% 0.48/0.69           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.69  thf('12', plain,
% 0.48/0.69      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))
% 0.48/0.69         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.48/0.69      inference('sup+', [status(thm)], ['10', '11'])).
% 0.48/0.69  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.48/0.69  thf('13', plain, (![X12 : $i]: (r1_tarski @ k1_xboole_0 @ X12)),
% 0.48/0.69      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.48/0.69  thf('14', plain,
% 0.48/0.69      (![X10 : $i, X11 : $i]:
% 0.48/0.69         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 0.48/0.69      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.48/0.69  thf('15', plain,
% 0.48/0.69      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['13', '14'])).
% 0.48/0.69  thf('16', plain,
% 0.48/0.69      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.48/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.69  thf('17', plain,
% 0.48/0.69      (![X5 : $i, X6 : $i]:
% 0.48/0.69         ((k4_xboole_0 @ X5 @ X6)
% 0.48/0.69           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.69  thf('18', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]:
% 0.48/0.69         ((k4_xboole_0 @ X0 @ X1)
% 0.48/0.69           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 0.48/0.69      inference('sup+', [status(thm)], ['16', '17'])).
% 0.48/0.69  thf('19', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k5_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['15', '18'])).
% 0.48/0.69  thf(t5_boole, axiom,
% 0.48/0.69    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.48/0.69  thf('20', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.48/0.69      inference('cnf', [status(esa)], [t5_boole])).
% 0.48/0.69  thf('21', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.48/0.69      inference('demod', [status(thm)], ['19', '20'])).
% 0.48/0.69  thf(t48_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.48/0.69  thf('22', plain,
% 0.48/0.69      (![X13 : $i, X14 : $i]:
% 0.48/0.69         ((k4_xboole_0 @ X13 @ (k4_xboole_0 @ X13 @ X14))
% 0.48/0.69           = (k3_xboole_0 @ X13 @ X14))),
% 0.48/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.48/0.69  thf('23', plain,
% 0.48/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['21', '22'])).
% 0.48/0.69  thf(idempotence_k3_xboole_0, axiom,
% 0.48/0.69    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.48/0.69  thf('24', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 0.48/0.69      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.48/0.69  thf('25', plain,
% 0.48/0.69      (![X5 : $i, X6 : $i]:
% 0.48/0.69         ((k4_xboole_0 @ X5 @ X6)
% 0.48/0.69           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.48/0.69  thf('26', plain,
% 0.48/0.69      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['24', '25'])).
% 0.48/0.69  thf('27', plain,
% 0.48/0.69      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.48/0.69      inference('sup-', [status(thm)], ['13', '14'])).
% 0.48/0.69  thf('28', plain,
% 0.48/0.69      (![X2 : $i, X3 : $i]: ((k3_xboole_0 @ X3 @ X2) = (k3_xboole_0 @ X2 @ X3))),
% 0.48/0.69      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.48/0.69  thf('29', plain,
% 0.48/0.69      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['27', '28'])).
% 0.48/0.69  thf('30', plain, (![X0 : $i]: ((k5_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.48/0.69      inference('demod', [status(thm)], ['23', '26', '29'])).
% 0.48/0.69  thf('31', plain,
% 0.48/0.69      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))
% 0.48/0.69         = (k1_xboole_0))),
% 0.48/0.69      inference('demod', [status(thm)], ['12', '30'])).
% 0.48/0.69  thf(t98_xboole_1, axiom,
% 0.48/0.69    (![A:$i,B:$i]:
% 0.48/0.69     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.48/0.69  thf('32', plain,
% 0.48/0.69      (![X16 : $i, X17 : $i]:
% 0.48/0.69         ((k2_xboole_0 @ X16 @ X17)
% 0.48/0.69           = (k5_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16)))),
% 0.48/0.69      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.48/0.69  thf('33', plain,
% 0.48/0.69      (((k2_xboole_0 @ (k2_tarski @ sk_C @ sk_D_1) @ (k1_tarski @ sk_A))
% 0.48/0.69         = (k5_xboole_0 @ (k2_tarski @ sk_C @ sk_D_1) @ k1_xboole_0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['31', '32'])).
% 0.48/0.69  thf(commutativity_k2_xboole_0, axiom,
% 0.48/0.69    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.48/0.69  thf('34', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.48/0.69      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.48/0.69  thf('35', plain, (![X15 : $i]: ((k5_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.48/0.69      inference('cnf', [status(esa)], [t5_boole])).
% 0.48/0.69  thf('36', plain,
% 0.48/0.69      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_C @ sk_D_1))
% 0.48/0.69         = (k2_tarski @ sk_C @ sk_D_1))),
% 0.48/0.69      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.48/0.69  thf(t69_enumset1, axiom,
% 0.48/0.69    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.48/0.69  thf('37', plain,
% 0.48/0.69      (![X44 : $i]: ((k2_tarski @ X44 @ X44) = (k1_tarski @ X44))),
% 0.48/0.69      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.48/0.69  thf(l53_enumset1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.69     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.48/0.69       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.48/0.69  thf('38', plain,
% 0.48/0.69      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.48/0.69         ((k2_enumset1 @ X36 @ X37 @ X38 @ X39)
% 0.48/0.69           = (k2_xboole_0 @ (k2_tarski @ X36 @ X37) @ (k2_tarski @ X38 @ X39)))),
% 0.48/0.69      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.48/0.69  thf('39', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 0.48/0.69           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.48/0.69      inference('sup+', [status(thm)], ['37', '38'])).
% 0.48/0.69  thf(t71_enumset1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i]:
% 0.48/0.69     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.48/0.69  thf('40', plain,
% 0.48/0.69      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.48/0.69         ((k2_enumset1 @ X47 @ X47 @ X48 @ X49)
% 0.48/0.69           = (k1_enumset1 @ X47 @ X48 @ X49))),
% 0.48/0.69      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.48/0.69  thf(t98_enumset1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i]:
% 0.48/0.69     ( ( k1_enumset1 @ A @ B @ C ) = ( k1_enumset1 @ A @ C @ B ) ))).
% 0.48/0.69  thf('41', plain,
% 0.48/0.69      (![X65 : $i, X66 : $i, X67 : $i]:
% 0.48/0.69         ((k1_enumset1 @ X65 @ X67 @ X66) = (k1_enumset1 @ X65 @ X66 @ X67))),
% 0.48/0.69      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.48/0.69  thf('42', plain,
% 0.48/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.69         ((k1_enumset1 @ X2 @ X0 @ X1) = (k2_enumset1 @ X2 @ X2 @ X1 @ X0))),
% 0.48/0.69      inference('sup+', [status(thm)], ['40', '41'])).
% 0.48/0.69  thf('43', plain,
% 0.48/0.69      (![X65 : $i, X66 : $i, X67 : $i]:
% 0.48/0.69         ((k1_enumset1 @ X65 @ X67 @ X66) = (k1_enumset1 @ X65 @ X66 @ X67))),
% 0.48/0.69      inference('cnf', [status(esa)], [t98_enumset1])).
% 0.48/0.69  thf('44', plain,
% 0.48/0.69      (((k1_enumset1 @ sk_A @ sk_C @ sk_D_1) = (k2_tarski @ sk_C @ sk_D_1))),
% 0.48/0.69      inference('demod', [status(thm)], ['36', '39', '42', '43'])).
% 0.48/0.69  thf(d1_enumset1, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.69     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.48/0.69       ( ![E:$i]:
% 0.48/0.69         ( ( r2_hidden @ E @ D ) <=>
% 0.48/0.69           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.48/0.69  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.48/0.69  thf(zf_stmt_2, axiom,
% 0.48/0.69    (![E:$i,C:$i,B:$i,A:$i]:
% 0.48/0.69     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.48/0.69       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.48/0.69  thf(zf_stmt_3, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.69     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.48/0.69       ( ![E:$i]:
% 0.48/0.69         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.48/0.69  thf('45', plain,
% 0.48/0.69      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.48/0.69         ((zip_tseitin_0 @ X23 @ X24 @ X25 @ X26)
% 0.48/0.69          | (r2_hidden @ X23 @ X27)
% 0.48/0.69          | ((X27) != (k1_enumset1 @ X26 @ X25 @ X24)))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.48/0.69  thf('46', plain,
% 0.48/0.69      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.48/0.69         ((r2_hidden @ X23 @ (k1_enumset1 @ X26 @ X25 @ X24))
% 0.48/0.69          | (zip_tseitin_0 @ X23 @ X24 @ X25 @ X26))),
% 0.48/0.69      inference('simplify', [status(thm)], ['45'])).
% 0.48/0.69  thf('47', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((r2_hidden @ X0 @ (k2_tarski @ sk_C @ sk_D_1))
% 0.48/0.69          | (zip_tseitin_0 @ X0 @ sk_D_1 @ sk_C @ sk_A))),
% 0.48/0.69      inference('sup+', [status(thm)], ['44', '46'])).
% 0.48/0.69  thf(d2_tarski, axiom,
% 0.48/0.69    (![A:$i,B:$i,C:$i]:
% 0.48/0.69     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.48/0.69       ( ![D:$i]:
% 0.48/0.69         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.48/0.69  thf('48', plain,
% 0.48/0.69      (![X30 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.48/0.69         (~ (r2_hidden @ X34 @ X32)
% 0.48/0.69          | ((X34) = (X33))
% 0.48/0.69          | ((X34) = (X30))
% 0.48/0.69          | ((X32) != (k2_tarski @ X33 @ X30)))),
% 0.48/0.69      inference('cnf', [status(esa)], [d2_tarski])).
% 0.48/0.69  thf('49', plain,
% 0.48/0.69      (![X30 : $i, X33 : $i, X34 : $i]:
% 0.48/0.69         (((X34) = (X30))
% 0.48/0.69          | ((X34) = (X33))
% 0.48/0.69          | ~ (r2_hidden @ X34 @ (k2_tarski @ X33 @ X30)))),
% 0.48/0.69      inference('simplify', [status(thm)], ['48'])).
% 0.48/0.69  thf('50', plain,
% 0.48/0.69      (![X0 : $i]:
% 0.48/0.69         ((zip_tseitin_0 @ X0 @ sk_D_1 @ sk_C @ sk_A)
% 0.48/0.69          | ((X0) = (sk_C))
% 0.48/0.69          | ((X0) = (sk_D_1)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['47', '49'])).
% 0.48/0.69  thf('51', plain,
% 0.48/0.69      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.48/0.69         (((X19) != (X18)) | ~ (zip_tseitin_0 @ X19 @ X20 @ X21 @ X18))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.48/0.69  thf('52', plain,
% 0.48/0.69      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.48/0.69         ~ (zip_tseitin_0 @ X18 @ X20 @ X21 @ X18)),
% 0.48/0.69      inference('simplify', [status(thm)], ['51'])).
% 0.48/0.69  thf('53', plain, ((((sk_A) = (sk_D_1)) | ((sk_A) = (sk_C)))),
% 0.48/0.69      inference('sup-', [status(thm)], ['50', '52'])).
% 0.48/0.69  thf('54', plain, (((sk_A) != (sk_C))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('55', plain, (((sk_A) != (sk_D_1))),
% 0.48/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.69  thf('56', plain, ($false),
% 0.48/0.69      inference('simplify_reflect-', [status(thm)], ['53', '54', '55'])).
% 0.48/0.69  
% 0.48/0.69  % SZS output end Refutation
% 0.48/0.69  
% 0.48/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
