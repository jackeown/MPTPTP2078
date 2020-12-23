%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U8w8GpUBpr

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:52 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :   77 (  90 expanded)
%              Number of leaves         :   30 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :  615 ( 747 expanded)
%              Number of equality atoms :   62 (  79 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

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
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 )
      | ( X12 = X13 )
      | ( X12 = X14 )
      | ( X12 = X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = k1_xboole_0 )
     => ( A = B ) ) )).

thf(zf_stmt_1,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t21_zfmisc_1])).

thf('1',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ( k2_xboole_0 @ X7 @ X8 )
      = ( k5_xboole_0 @ X7 @ ( k4_xboole_0 @ X8 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('4',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('5',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('6',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( k2_enumset1 @ X33 @ X33 @ X34 @ X35 )
      = ( k1_enumset1 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('11',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( k5_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 )
      = ( k4_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('12',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k4_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 @ X44 )
      = ( k3_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ( k4_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 @ X44 )
      = ( k3_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t61_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G )
      = ( k2_xboole_0 @ ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( k5_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 ) @ ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[t61_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X5 ) ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('18',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k3_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['10','19'])).

thf('21',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( k3_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39 )
      = ( k2_enumset1 @ X36 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k2_tarski @ X10 @ X9 )
      = ( k2_tarski @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('26',plain,
    ( ( k2_tarski @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['5','24','25'])).

thf('27',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('28',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 )
      | ( r2_hidden @ X16 @ X20 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('29',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( r2_hidden @ X16 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X12 != X11 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ~ ( zip_tseitin_0 @ X11 @ X13 @ X14 @ X11 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['26','33'])).

thf('35',plain,(
    ! [X30: $i] :
      ( ( k2_tarski @ X30 @ X30 )
      = ( k1_tarski @ X30 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('36',plain,(
    ! [X31: $i,X32: $i] :
      ( ( k1_enumset1 @ X31 @ X31 @ X32 )
      = ( k2_tarski @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('37',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ~ ( zip_tseitin_0 @ X21 @ X17 @ X18 @ X19 )
      | ( X20
       != ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('38',plain,(
    ! [X17: $i,X18: $i,X19: $i,X21: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X17 @ X18 @ X19 )
      | ~ ( r2_hidden @ X21 @ ( k1_enumset1 @ X19 @ X18 @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    ~ ( zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_B )
    | ( sk_A = sk_B ) ),
    inference('sup-',[status(thm)],['0','41'])).

thf('43',plain,(
    sk_A = sk_B ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.U8w8GpUBpr
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:20:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.48/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.48/0.68  % Solved by: fo/fo7.sh
% 0.48/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.48/0.68  % done 627 iterations in 0.224s
% 0.48/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.48/0.68  % SZS output start Refutation
% 0.48/0.68  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.48/0.68  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.48/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.48/0.68  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.48/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.48/0.68  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.48/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.48/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.48/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.48/0.68  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.48/0.68  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.48/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.48/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.48/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.48/0.68  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.48/0.68  thf(d1_enumset1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.68     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.48/0.68       ( ![E:$i]:
% 0.48/0.68         ( ( r2_hidden @ E @ D ) <=>
% 0.48/0.68           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.48/0.68  thf(zf_stmt_0, axiom,
% 0.48/0.68    (![E:$i,C:$i,B:$i,A:$i]:
% 0.48/0.68     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.48/0.68       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.48/0.68  thf('0', plain,
% 0.48/0.68      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.48/0.68         ((zip_tseitin_0 @ X12 @ X13 @ X14 @ X15)
% 0.48/0.68          | ((X12) = (X13))
% 0.48/0.68          | ((X12) = (X14))
% 0.48/0.68          | ((X12) = (X15)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf(t21_zfmisc_1, conjecture,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.48/0.68         ( k1_xboole_0 ) ) =>
% 0.48/0.68       ( ( A ) = ( B ) ) ))).
% 0.48/0.68  thf(zf_stmt_1, negated_conjecture,
% 0.48/0.68    (~( ![A:$i,B:$i]:
% 0.48/0.68        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.48/0.68            ( k1_xboole_0 ) ) =>
% 0.48/0.68          ( ( A ) = ( B ) ) ) )),
% 0.48/0.68    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 0.48/0.68  thf('1', plain,
% 0.48/0.68      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.48/0.68  thf(t98_xboole_1, axiom,
% 0.48/0.68    (![A:$i,B:$i]:
% 0.48/0.68     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.48/0.68  thf('2', plain,
% 0.48/0.68      (![X7 : $i, X8 : $i]:
% 0.48/0.68         ((k2_xboole_0 @ X7 @ X8)
% 0.48/0.68           = (k5_xboole_0 @ X7 @ (k4_xboole_0 @ X8 @ X7)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.48/0.68  thf('3', plain,
% 0.48/0.68      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.48/0.68         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['1', '2'])).
% 0.48/0.68  thf(t5_boole, axiom,
% 0.48/0.68    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.48/0.68  thf('4', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.48/0.68      inference('cnf', [status(esa)], [t5_boole])).
% 0.48/0.68  thf('5', plain,
% 0.48/0.68      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.48/0.68         = (k1_tarski @ sk_B))),
% 0.48/0.68      inference('demod', [status(thm)], ['3', '4'])).
% 0.48/0.68  thf(t71_enumset1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i]:
% 0.48/0.68     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.48/0.68  thf('6', plain,
% 0.48/0.68      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.48/0.68         ((k2_enumset1 @ X33 @ X33 @ X34 @ X35)
% 0.48/0.68           = (k1_enumset1 @ X33 @ X34 @ X35))),
% 0.48/0.68      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.48/0.68  thf(t70_enumset1, axiom,
% 0.48/0.68    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.48/0.68  thf('7', plain,
% 0.48/0.68      (![X31 : $i, X32 : $i]:
% 0.48/0.68         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 0.48/0.68      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.48/0.68  thf('8', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.48/0.68  thf(t69_enumset1, axiom,
% 0.48/0.68    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.48/0.68  thf('9', plain, (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 0.48/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.48/0.68  thf('10', plain,
% 0.48/0.68      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['8', '9'])).
% 0.48/0.68  thf(t74_enumset1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.48/0.68     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.48/0.68       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.48/0.68  thf('11', plain,
% 0.48/0.68      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.48/0.68         ((k5_enumset1 @ X45 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50)
% 0.48/0.68           = (k4_enumset1 @ X45 @ X46 @ X47 @ X48 @ X49 @ X50))),
% 0.48/0.68      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.48/0.68  thf(t73_enumset1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.48/0.68     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.48/0.68       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.48/0.68  thf('12', plain,
% 0.48/0.68      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.48/0.68         ((k4_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 @ X44)
% 0.48/0.68           = (k3_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44))),
% 0.48/0.68      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.48/0.68  thf('13', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.48/0.68         ((k5_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.48/0.68           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['11', '12'])).
% 0.48/0.68  thf('14', plain,
% 0.48/0.68      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 0.48/0.68         ((k4_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 @ X44)
% 0.48/0.68           = (k3_enumset1 @ X40 @ X41 @ X42 @ X43 @ X44))),
% 0.48/0.68      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.48/0.68  thf(t61_enumset1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.48/0.68     ( ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) =
% 0.48/0.68       ( k2_xboole_0 @
% 0.48/0.68         ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) @ ( k1_tarski @ G ) ) ))).
% 0.48/0.68  thf('15', plain,
% 0.48/0.68      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.48/0.68         ((k5_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28 @ X29)
% 0.48/0.68           = (k2_xboole_0 @ 
% 0.48/0.68              (k4_enumset1 @ X23 @ X24 @ X25 @ X26 @ X27 @ X28) @ 
% 0.48/0.68              (k1_tarski @ X29)))),
% 0.48/0.68      inference('cnf', [status(esa)], [t61_enumset1])).
% 0.48/0.68  thf('16', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.48/0.68         ((k5_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 @ X5)
% 0.48/0.68           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.48/0.68              (k1_tarski @ X5)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['14', '15'])).
% 0.48/0.68  thf('17', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.48/0.68         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.48/0.68           = (k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 0.48/0.68              (k1_tarski @ X0)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['13', '16'])).
% 0.48/0.68  thf(t72_enumset1, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.68     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.48/0.68  thf('18', plain,
% 0.48/0.68      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.48/0.68         ((k3_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39)
% 0.48/0.68           = (k2_enumset1 @ X36 @ X37 @ X38 @ X39))),
% 0.48/0.68      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.48/0.68  thf('19', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.48/0.68         ((k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.48/0.68           = (k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ 
% 0.48/0.68              (k1_tarski @ X0)))),
% 0.48/0.68      inference('demod', [status(thm)], ['17', '18'])).
% 0.48/0.68  thf('20', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1)
% 0.48/0.68           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.48/0.68      inference('sup+', [status(thm)], ['10', '19'])).
% 0.48/0.68  thf('21', plain,
% 0.48/0.68      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.48/0.68         ((k3_enumset1 @ X36 @ X36 @ X37 @ X38 @ X39)
% 0.48/0.68           = (k2_enumset1 @ X36 @ X37 @ X38 @ X39))),
% 0.48/0.68      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.48/0.68  thf('22', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k2_enumset1 @ X0 @ X0 @ X0 @ X1)
% 0.48/0.68           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.48/0.68      inference('demod', [status(thm)], ['20', '21'])).
% 0.48/0.68  thf('23', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['6', '7'])).
% 0.48/0.68  thf('24', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         ((k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.48/0.68           = (k2_tarski @ X1 @ X0))),
% 0.48/0.68      inference('sup+', [status(thm)], ['22', '23'])).
% 0.48/0.68  thf(commutativity_k2_tarski, axiom,
% 0.48/0.68    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.48/0.68  thf('25', plain,
% 0.48/0.68      (![X9 : $i, X10 : $i]: ((k2_tarski @ X10 @ X9) = (k2_tarski @ X9 @ X10))),
% 0.48/0.68      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.48/0.68  thf('26', plain, (((k2_tarski @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.48/0.68      inference('demod', [status(thm)], ['5', '24', '25'])).
% 0.48/0.68  thf('27', plain,
% 0.48/0.68      (![X31 : $i, X32 : $i]:
% 0.48/0.68         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 0.48/0.68      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.48/0.68  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.48/0.68  thf(zf_stmt_3, axiom,
% 0.48/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.48/0.68     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.48/0.68       ( ![E:$i]:
% 0.48/0.68         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.48/0.68  thf('28', plain,
% 0.48/0.68      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.48/0.68         ((zip_tseitin_0 @ X16 @ X17 @ X18 @ X19)
% 0.48/0.68          | (r2_hidden @ X16 @ X20)
% 0.48/0.68          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.48/0.68  thf('29', plain,
% 0.48/0.68      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.48/0.68         ((r2_hidden @ X16 @ (k1_enumset1 @ X19 @ X18 @ X17))
% 0.48/0.68          | (zip_tseitin_0 @ X16 @ X17 @ X18 @ X19))),
% 0.48/0.68      inference('simplify', [status(thm)], ['28'])).
% 0.48/0.68  thf('30', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.68         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.48/0.68          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.48/0.68      inference('sup+', [status(thm)], ['27', '29'])).
% 0.48/0.68  thf('31', plain,
% 0.48/0.68      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.48/0.68         (((X12) != (X11)) | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X11))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.48/0.68  thf('32', plain,
% 0.48/0.68      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.48/0.68         ~ (zip_tseitin_0 @ X11 @ X13 @ X14 @ X11)),
% 0.48/0.68      inference('simplify', [status(thm)], ['31'])).
% 0.48/0.68  thf('33', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.48/0.68      inference('sup-', [status(thm)], ['30', '32'])).
% 0.48/0.68  thf('34', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.48/0.68      inference('sup+', [status(thm)], ['26', '33'])).
% 0.48/0.68  thf('35', plain,
% 0.48/0.68      (![X30 : $i]: ((k2_tarski @ X30 @ X30) = (k1_tarski @ X30))),
% 0.48/0.68      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.48/0.68  thf('36', plain,
% 0.48/0.68      (![X31 : $i, X32 : $i]:
% 0.48/0.68         ((k1_enumset1 @ X31 @ X31 @ X32) = (k2_tarski @ X31 @ X32))),
% 0.48/0.68      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.48/0.68  thf('37', plain,
% 0.48/0.68      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.48/0.68         (~ (r2_hidden @ X21 @ X20)
% 0.48/0.68          | ~ (zip_tseitin_0 @ X21 @ X17 @ X18 @ X19)
% 0.48/0.68          | ((X20) != (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.48/0.68  thf('38', plain,
% 0.48/0.68      (![X17 : $i, X18 : $i, X19 : $i, X21 : $i]:
% 0.48/0.68         (~ (zip_tseitin_0 @ X21 @ X17 @ X18 @ X19)
% 0.48/0.68          | ~ (r2_hidden @ X21 @ (k1_enumset1 @ X19 @ X18 @ X17)))),
% 0.48/0.68      inference('simplify', [status(thm)], ['37'])).
% 0.48/0.68  thf('39', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.48/0.68         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.48/0.68          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.48/0.68      inference('sup-', [status(thm)], ['36', '38'])).
% 0.48/0.68  thf('40', plain,
% 0.48/0.68      (![X0 : $i, X1 : $i]:
% 0.48/0.68         (~ (r2_hidden @ X1 @ (k1_tarski @ X0))
% 0.48/0.68          | ~ (zip_tseitin_0 @ X1 @ X0 @ X0 @ X0))),
% 0.48/0.68      inference('sup-', [status(thm)], ['35', '39'])).
% 0.48/0.68  thf('41', plain, (~ (zip_tseitin_0 @ sk_A @ sk_B @ sk_B @ sk_B)),
% 0.48/0.68      inference('sup-', [status(thm)], ['34', '40'])).
% 0.48/0.68  thf('42', plain,
% 0.48/0.68      ((((sk_A) = (sk_B)) | ((sk_A) = (sk_B)) | ((sk_A) = (sk_B)))),
% 0.48/0.68      inference('sup-', [status(thm)], ['0', '41'])).
% 0.48/0.68  thf('43', plain, (((sk_A) = (sk_B))),
% 0.48/0.68      inference('simplify', [status(thm)], ['42'])).
% 0.48/0.68  thf('44', plain, (((sk_A) != (sk_B))),
% 0.48/0.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.48/0.68  thf('45', plain, ($false),
% 0.48/0.68      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.48/0.68  
% 0.48/0.68  % SZS output end Refutation
% 0.48/0.68  
% 0.48/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
