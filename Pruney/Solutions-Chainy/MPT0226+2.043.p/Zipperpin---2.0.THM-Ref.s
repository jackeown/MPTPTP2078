%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9Hsu4IzCGs

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:56 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   73 (  85 expanded)
%              Number of leaves         :   32 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :  613 ( 740 expanded)
%              Number of equality atoms :   59 (  73 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t21_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = k1_xboole_0 )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = k1_xboole_0 )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t21_zfmisc_1])).

thf('0',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ X4 )
      = ( k5_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('4',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('6',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X37 @ X37 @ X38 @ X39 )
      = ( k1_enumset1 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('9',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( k3_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43 )
      = ( k2_enumset1 @ X40 @ X41 @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('11',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k5_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k4_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('12',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( k6_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 ) @ ( k1_tarski @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('14',plain,(
    ! [X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( k6_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 )
      = ( k5_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('15',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k5_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k4_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('17',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k4_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48 )
      = ( k3_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( k4_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48 )
      = ( k3_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['10','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) )
      = ( k2_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['4','25'])).

thf('27',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
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

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 )
      | ( r2_hidden @ X10 @ X14 )
      | ( X14
       != ( k1_enumset1 @ X13 @ X12 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('29',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ ( k1_enumset1 @ X13 @ X12 @ X11 ) )
      | ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','29'])).

thf('31',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( X6 != X7 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 @ X5 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('32',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ~ ( zip_tseitin_0 @ X7 @ X7 @ X8 @ X5 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['26','33'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('35',plain,(
    ! [X17: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ( X20 = X17 )
      | ( X19
       != ( k1_tarski @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('36',plain,(
    ! [X17: $i,X20: $i] :
      ( ( X20 = X17 )
      | ~ ( r2_hidden @ X20 @ ( k1_tarski @ X17 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9Hsu4IzCGs
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:08:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.55/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.74  % Solved by: fo/fo7.sh
% 0.55/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.74  % done 503 iterations in 0.273s
% 0.55/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.74  % SZS output start Refutation
% 0.55/0.74  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.55/0.74  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.55/0.74                                           $i > $i).
% 0.55/0.74  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.55/0.74  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.55/0.74  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.55/0.74  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.55/0.74  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.74  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.55/0.74  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.55/0.74  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.55/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.74  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.55/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.74  thf(sk_B_type, type, sk_B: $i).
% 0.55/0.74  thf(t21_zfmisc_1, conjecture,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.55/0.74         ( k1_xboole_0 ) ) =>
% 0.55/0.74       ( ( A ) = ( B ) ) ))).
% 0.55/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.74    (~( ![A:$i,B:$i]:
% 0.55/0.74        ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.55/0.74            ( k1_xboole_0 ) ) =>
% 0.55/0.74          ( ( A ) = ( B ) ) ) )),
% 0.55/0.74    inference('cnf.neg', [status(esa)], [t21_zfmisc_1])).
% 0.55/0.74  thf('0', plain,
% 0.55/0.74      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf(t98_xboole_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.55/0.74  thf('1', plain,
% 0.55/0.74      (![X3 : $i, X4 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ X3 @ X4)
% 0.55/0.74           = (k5_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.55/0.74  thf('2', plain,
% 0.55/0.74      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.55/0.74         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['0', '1'])).
% 0.55/0.74  thf(t5_boole, axiom,
% 0.55/0.74    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.55/0.74  thf('3', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.55/0.74      inference('cnf', [status(esa)], [t5_boole])).
% 0.55/0.74  thf('4', plain,
% 0.55/0.74      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.55/0.74         = (k1_tarski @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['2', '3'])).
% 0.55/0.74  thf(t69_enumset1, axiom,
% 0.55/0.74    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.55/0.74  thf('5', plain, (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.55/0.74      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.55/0.74  thf(t71_enumset1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i]:
% 0.55/0.74     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.55/0.74  thf('6', plain,
% 0.55/0.74      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.55/0.74         ((k2_enumset1 @ X37 @ X37 @ X38 @ X39)
% 0.55/0.74           = (k1_enumset1 @ X37 @ X38 @ X39))),
% 0.55/0.74      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.55/0.74  thf(t70_enumset1, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.55/0.74  thf('7', plain,
% 0.55/0.74      (![X35 : $i, X36 : $i]:
% 0.55/0.74         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.55/0.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.55/0.74  thf('8', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['6', '7'])).
% 0.55/0.74  thf(t72_enumset1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.74     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.55/0.74  thf('9', plain,
% 0.55/0.74      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.55/0.74         ((k3_enumset1 @ X40 @ X40 @ X41 @ X42 @ X43)
% 0.55/0.74           = (k2_enumset1 @ X40 @ X41 @ X42 @ X43))),
% 0.55/0.74      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.55/0.74  thf('10', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['8', '9'])).
% 0.55/0.74  thf(t74_enumset1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.55/0.74     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.55/0.74       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.55/0.74  thf('11', plain,
% 0.55/0.74      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.55/0.74         ((k5_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54)
% 0.55/0.74           = (k4_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 0.55/0.74      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.55/0.74  thf(t68_enumset1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.55/0.74     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.55/0.74       ( k2_xboole_0 @
% 0.55/0.74         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 0.55/0.74  thf('12', plain,
% 0.55/0.74      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, 
% 0.55/0.74         X33 : $i]:
% 0.55/0.74         ((k6_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32 @ X33)
% 0.55/0.74           = (k2_xboole_0 @ 
% 0.55/0.74              (k5_enumset1 @ X26 @ X27 @ X28 @ X29 @ X30 @ X31 @ X32) @ 
% 0.55/0.74              (k1_tarski @ X33)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t68_enumset1])).
% 0.55/0.74  thf('13', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.55/0.74         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 0.55/0.74           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.55/0.74              (k1_tarski @ X6)))),
% 0.55/0.74      inference('sup+', [status(thm)], ['11', '12'])).
% 0.55/0.74  thf(t75_enumset1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.55/0.74     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.55/0.74       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.55/0.74  thf('14', plain,
% 0.55/0.74      (![X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i, X61 : $i]:
% 0.55/0.74         ((k6_enumset1 @ X55 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61)
% 0.55/0.74           = (k5_enumset1 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61))),
% 0.55/0.74      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.55/0.74  thf('15', plain,
% 0.55/0.74      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.55/0.74         ((k5_enumset1 @ X49 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54)
% 0.55/0.74           = (k4_enumset1 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 0.55/0.74      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.55/0.74  thf('16', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.55/0.74         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.55/0.74           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['14', '15'])).
% 0.55/0.74  thf(t73_enumset1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.55/0.74     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.55/0.74       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.55/0.74  thf('17', plain,
% 0.55/0.74      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.55/0.74         ((k4_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48)
% 0.55/0.74           = (k3_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48))),
% 0.55/0.74      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.55/0.74  thf('18', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.55/0.74         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.55/0.74           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['16', '17'])).
% 0.55/0.74  thf('19', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ (k4_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 0.55/0.74           (k1_tarski @ X0)) = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['13', '18'])).
% 0.55/0.74  thf('20', plain,
% 0.55/0.74      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.55/0.74         ((k4_enumset1 @ X44 @ X44 @ X45 @ X46 @ X47 @ X48)
% 0.55/0.74           = (k3_enumset1 @ X44 @ X45 @ X46 @ X47 @ X48))),
% 0.55/0.74      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.55/0.74  thf('21', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ (k3_enumset1 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 0.55/0.74           (k1_tarski @ X0)) = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.55/0.74      inference('demod', [status(thm)], ['19', '20'])).
% 0.55/0.74  thf('22', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 0.55/0.74           = (k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2))),
% 0.55/0.74      inference('sup+', [status(thm)], ['10', '21'])).
% 0.55/0.74  thf('23', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.55/0.74           = (k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1))),
% 0.55/0.74      inference('sup+', [status(thm)], ['5', '22'])).
% 0.55/0.74  thf('24', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['8', '9'])).
% 0.55/0.74  thf('25', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1))
% 0.55/0.74           = (k2_tarski @ X0 @ X1))),
% 0.55/0.74      inference('demod', [status(thm)], ['23', '24'])).
% 0.55/0.74  thf('26', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.55/0.74      inference('demod', [status(thm)], ['4', '25'])).
% 0.55/0.74  thf('27', plain,
% 0.55/0.74      (![X35 : $i, X36 : $i]:
% 0.55/0.74         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.55/0.74      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.55/0.74  thf(d1_enumset1, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.74     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.55/0.74       ( ![E:$i]:
% 0.55/0.74         ( ( r2_hidden @ E @ D ) <=>
% 0.55/0.74           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.55/0.74  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.55/0.74  thf(zf_stmt_2, axiom,
% 0.55/0.74    (![E:$i,C:$i,B:$i,A:$i]:
% 0.55/0.74     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.55/0.74       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.55/0.74  thf(zf_stmt_3, axiom,
% 0.55/0.74    (![A:$i,B:$i,C:$i,D:$i]:
% 0.55/0.74     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.55/0.74       ( ![E:$i]:
% 0.55/0.74         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.55/0.74  thf('28', plain,
% 0.55/0.74      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.55/0.74         ((zip_tseitin_0 @ X10 @ X11 @ X12 @ X13)
% 0.55/0.74          | (r2_hidden @ X10 @ X14)
% 0.55/0.74          | ((X14) != (k1_enumset1 @ X13 @ X12 @ X11)))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.55/0.74  thf('29', plain,
% 0.55/0.74      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.55/0.74         ((r2_hidden @ X10 @ (k1_enumset1 @ X13 @ X12 @ X11))
% 0.55/0.74          | (zip_tseitin_0 @ X10 @ X11 @ X12 @ X13))),
% 0.55/0.74      inference('simplify', [status(thm)], ['28'])).
% 0.55/0.74  thf('30', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.55/0.74         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.55/0.74          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.55/0.74      inference('sup+', [status(thm)], ['27', '29'])).
% 0.55/0.74  thf('31', plain,
% 0.55/0.74      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.55/0.74         (((X6) != (X7)) | ~ (zip_tseitin_0 @ X6 @ X7 @ X8 @ X5))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.55/0.74  thf('32', plain,
% 0.55/0.74      (![X5 : $i, X7 : $i, X8 : $i]: ~ (zip_tseitin_0 @ X7 @ X7 @ X8 @ X5)),
% 0.55/0.74      inference('simplify', [status(thm)], ['31'])).
% 0.55/0.74  thf('33', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.55/0.74      inference('sup-', [status(thm)], ['30', '32'])).
% 0.55/0.74  thf('34', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.55/0.74      inference('sup+', [status(thm)], ['26', '33'])).
% 0.55/0.74  thf(d1_tarski, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.55/0.74       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.55/0.74  thf('35', plain,
% 0.55/0.74      (![X17 : $i, X19 : $i, X20 : $i]:
% 0.55/0.74         (~ (r2_hidden @ X20 @ X19)
% 0.55/0.74          | ((X20) = (X17))
% 0.55/0.74          | ((X19) != (k1_tarski @ X17)))),
% 0.55/0.74      inference('cnf', [status(esa)], [d1_tarski])).
% 0.55/0.74  thf('36', plain,
% 0.55/0.74      (![X17 : $i, X20 : $i]:
% 0.55/0.74         (((X20) = (X17)) | ~ (r2_hidden @ X20 @ (k1_tarski @ X17)))),
% 0.55/0.74      inference('simplify', [status(thm)], ['35'])).
% 0.55/0.74  thf('37', plain, (((sk_A) = (sk_B))),
% 0.55/0.74      inference('sup-', [status(thm)], ['34', '36'])).
% 0.55/0.74  thf('38', plain, (((sk_A) != (sk_B))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('39', plain, ($false),
% 0.55/0.74      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.55/0.74  
% 0.55/0.74  % SZS output end Refutation
% 0.55/0.74  
% 0.55/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
