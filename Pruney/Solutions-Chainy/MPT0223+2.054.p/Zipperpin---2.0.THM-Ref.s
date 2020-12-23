%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cWyLCFfEmq

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:29:37 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   80 (  92 expanded)
%              Number of leaves         :   35 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :  662 ( 791 expanded)
%              Number of equality atoms :   65 (  79 expanded)
%              Maximal formula depth    :   19 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t18_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
     => ( A = B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
          = ( k1_tarski @ A ) )
       => ( A = B ) ) ),
    inference('cnf.neg',[status(esa)],[t18_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('2',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('3',plain,(
    ! [X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X3 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('4',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['2','3'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k2_xboole_0 @ X4 @ X5 )
      = ( k5_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('6',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_B ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('7',plain,(
    ! [X2: $i] :
      ( ( k5_xboole_0 @ X2 @ k1_xboole_0 )
      = X2 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('8',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('9',plain,(
    ! [X62: $i] :
      ( ( k2_tarski @ X62 @ X62 )
      = ( k1_tarski @ X62 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('10',plain,(
    ! [X65: $i,X66: $i,X67: $i] :
      ( ( k2_enumset1 @ X65 @ X65 @ X66 @ X67 )
      = ( k1_enumset1 @ X65 @ X66 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k1_enumset1 @ X63 @ X63 @ X64 )
      = ( k2_tarski @ X63 @ X64 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('13',plain,(
    ! [X68: $i,X69: $i,X70: $i,X71: $i] :
      ( ( k3_enumset1 @ X68 @ X68 @ X69 @ X70 @ X71 )
      = ( k2_enumset1 @ X68 @ X69 @ X70 @ X71 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('15',plain,(
    ! [X83: $i,X84: $i,X85: $i,X86: $i,X87: $i,X88: $i,X89: $i] :
      ( ( k6_enumset1 @ X83 @ X83 @ X84 @ X85 @ X86 @ X87 @ X88 @ X89 )
      = ( k5_enumset1 @ X83 @ X84 @ X85 @ X86 @ X87 @ X88 @ X89 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('16',plain,(
    ! [X77: $i,X78: $i,X79: $i,X80: $i,X81: $i,X82: $i] :
      ( ( k5_enumset1 @ X77 @ X77 @ X78 @ X79 @ X80 @ X81 @ X82 )
      = ( k4_enumset1 @ X77 @ X78 @ X79 @ X80 @ X81 @ X82 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X77: $i,X78: $i,X79: $i,X80: $i,X81: $i,X82: $i] :
      ( ( k5_enumset1 @ X77 @ X77 @ X78 @ X79 @ X80 @ X81 @ X82 )
      = ( k4_enumset1 @ X77 @ X78 @ X79 @ X80 @ X81 @ X82 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('19',plain,(
    ! [X54: $i,X55: $i,X56: $i,X57: $i,X58: $i,X59: $i,X60: $i,X61: $i] :
      ( ( k6_enumset1 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 ) @ ( k1_tarski @ X61 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['17','20'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('22',plain,(
    ! [X72: $i,X73: $i,X74: $i,X75: $i,X76: $i] :
      ( ( k4_enumset1 @ X72 @ X72 @ X73 @ X74 @ X75 @ X76 )
      = ( k3_enumset1 @ X72 @ X73 @ X74 @ X75 @ X76 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X72: $i,X73: $i,X74: $i,X75: $i,X76: $i] :
      ( ( k4_enumset1 @ X72 @ X72 @ X73 @ X74 @ X75 @ X76 )
      = ( k3_enumset1 @ X72 @ X73 @ X74 @ X75 @ X76 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['9','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( k2_tarski @ sk_B @ sk_A )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['8','29'])).

thf('31',plain,(
    ! [X63: $i,X64: $i] :
      ( ( k1_enumset1 @ X63 @ X63 @ X64 )
      = ( k2_tarski @ X63 @ X64 ) ) ),
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

thf('32',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ( r2_hidden @ X11 @ X15 )
      | ( X15
       != ( k1_enumset1 @ X14 @ X13 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('33',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X11 @ ( k1_enumset1 @ X14 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X7 != X8 )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('36',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ~ ( zip_tseitin_0 @ X8 @ X8 @ X9 @ X6 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_B ) ),
    inference('sup+',[status(thm)],['30','37'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('39',plain,(
    ! [X18: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X21 @ X20 )
      | ( X21 = X18 )
      | ( X20
       != ( k1_tarski @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('40',plain,(
    ! [X18: $i,X21: $i] :
      ( ( X21 = X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_tarski @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    sk_A = sk_B ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.cWyLCFfEmq
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.45/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.45/0.67  % Solved by: fo/fo7.sh
% 0.45/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.67  % done 503 iterations in 0.238s
% 0.45/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.45/0.67  % SZS output start Refutation
% 0.45/0.67  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.67  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.45/0.67                                           $i > $i).
% 0.45/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.45/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.67  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.67  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.45/0.67  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.67  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.67  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.45/0.67  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.45/0.67  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.45/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.67  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.67  thf(t18_zfmisc_1, conjecture,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.45/0.67         ( k1_tarski @ A ) ) =>
% 0.45/0.67       ( ( A ) = ( B ) ) ))).
% 0.45/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.67    (~( ![A:$i,B:$i]:
% 0.45/0.67        ( ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.45/0.67            ( k1_tarski @ A ) ) =>
% 0.45/0.67          ( ( A ) = ( B ) ) ) )),
% 0.45/0.67    inference('cnf.neg', [status(esa)], [t18_zfmisc_1])).
% 0.45/0.67  thf('0', plain,
% 0.45/0.67      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.45/0.67         = (k1_tarski @ sk_A))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf(t100_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.45/0.67  thf('1', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k4_xboole_0 @ X0 @ X1)
% 0.45/0.67           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.45/0.67  thf('2', plain,
% 0.45/0.67      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B))
% 0.45/0.67         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['0', '1'])).
% 0.45/0.67  thf(t92_xboole_1, axiom,
% 0.45/0.67    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.45/0.67  thf('3', plain, (![X3 : $i]: ((k5_xboole_0 @ X3 @ X3) = (k1_xboole_0))),
% 0.45/0.67      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.45/0.67  thf('4', plain,
% 0.45/0.67      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) = (k1_xboole_0))),
% 0.45/0.67      inference('demod', [status(thm)], ['2', '3'])).
% 0.45/0.67  thf(t98_xboole_1, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.45/0.67  thf('5', plain,
% 0.45/0.67      (![X4 : $i, X5 : $i]:
% 0.45/0.67         ((k2_xboole_0 @ X4 @ X5)
% 0.45/0.67           = (k5_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X4)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.45/0.67  thf('6', plain,
% 0.45/0.67      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.45/0.67         = (k5_xboole_0 @ (k1_tarski @ sk_B) @ k1_xboole_0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['4', '5'])).
% 0.45/0.67  thf(t5_boole, axiom,
% 0.45/0.67    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.67  thf('7', plain, (![X2 : $i]: ((k5_xboole_0 @ X2 @ k1_xboole_0) = (X2))),
% 0.45/0.67      inference('cnf', [status(esa)], [t5_boole])).
% 0.45/0.67  thf('8', plain,
% 0.45/0.67      (((k2_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ sk_A))
% 0.45/0.67         = (k1_tarski @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['6', '7'])).
% 0.45/0.67  thf(t69_enumset1, axiom,
% 0.45/0.67    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.67  thf('9', plain, (![X62 : $i]: ((k2_tarski @ X62 @ X62) = (k1_tarski @ X62))),
% 0.45/0.67      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.67  thf(t71_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i]:
% 0.45/0.67     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.45/0.67  thf('10', plain,
% 0.45/0.67      (![X65 : $i, X66 : $i, X67 : $i]:
% 0.45/0.67         ((k2_enumset1 @ X65 @ X65 @ X66 @ X67)
% 0.45/0.67           = (k1_enumset1 @ X65 @ X66 @ X67))),
% 0.45/0.67      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.45/0.67  thf(t70_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.45/0.67  thf('11', plain,
% 0.45/0.67      (![X63 : $i, X64 : $i]:
% 0.45/0.67         ((k1_enumset1 @ X63 @ X63 @ X64) = (k2_tarski @ X63 @ X64))),
% 0.45/0.67      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.67  thf('12', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['10', '11'])).
% 0.45/0.67  thf(t72_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.45/0.67  thf('13', plain,
% 0.45/0.67      (![X68 : $i, X69 : $i, X70 : $i, X71 : $i]:
% 0.45/0.67         ((k3_enumset1 @ X68 @ X68 @ X69 @ X70 @ X71)
% 0.45/0.67           = (k2_enumset1 @ X68 @ X69 @ X70 @ X71))),
% 0.45/0.67      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.45/0.67  thf('14', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['12', '13'])).
% 0.45/0.67  thf(t75_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.45/0.67     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.45/0.67       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.45/0.67  thf('15', plain,
% 0.45/0.67      (![X83 : $i, X84 : $i, X85 : $i, X86 : $i, X87 : $i, X88 : $i, X89 : $i]:
% 0.45/0.67         ((k6_enumset1 @ X83 @ X83 @ X84 @ X85 @ X86 @ X87 @ X88 @ X89)
% 0.45/0.67           = (k5_enumset1 @ X83 @ X84 @ X85 @ X86 @ X87 @ X88 @ X89))),
% 0.45/0.67      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.45/0.67  thf(t74_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.45/0.67     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.45/0.67       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.45/0.67  thf('16', plain,
% 0.45/0.67      (![X77 : $i, X78 : $i, X79 : $i, X80 : $i, X81 : $i, X82 : $i]:
% 0.45/0.67         ((k5_enumset1 @ X77 @ X77 @ X78 @ X79 @ X80 @ X81 @ X82)
% 0.45/0.67           = (k4_enumset1 @ X77 @ X78 @ X79 @ X80 @ X81 @ X82))),
% 0.45/0.67      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.45/0.67  thf('17', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.67         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.45/0.67           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['15', '16'])).
% 0.45/0.67  thf('18', plain,
% 0.45/0.67      (![X77 : $i, X78 : $i, X79 : $i, X80 : $i, X81 : $i, X82 : $i]:
% 0.45/0.67         ((k5_enumset1 @ X77 @ X77 @ X78 @ X79 @ X80 @ X81 @ X82)
% 0.45/0.67           = (k4_enumset1 @ X77 @ X78 @ X79 @ X80 @ X81 @ X82))),
% 0.45/0.67      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.45/0.67  thf(t68_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.45/0.67     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.45/0.67       ( k2_xboole_0 @
% 0.45/0.67         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 0.45/0.67  thf('19', plain,
% 0.45/0.67      (![X54 : $i, X55 : $i, X56 : $i, X57 : $i, X58 : $i, X59 : $i, X60 : $i, 
% 0.45/0.67         X61 : $i]:
% 0.45/0.67         ((k6_enumset1 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60 @ X61)
% 0.45/0.67           = (k2_xboole_0 @ 
% 0.45/0.67              (k5_enumset1 @ X54 @ X55 @ X56 @ X57 @ X58 @ X59 @ X60) @ 
% 0.45/0.67              (k1_tarski @ X61)))),
% 0.45/0.67      inference('cnf', [status(esa)], [t68_enumset1])).
% 0.45/0.67  thf('20', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.45/0.67         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 0.45/0.67           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.45/0.67              (k1_tarski @ X6)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['18', '19'])).
% 0.45/0.67  thf('21', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.67         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.45/0.67           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.45/0.67              (k1_tarski @ X0)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['17', '20'])).
% 0.45/0.67  thf(t73_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.45/0.67     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.45/0.67       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.45/0.67  thf('22', plain,
% 0.45/0.67      (![X72 : $i, X73 : $i, X74 : $i, X75 : $i, X76 : $i]:
% 0.45/0.67         ((k4_enumset1 @ X72 @ X72 @ X73 @ X74 @ X75 @ X76)
% 0.45/0.67           = (k3_enumset1 @ X72 @ X73 @ X74 @ X75 @ X76))),
% 0.45/0.67      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.45/0.67  thf('23', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.45/0.67         ((k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.45/0.67           = (k2_xboole_0 @ (k3_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1) @ 
% 0.45/0.67              (k1_tarski @ X0)))),
% 0.45/0.67      inference('demod', [status(thm)], ['21', '22'])).
% 0.45/0.67  thf('24', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((k4_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 0.45/0.67           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['14', '23'])).
% 0.45/0.67  thf('25', plain,
% 0.45/0.67      (![X72 : $i, X73 : $i, X74 : $i, X75 : $i, X76 : $i]:
% 0.45/0.67         ((k4_enumset1 @ X72 @ X72 @ X73 @ X74 @ X75 @ X76)
% 0.45/0.67           = (k3_enumset1 @ X72 @ X73 @ X74 @ X75 @ X76))),
% 0.45/0.67      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.45/0.67  thf('26', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2)
% 0.45/0.67           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.45/0.67      inference('demod', [status(thm)], ['24', '25'])).
% 0.45/0.67  thf('27', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k3_enumset1 @ X0 @ X0 @ X0 @ X0 @ X1)
% 0.45/0.67           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.45/0.67      inference('sup+', [status(thm)], ['9', '26'])).
% 0.45/0.67  thf('28', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k3_enumset1 @ X1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.45/0.67      inference('sup+', [status(thm)], ['12', '13'])).
% 0.45/0.67  thf('29', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]:
% 0.45/0.67         ((k2_tarski @ X0 @ X1)
% 0.45/0.67           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k1_tarski @ X1)))),
% 0.45/0.67      inference('demod', [status(thm)], ['27', '28'])).
% 0.45/0.67  thf('30', plain, (((k2_tarski @ sk_B @ sk_A) = (k1_tarski @ sk_B))),
% 0.45/0.67      inference('demod', [status(thm)], ['8', '29'])).
% 0.45/0.67  thf('31', plain,
% 0.45/0.67      (![X63 : $i, X64 : $i]:
% 0.45/0.67         ((k1_enumset1 @ X63 @ X63 @ X64) = (k2_tarski @ X63 @ X64))),
% 0.45/0.67      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.45/0.67  thf(d1_enumset1, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.67       ( ![E:$i]:
% 0.45/0.67         ( ( r2_hidden @ E @ D ) <=>
% 0.45/0.67           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.45/0.67  thf(zf_stmt_2, axiom,
% 0.45/0.67    (![E:$i,C:$i,B:$i,A:$i]:
% 0.45/0.67     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.45/0.67       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.45/0.67  thf(zf_stmt_3, axiom,
% 0.45/0.67    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.67     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.45/0.67       ( ![E:$i]:
% 0.45/0.67         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.45/0.67  thf('32', plain,
% 0.45/0.67      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.45/0.67         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 0.45/0.67          | (r2_hidden @ X11 @ X15)
% 0.45/0.67          | ((X15) != (k1_enumset1 @ X14 @ X13 @ X12)))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.45/0.67  thf('33', plain,
% 0.45/0.67      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.67         ((r2_hidden @ X11 @ (k1_enumset1 @ X14 @ X13 @ X12))
% 0.45/0.67          | (zip_tseitin_0 @ X11 @ X12 @ X13 @ X14))),
% 0.45/0.67      inference('simplify', [status(thm)], ['32'])).
% 0.45/0.67  thf('34', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.67         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.45/0.67          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.45/0.67      inference('sup+', [status(thm)], ['31', '33'])).
% 0.45/0.67  thf('35', plain,
% 0.45/0.67      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.45/0.67         (((X7) != (X8)) | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X6))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.67  thf('36', plain,
% 0.45/0.67      (![X6 : $i, X8 : $i, X9 : $i]: ~ (zip_tseitin_0 @ X8 @ X8 @ X9 @ X6)),
% 0.45/0.67      inference('simplify', [status(thm)], ['35'])).
% 0.45/0.67  thf('37', plain,
% 0.45/0.67      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.45/0.67      inference('sup-', [status(thm)], ['34', '36'])).
% 0.45/0.67  thf('38', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_B))),
% 0.45/0.67      inference('sup+', [status(thm)], ['30', '37'])).
% 0.45/0.67  thf(d1_tarski, axiom,
% 0.45/0.67    (![A:$i,B:$i]:
% 0.45/0.67     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.67       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.45/0.67  thf('39', plain,
% 0.45/0.67      (![X18 : $i, X20 : $i, X21 : $i]:
% 0.45/0.67         (~ (r2_hidden @ X21 @ X20)
% 0.45/0.67          | ((X21) = (X18))
% 0.45/0.67          | ((X20) != (k1_tarski @ X18)))),
% 0.45/0.67      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.67  thf('40', plain,
% 0.45/0.67      (![X18 : $i, X21 : $i]:
% 0.45/0.67         (((X21) = (X18)) | ~ (r2_hidden @ X21 @ (k1_tarski @ X18)))),
% 0.45/0.67      inference('simplify', [status(thm)], ['39'])).
% 0.45/0.67  thf('41', plain, (((sk_A) = (sk_B))),
% 0.45/0.67      inference('sup-', [status(thm)], ['38', '40'])).
% 0.45/0.67  thf('42', plain, (((sk_A) != (sk_B))),
% 0.45/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.67  thf('43', plain, ($false),
% 0.45/0.67      inference('simplify_reflect-', [status(thm)], ['41', '42'])).
% 0.45/0.67  
% 0.45/0.67  % SZS output end Refutation
% 0.45/0.67  
% 0.45/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
