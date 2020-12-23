%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gvFFgiwGJ6

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:30 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :   64 (  70 expanded)
%              Number of leaves         :   29 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  556 ( 626 expanded)
%              Number of equality atoms :   49 (  55 expanded)
%              Maximal formula depth    :   19 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_enumset1_type,type,(
    k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i )).

thf(k3_enumset1_type,type,(
    k3_enumset1: $i > $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k6_enumset1_type,type,(
    k6_enumset1: $i > $i > $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_enumset1_type,type,(
    k4_enumset1: $i > $i > $i > $i > $i > $i > $i )).

thf(t26_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t26_zfmisc_1])).

thf('0',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 )
      | ~ ( r1_tarski @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('2',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ ( k1_tarski @ sk_C_1 ) )
    = ( k1_tarski @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('3',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k2_enumset1 @ X30 @ X30 @ X31 @ X32 )
      = ( k1_enumset1 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X28: $i,X29: $i] :
      ( ( k1_enumset1 @ X28 @ X28 @ X29 )
      = ( k2_tarski @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t74_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F )
      = ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ) )).

thf('6',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k5_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 )
      = ( k4_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf(t68_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i,H: $i] :
      ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H )
      = ( k2_xboole_0 @ ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ) )).

thf('7',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i,X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( k6_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26 )
      = ( k2_xboole_0 @ ( k5_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 ) @ ( k1_tarski @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t68_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6 )
      = ( k2_xboole_0 @ ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) @ ( k1_tarski @ X6 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t75_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i,G: $i] :
      ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G )
      = ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ) )).

thf('9',plain,(
    ! [X48: $i,X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ( k6_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 )
      = ( k5_enumset1 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t75_enumset1])).

thf('10',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( k5_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 )
      = ( k4_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t74_enumset1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(t73_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E )
      = ( k3_enumset1 @ A @ B @ C @ D @ E ) ) )).

thf('12',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k4_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 )
      = ( k3_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0 )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k4_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( k4_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41 )
      = ( k3_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t73_enumset1])).

thf(t72_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k3_enumset1 @ A @ A @ B @ C @ D )
      = ( k2_enumset1 @ A @ B @ C @ D ) ) )).

thf('16',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k3_enumset1 @ X33 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_enumset1 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ ( k2_enumset1 @ X4 @ X3 @ X2 @ X1 ) @ ( k1_tarski @ X0 ) )
      = ( k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','17'])).

thf('19',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( k3_enumset1 @ X33 @ X33 @ X34 @ X35 @ X36 )
      = ( k2_enumset1 @ X33 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t72_enumset1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) )
      = ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( k2_enumset1 @ X30 @ X30 @ X31 @ X32 )
      = ( k1_enumset1 @ X30 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('22',plain,
    ( ( k1_enumset1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k1_tarski @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','20','21'])).

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

thf('23',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 )
      | ( r2_hidden @ X7 @ X11 )
      | ( X11
       != ( k1_enumset1 @ X10 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('24',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X7 @ ( k1_enumset1 @ X10 @ X9 @ X8 ) )
      | ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k1_tarski @ sk_C_1 ) )
      | ( zip_tseitin_0 @ X0 @ sk_C_1 @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X3 != X2 )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X5 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('27',plain,(
    ! [X2: $i,X4: $i,X5: $i] :
      ~ ( zip_tseitin_0 @ X2 @ X4 @ X5 @ X2 ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    r2_hidden @ sk_A @ ( k1_tarski @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('29',plain,(
    ! [X14: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X17 @ X16 )
      | ( X17 = X14 )
      | ( X16
       != ( k1_tarski @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('30',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17 = X14 )
      | ~ ( r2_hidden @ X17 @ ( k1_tarski @ X14 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    sk_A = sk_C_1 ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gvFFgiwGJ6
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:34:48 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.58/0.80  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.80  % Solved by: fo/fo7.sh
% 0.58/0.80  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.80  % done 479 iterations in 0.353s
% 0.58/0.80  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.80  % SZS output start Refutation
% 0.58/0.80  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.80  thf(k5_enumset1_type, type, k5_enumset1: $i > $i > $i > $i > $i > $i > $i > $i).
% 0.58/0.80  thf(k3_enumset1_type, type, k3_enumset1: $i > $i > $i > $i > $i > $i).
% 0.58/0.80  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.58/0.80  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.58/0.80  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.58/0.80  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.58/0.80  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.80  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.58/0.80  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.80  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.58/0.80  thf(k6_enumset1_type, type, k6_enumset1: $i > $i > $i > $i > $i > $i > $i > 
% 0.58/0.80                                           $i > $i).
% 0.58/0.80  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.80  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.58/0.80  thf(k4_enumset1_type, type, k4_enumset1: $i > $i > $i > $i > $i > $i > $i).
% 0.58/0.80  thf(t26_zfmisc_1, conjecture,
% 0.58/0.80    (![A:$i,B:$i,C:$i]:
% 0.58/0.80     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.58/0.80       ( ( A ) = ( C ) ) ))).
% 0.58/0.80  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.80    (~( ![A:$i,B:$i,C:$i]:
% 0.58/0.80        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.58/0.80          ( ( A ) = ( C ) ) ) )),
% 0.58/0.80    inference('cnf.neg', [status(esa)], [t26_zfmisc_1])).
% 0.58/0.80  thf('0', plain,
% 0.58/0.80      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C_1))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf(t12_xboole_1, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.58/0.80  thf('1', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         (((k2_xboole_0 @ X1 @ X0) = (X0)) | ~ (r1_tarski @ X1 @ X0))),
% 0.58/0.80      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.58/0.80  thf('2', plain,
% 0.58/0.80      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ (k1_tarski @ sk_C_1))
% 0.58/0.80         = (k1_tarski @ sk_C_1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['0', '1'])).
% 0.58/0.80  thf(t71_enumset1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i]:
% 0.58/0.80     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.58/0.80  thf('3', plain,
% 0.58/0.80      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.58/0.80         ((k2_enumset1 @ X30 @ X30 @ X31 @ X32)
% 0.58/0.80           = (k1_enumset1 @ X30 @ X31 @ X32))),
% 0.58/0.80      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.58/0.80  thf(t70_enumset1, axiom,
% 0.58/0.80    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.58/0.80  thf('4', plain,
% 0.58/0.80      (![X28 : $i, X29 : $i]:
% 0.58/0.80         ((k1_enumset1 @ X28 @ X28 @ X29) = (k2_tarski @ X28 @ X29))),
% 0.58/0.80      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.58/0.80  thf('5', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i]:
% 0.58/0.80         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['3', '4'])).
% 0.58/0.80  thf(t74_enumset1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.58/0.80     ( ( k5_enumset1 @ A @ A @ B @ C @ D @ E @ F ) =
% 0.58/0.80       ( k4_enumset1 @ A @ B @ C @ D @ E @ F ) ))).
% 0.58/0.80  thf('6', plain,
% 0.58/0.80      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.58/0.80         ((k5_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47)
% 0.58/0.80           = (k4_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47))),
% 0.58/0.80      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.58/0.80  thf(t68_enumset1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i,H:$i]:
% 0.58/0.80     ( ( k6_enumset1 @ A @ B @ C @ D @ E @ F @ G @ H ) =
% 0.58/0.80       ( k2_xboole_0 @
% 0.58/0.80         ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) @ ( k1_tarski @ H ) ) ))).
% 0.58/0.80  thf('7', plain,
% 0.58/0.80      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i, X25 : $i, 
% 0.58/0.80         X26 : $i]:
% 0.58/0.80         ((k6_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25 @ X26)
% 0.58/0.80           = (k2_xboole_0 @ 
% 0.58/0.80              (k5_enumset1 @ X19 @ X20 @ X21 @ X22 @ X23 @ X24 @ X25) @ 
% 0.58/0.80              (k1_tarski @ X26)))),
% 0.58/0.80      inference('cnf', [status(esa)], [t68_enumset1])).
% 0.58/0.80  thf('8', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.58/0.80         ((k6_enumset1 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0 @ X6)
% 0.58/0.80           = (k2_xboole_0 @ (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0) @ 
% 0.58/0.80              (k1_tarski @ X6)))),
% 0.58/0.80      inference('sup+', [status(thm)], ['6', '7'])).
% 0.58/0.80  thf(t75_enumset1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.58/0.80     ( ( k6_enumset1 @ A @ A @ B @ C @ D @ E @ F @ G ) =
% 0.58/0.80       ( k5_enumset1 @ A @ B @ C @ D @ E @ F @ G ) ))).
% 0.58/0.80  thf('9', plain,
% 0.58/0.80      (![X48 : $i, X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.58/0.80         ((k6_enumset1 @ X48 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54)
% 0.58/0.80           = (k5_enumset1 @ X48 @ X49 @ X50 @ X51 @ X52 @ X53 @ X54))),
% 0.58/0.80      inference('cnf', [status(esa)], [t75_enumset1])).
% 0.58/0.80  thf('10', plain,
% 0.58/0.80      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.58/0.80         ((k5_enumset1 @ X42 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47)
% 0.58/0.80           = (k4_enumset1 @ X42 @ X43 @ X44 @ X45 @ X46 @ X47))),
% 0.58/0.80      inference('cnf', [status(esa)], [t74_enumset1])).
% 0.58/0.80  thf('11', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.80         ((k6_enumset1 @ X5 @ X5 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.58/0.80           = (k4_enumset1 @ X5 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['9', '10'])).
% 0.58/0.80  thf(t73_enumset1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.58/0.80     ( ( k4_enumset1 @ A @ A @ B @ C @ D @ E ) =
% 0.58/0.80       ( k3_enumset1 @ A @ B @ C @ D @ E ) ))).
% 0.58/0.80  thf('12', plain,
% 0.58/0.80      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.58/0.80         ((k4_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41)
% 0.58/0.80           = (k3_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41))),
% 0.58/0.80      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.58/0.80  thf('13', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.80         ((k6_enumset1 @ X4 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1 @ X0)
% 0.58/0.80           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['11', '12'])).
% 0.58/0.80  thf('14', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ (k4_enumset1 @ X4 @ X4 @ X4 @ X3 @ X2 @ X1) @ 
% 0.58/0.80           (k1_tarski @ X0)) = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.58/0.80      inference('sup+', [status(thm)], ['8', '13'])).
% 0.58/0.80  thf('15', plain,
% 0.58/0.80      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.58/0.80         ((k4_enumset1 @ X37 @ X37 @ X38 @ X39 @ X40 @ X41)
% 0.58/0.80           = (k3_enumset1 @ X37 @ X38 @ X39 @ X40 @ X41))),
% 0.58/0.80      inference('cnf', [status(esa)], [t73_enumset1])).
% 0.58/0.80  thf(t72_enumset1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.80     ( ( k3_enumset1 @ A @ A @ B @ C @ D ) = ( k2_enumset1 @ A @ B @ C @ D ) ))).
% 0.58/0.80  thf('16', plain,
% 0.58/0.80      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.58/0.80         ((k3_enumset1 @ X33 @ X33 @ X34 @ X35 @ X36)
% 0.58/0.80           = (k2_enumset1 @ X33 @ X34 @ X35 @ X36))),
% 0.58/0.80      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.58/0.80  thf('17', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ (k2_enumset1 @ X4 @ X3 @ X2 @ X1) @ (k1_tarski @ X0))
% 0.58/0.80           = (k3_enumset1 @ X4 @ X3 @ X2 @ X1 @ X0))),
% 0.58/0.80      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.58/0.80  thf('18', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 0.58/0.80           = (k3_enumset1 @ X1 @ X1 @ X1 @ X0 @ X2))),
% 0.58/0.80      inference('sup+', [status(thm)], ['5', '17'])).
% 0.58/0.80  thf('19', plain,
% 0.58/0.80      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.58/0.80         ((k3_enumset1 @ X33 @ X33 @ X34 @ X35 @ X36)
% 0.58/0.80           = (k2_enumset1 @ X33 @ X34 @ X35 @ X36))),
% 0.58/0.80      inference('cnf', [status(esa)], [t72_enumset1])).
% 0.58/0.80  thf('20', plain,
% 0.58/0.80      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.80         ((k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2))
% 0.58/0.80           = (k2_enumset1 @ X1 @ X1 @ X0 @ X2))),
% 0.58/0.80      inference('demod', [status(thm)], ['18', '19'])).
% 0.58/0.80  thf('21', plain,
% 0.58/0.80      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.58/0.80         ((k2_enumset1 @ X30 @ X30 @ X31 @ X32)
% 0.58/0.80           = (k1_enumset1 @ X30 @ X31 @ X32))),
% 0.58/0.80      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.58/0.80  thf('22', plain,
% 0.58/0.80      (((k1_enumset1 @ sk_A @ sk_B @ sk_C_1) = (k1_tarski @ sk_C_1))),
% 0.58/0.80      inference('demod', [status(thm)], ['2', '20', '21'])).
% 0.58/0.80  thf(d1_enumset1, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.80     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.58/0.80       ( ![E:$i]:
% 0.58/0.80         ( ( r2_hidden @ E @ D ) <=>
% 0.58/0.80           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.58/0.80  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.58/0.80  thf(zf_stmt_2, axiom,
% 0.58/0.80    (![E:$i,C:$i,B:$i,A:$i]:
% 0.58/0.80     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.58/0.80       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.58/0.80  thf(zf_stmt_3, axiom,
% 0.58/0.80    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.80     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.58/0.80       ( ![E:$i]:
% 0.58/0.80         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.58/0.80  thf('23', plain,
% 0.58/0.80      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.58/0.80         ((zip_tseitin_0 @ X7 @ X8 @ X9 @ X10)
% 0.58/0.80          | (r2_hidden @ X7 @ X11)
% 0.58/0.80          | ((X11) != (k1_enumset1 @ X10 @ X9 @ X8)))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.80  thf('24', plain,
% 0.58/0.80      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.58/0.80         ((r2_hidden @ X7 @ (k1_enumset1 @ X10 @ X9 @ X8))
% 0.58/0.80          | (zip_tseitin_0 @ X7 @ X8 @ X9 @ X10))),
% 0.58/0.80      inference('simplify', [status(thm)], ['23'])).
% 0.58/0.80  thf('25', plain,
% 0.58/0.80      (![X0 : $i]:
% 0.58/0.80         ((r2_hidden @ X0 @ (k1_tarski @ sk_C_1))
% 0.58/0.80          | (zip_tseitin_0 @ X0 @ sk_C_1 @ sk_B @ sk_A))),
% 0.58/0.80      inference('sup+', [status(thm)], ['22', '24'])).
% 0.58/0.80  thf('26', plain,
% 0.58/0.80      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.80         (((X3) != (X2)) | ~ (zip_tseitin_0 @ X3 @ X4 @ X5 @ X2))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.80  thf('27', plain,
% 0.58/0.80      (![X2 : $i, X4 : $i, X5 : $i]: ~ (zip_tseitin_0 @ X2 @ X4 @ X5 @ X2)),
% 0.58/0.80      inference('simplify', [status(thm)], ['26'])).
% 0.58/0.80  thf('28', plain, ((r2_hidden @ sk_A @ (k1_tarski @ sk_C_1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['25', '27'])).
% 0.58/0.80  thf(d1_tarski, axiom,
% 0.58/0.80    (![A:$i,B:$i]:
% 0.58/0.80     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.58/0.80       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.58/0.80  thf('29', plain,
% 0.58/0.80      (![X14 : $i, X16 : $i, X17 : $i]:
% 0.58/0.80         (~ (r2_hidden @ X17 @ X16)
% 0.58/0.80          | ((X17) = (X14))
% 0.58/0.80          | ((X16) != (k1_tarski @ X14)))),
% 0.58/0.80      inference('cnf', [status(esa)], [d1_tarski])).
% 0.58/0.80  thf('30', plain,
% 0.58/0.80      (![X14 : $i, X17 : $i]:
% 0.58/0.80         (((X17) = (X14)) | ~ (r2_hidden @ X17 @ (k1_tarski @ X14)))),
% 0.58/0.80      inference('simplify', [status(thm)], ['29'])).
% 0.58/0.80  thf('31', plain, (((sk_A) = (sk_C_1))),
% 0.58/0.80      inference('sup-', [status(thm)], ['28', '30'])).
% 0.58/0.80  thf('32', plain, (((sk_A) != (sk_C_1))),
% 0.58/0.80      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.80  thf('33', plain, ($false),
% 0.58/0.80      inference('simplify_reflect-', [status(thm)], ['31', '32'])).
% 0.58/0.80  
% 0.58/0.80  % SZS output end Refutation
% 0.58/0.80  
% 0.58/0.81  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
