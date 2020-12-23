%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.axfibGCMLs

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:47 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   67 (  91 expanded)
%              Number of leaves         :   27 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  458 ( 643 expanded)
%              Number of equality atoms :   58 (  77 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('0',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( k2_enumset1 @ X28 @ X28 @ X29 @ X30 )
      = ( k1_enumset1 @ X28 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t46_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( k2_enumset1 @ X21 @ X22 @ X23 @ X24 )
      = ( k2_xboole_0 @ ( k1_enumset1 @ X21 @ X22 @ X23 ) @ ( k1_tarski @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t46_enumset1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X0 @ X2 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X0 ) @ ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k2_tarski @ X1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('7',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X1 @ X0 )
      = ( k2_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X37: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('10',plain,(
    ! [X35: $i,X36: $i] :
      ( ( X35 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X35 @ X36 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X35 ) @ ( k1_setfam_1 @ X36 ) ) )
      | ( X36 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ X1 @ ( k1_tarski @ X0 ) ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X1 ) @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ ( k1_tarski @ X1 ) ) @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X37: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X37 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X1 )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('15',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k3_xboole_0 @ sk_A @ sk_B )
     != ( k3_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X25: $i] :
      ( ( k2_tarski @ X25 @ X25 )
      = ( k1_tarski @ X25 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('19',plain,(
    ! [X26: $i,X27: $i] :
      ( ( k1_enumset1 @ X26 @ X26 @ X27 )
      = ( k2_tarski @ X26 @ X27 ) ) ),
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

thf('20',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X14 @ X18 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ~ ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X9 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_B @ k1_xboole_0 )
    | ( ( k1_tarski @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','26'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('28',plain,(
    ! [X3: $i] :
      ( ( k3_xboole_0 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('29',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['30'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('32',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X31 ) @ X32 )
      | ~ ( r2_hidden @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['27','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','25'])).

thf('36',plain,(
    r2_hidden @ sk_A @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('38',plain,(
    $false ),
    inference('sup-',[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.axfibGCMLs
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:22:33 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.40/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.61  % Solved by: fo/fo7.sh
% 0.40/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.61  % done 259 iterations in 0.153s
% 0.40/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.61  % SZS output start Refutation
% 0.40/0.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.40/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.61  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.40/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.40/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.40/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.61  thf(t71_enumset1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.40/0.61  thf('0', plain,
% 0.40/0.61      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.40/0.61         ((k2_enumset1 @ X28 @ X28 @ X29 @ X30)
% 0.40/0.61           = (k1_enumset1 @ X28 @ X29 @ X30))),
% 0.40/0.61      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.40/0.61  thf(t70_enumset1, axiom,
% 0.40/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.40/0.61  thf('1', plain,
% 0.40/0.61      (![X26 : $i, X27 : $i]:
% 0.40/0.61         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 0.40/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.61  thf('2', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['0', '1'])).
% 0.40/0.61  thf('3', plain,
% 0.40/0.61      (![X26 : $i, X27 : $i]:
% 0.40/0.61         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 0.40/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.61  thf(t46_enumset1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.61     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.40/0.61       ( k2_xboole_0 @ ( k1_enumset1 @ A @ B @ C ) @ ( k1_tarski @ D ) ) ))).
% 0.40/0.61  thf('4', plain,
% 0.40/0.61      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.40/0.61         ((k2_enumset1 @ X21 @ X22 @ X23 @ X24)
% 0.40/0.61           = (k2_xboole_0 @ (k1_enumset1 @ X21 @ X22 @ X23) @ (k1_tarski @ X24)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t46_enumset1])).
% 0.40/0.61  thf('5', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         ((k2_enumset1 @ X1 @ X1 @ X0 @ X2)
% 0.40/0.61           = (k2_xboole_0 @ (k2_tarski @ X1 @ X0) @ (k1_tarski @ X2)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['3', '4'])).
% 0.40/0.61  thf('6', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((k2_tarski @ X1 @ X0)
% 0.40/0.61           = (k2_xboole_0 @ (k2_tarski @ X1 @ X1) @ (k1_tarski @ X0)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['2', '5'])).
% 0.40/0.61  thf(t69_enumset1, axiom,
% 0.40/0.61    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.40/0.61  thf('7', plain, (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.40/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.61  thf('8', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((k2_tarski @ X1 @ X0)
% 0.40/0.61           = (k2_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.40/0.61      inference('demod', [status(thm)], ['6', '7'])).
% 0.40/0.61  thf(t11_setfam_1, axiom,
% 0.40/0.61    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.40/0.61  thf('9', plain, (![X37 : $i]: ((k1_setfam_1 @ (k1_tarski @ X37)) = (X37))),
% 0.40/0.61      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.40/0.61  thf(t10_setfam_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.40/0.61          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.40/0.61            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.40/0.61  thf('10', plain,
% 0.40/0.61      (![X35 : $i, X36 : $i]:
% 0.40/0.61         (((X35) = (k1_xboole_0))
% 0.40/0.61          | ((k1_setfam_1 @ (k2_xboole_0 @ X35 @ X36))
% 0.40/0.61              = (k3_xboole_0 @ (k1_setfam_1 @ X35) @ (k1_setfam_1 @ X36)))
% 0.40/0.61          | ((X36) = (k1_xboole_0)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.40/0.61  thf('11', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (((k1_setfam_1 @ (k2_xboole_0 @ X1 @ (k1_tarski @ X0)))
% 0.40/0.61            = (k3_xboole_0 @ (k1_setfam_1 @ X1) @ X0))
% 0.40/0.61          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.40/0.61          | ((X1) = (k1_xboole_0)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['9', '10'])).
% 0.40/0.61  thf('12', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.40/0.61            = (k3_xboole_0 @ (k1_setfam_1 @ (k1_tarski @ X1)) @ X0))
% 0.40/0.61          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.40/0.61          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['8', '11'])).
% 0.40/0.61  thf('13', plain, (![X37 : $i]: ((k1_setfam_1 @ (k1_tarski @ X37)) = (X37))),
% 0.40/0.61      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.40/0.61  thf('14', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.40/0.61          | ((k1_tarski @ X1) = (k1_xboole_0))
% 0.40/0.61          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.40/0.61      inference('demod', [status(thm)], ['12', '13'])).
% 0.40/0.61  thf(t12_setfam_1, conjecture,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.40/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.61    (~( ![A:$i,B:$i]:
% 0.40/0.61        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.40/0.61    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.40/0.61  thf('15', plain,
% 0.40/0.61      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.40/0.61         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('16', plain,
% 0.40/0.61      ((((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))
% 0.40/0.61        | ((k1_tarski @ sk_B) = (k1_xboole_0))
% 0.40/0.61        | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.61  thf('17', plain,
% 0.40/0.61      ((((k1_tarski @ sk_A) = (k1_xboole_0))
% 0.40/0.61        | ((k1_tarski @ sk_B) = (k1_xboole_0)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['16'])).
% 0.40/0.61  thf('18', plain,
% 0.40/0.61      (![X25 : $i]: ((k2_tarski @ X25 @ X25) = (k1_tarski @ X25))),
% 0.40/0.61      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.40/0.61  thf('19', plain,
% 0.40/0.61      (![X26 : $i, X27 : $i]:
% 0.40/0.61         ((k1_enumset1 @ X26 @ X26 @ X27) = (k2_tarski @ X26 @ X27))),
% 0.40/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.40/0.61  thf(d1_enumset1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.40/0.61       ( ![E:$i]:
% 0.40/0.61         ( ( r2_hidden @ E @ D ) <=>
% 0.40/0.61           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.40/0.61  thf(zf_stmt_2, axiom,
% 0.40/0.61    (![E:$i,C:$i,B:$i,A:$i]:
% 0.40/0.61     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.40/0.61       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_3, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.40/0.61       ( ![E:$i]:
% 0.40/0.61         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.40/0.61  thf('20', plain,
% 0.40/0.61      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.40/0.61         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 0.40/0.61          | (r2_hidden @ X14 @ X18)
% 0.40/0.61          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.40/0.61  thf('21', plain,
% 0.40/0.61      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.40/0.61         ((r2_hidden @ X14 @ (k1_enumset1 @ X17 @ X16 @ X15))
% 0.40/0.61          | (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17))),
% 0.40/0.61      inference('simplify', [status(thm)], ['20'])).
% 0.40/0.61  thf('22', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.61         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.40/0.61          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.40/0.61      inference('sup+', [status(thm)], ['19', '21'])).
% 0.40/0.61  thf('23', plain,
% 0.40/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.40/0.61         (((X10) != (X9)) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.40/0.61  thf('24', plain,
% 0.40/0.61      (![X9 : $i, X11 : $i, X12 : $i]: ~ (zip_tseitin_0 @ X9 @ X11 @ X12 @ X9)),
% 0.40/0.61      inference('simplify', [status(thm)], ['23'])).
% 0.40/0.61  thf('25', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.40/0.61      inference('sup-', [status(thm)], ['22', '24'])).
% 0.40/0.61  thf('26', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['18', '25'])).
% 0.40/0.61  thf('27', plain,
% 0.40/0.61      (((r2_hidden @ sk_B @ k1_xboole_0) | ((k1_tarski @ sk_A) = (k1_xboole_0)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['17', '26'])).
% 0.40/0.61  thf(t2_boole, axiom,
% 0.40/0.61    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.40/0.61  thf('28', plain,
% 0.40/0.61      (![X3 : $i]: ((k3_xboole_0 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [t2_boole])).
% 0.40/0.61  thf(d7_xboole_0, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.40/0.61       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.40/0.61  thf('29', plain,
% 0.40/0.61      (![X0 : $i, X2 : $i]:
% 0.40/0.61         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.40/0.61  thf('30', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['28', '29'])).
% 0.40/0.61  thf('31', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.40/0.61      inference('simplify', [status(thm)], ['30'])).
% 0.40/0.61  thf(l24_zfmisc_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.40/0.61  thf('32', plain,
% 0.40/0.61      (![X31 : $i, X32 : $i]:
% 0.40/0.61         (~ (r1_xboole_0 @ (k1_tarski @ X31) @ X32) | ~ (r2_hidden @ X31 @ X32))),
% 0.40/0.61      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.40/0.61  thf('33', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.40/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.61  thf('34', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.40/0.61      inference('clc', [status(thm)], ['27', '33'])).
% 0.40/0.61  thf('35', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['18', '25'])).
% 0.40/0.61  thf('36', plain, ((r2_hidden @ sk_A @ k1_xboole_0)),
% 0.40/0.61      inference('sup+', [status(thm)], ['34', '35'])).
% 0.40/0.61  thf('37', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.40/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.40/0.61  thf('38', plain, ($false), inference('sup-', [status(thm)], ['36', '37'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
