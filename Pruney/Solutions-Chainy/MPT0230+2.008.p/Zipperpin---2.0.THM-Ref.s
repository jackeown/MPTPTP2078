%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1PNroNhndf

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   65 (  71 expanded)
%              Number of leaves         :   30 (  34 expanded)
%              Depth                    :   14
%              Number of atoms          :  452 ( 528 expanded)
%              Number of equality atoms :   54 (  66 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ( X11 = X12 )
      | ( X11 = X13 )
      | ( X11 = X14 ) ) ),
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
    r1_tarski @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k3_xboole_0 @ X4 @ X5 )
        = X4 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('5',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k5_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('6',plain,(
    ! [X7: $i] :
      ( ( k5_xboole_0 @ X7 @ X7 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('7',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['5','6'])).

thf(t98_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ X8 @ ( k4_xboole_0 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t98_xboole_1])).

thf('9',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_A ) )
    = ( k5_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('11',plain,(
    ! [X6: $i] :
      ( ( k5_xboole_0 @ X6 @ k1_xboole_0 )
      = X6 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('12',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('13',plain,(
    ! [X34: $i] :
      ( ( k2_tarski @ X34 @ X34 )
      = ( k1_tarski @ X34 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l53_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( k2_enumset1 @ A @ B @ C @ D )
      = ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ) )).

thf('14',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( k2_enumset1 @ X22 @ X23 @ X24 @ X25 )
      = ( k2_xboole_0 @ ( k2_tarski @ X22 @ X23 ) @ ( k2_tarski @ X24 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[l53_enumset1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X2 @ X1 )
      = ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X2 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('16',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( k2_enumset1 @ X37 @ X37 @ X38 @ X39 )
      = ( k1_enumset1 @ X37 @ X38 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('17',plain,
    ( ( k1_enumset1 @ sk_A @ sk_B @ sk_C )
    = ( k2_tarski @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['12','15','16'])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 )
      | ( r2_hidden @ X15 @ X19 )
      | ( X19
       != ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X15 @ ( k1_enumset1 @ X18 @ X17 @ X16 ) )
      | ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_C ) )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup+',[status(thm)],['17','19'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k1_enumset1 @ X35 @ X35 @ X36 )
      = ( k2_tarski @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('22',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X20 @ X19 )
      | ~ ( zip_tseitin_0 @ X20 @ X16 @ X17 @ X18 )
      | ( X19
       != ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,(
    ! [X16: $i,X17: $i,X18: $i,X20: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X16 @ X17 @ X18 )
      | ~ ( r2_hidden @ X20 @ ( k1_enumset1 @ X18 @ X17 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A )
      | ~ ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_B )
      | ( X0 = sk_B )
      | ( X0 = sk_C )
      | ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A )
      | ( X0 = sk_C )
      | ( X0 = sk_B ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X11 != X10 )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X10: $i,X12: $i,X13: $i] :
      ~ ( zip_tseitin_0 @ X10 @ X12 @ X13 @ X10 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( sk_A = sk_B )
    | ( sk_A = sk_C ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    sk_A != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('32',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','31','32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1PNroNhndf
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:03:23 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 138 iterations in 0.059s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(d1_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.51       ( ![E:$i]:
% 0.22/0.51         ( ( r2_hidden @ E @ D ) <=>
% 0.22/0.51           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, axiom,
% 0.22/0.51    (![E:$i,C:$i,B:$i,A:$i]:
% 0.22/0.51     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.22/0.51       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.22/0.51  thf('0', plain,
% 0.22/0.51      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.51         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 0.22/0.51          | ((X11) = (X12))
% 0.22/0.51          | ((X11) = (X13))
% 0.22/0.51          | ((X11) = (X14)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(t25_zfmisc_1, conjecture,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.22/0.51          ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_1, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.51        ( ~( ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ B @ C ) ) & 
% 0.22/0.51             ( ( A ) != ( B ) ) & ( ( A ) != ( C ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t25_zfmisc_1])).
% 0.22/0.51  thf('1', plain,
% 0.22/0.51      ((r1_tarski @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.51  thf(t28_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X4 : $i, X5 : $i]:
% 0.22/0.51         (((k3_xboole_0 @ X4 @ X5) = (X4)) | ~ (r1_tarski @ X4 @ X5))),
% 0.22/0.51      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.22/0.51         = (k1_tarski @ sk_A))),
% 0.22/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf(t100_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X2 : $i, X3 : $i]:
% 0.22/0.51         ((k4_xboole_0 @ X2 @ X3)
% 0.22/0.51           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.22/0.51         = (k5_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_A)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['3', '4'])).
% 0.22/0.51  thf(t92_xboole_1, axiom,
% 0.22/0.51    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 0.22/0.51  thf('6', plain, (![X7 : $i]: ((k5_xboole_0 @ X7 @ X7) = (k1_xboole_0))),
% 0.22/0.51      inference('cnf', [status(esa)], [t92_xboole_1])).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.22/0.51         = (k1_xboole_0))),
% 0.22/0.51      inference('demod', [status(thm)], ['5', '6'])).
% 0.22/0.51  thf(t98_xboole_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( k2_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) ))).
% 0.22/0.51  thf('8', plain,
% 0.22/0.51      (![X8 : $i, X9 : $i]:
% 0.22/0.51         ((k2_xboole_0 @ X8 @ X9)
% 0.22/0.51           = (k5_xboole_0 @ X8 @ (k4_xboole_0 @ X9 @ X8)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t98_xboole_1])).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (((k2_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_A))
% 0.22/0.51         = (k5_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ k1_xboole_0))),
% 0.22/0.51      inference('sup+', [status(thm)], ['7', '8'])).
% 0.22/0.51  thf(commutativity_k2_xboole_0, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.22/0.51      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.22/0.51  thf(t5_boole, axiom,
% 0.22/0.51    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.51  thf('11', plain, (![X6 : $i]: ((k5_xboole_0 @ X6 @ k1_xboole_0) = (X6))),
% 0.22/0.51      inference('cnf', [status(esa)], [t5_boole])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ (k2_tarski @ sk_B @ sk_C))
% 0.22/0.51         = (k2_tarski @ sk_B @ sk_C))),
% 0.22/0.51      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.22/0.51  thf(t69_enumset1, axiom,
% 0.22/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.51  thf('13', plain,
% 0.22/0.51      (![X34 : $i]: ((k2_tarski @ X34 @ X34) = (k1_tarski @ X34))),
% 0.22/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.51  thf(l53_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( k2_enumset1 @ A @ B @ C @ D ) =
% 0.22/0.51       ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k2_tarski @ C @ D ) ) ))).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.51         ((k2_enumset1 @ X22 @ X23 @ X24 @ X25)
% 0.22/0.51           = (k2_xboole_0 @ (k2_tarski @ X22 @ X23) @ (k2_tarski @ X24 @ X25)))),
% 0.22/0.51      inference('cnf', [status(esa)], [l53_enumset1])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((k2_enumset1 @ X0 @ X0 @ X2 @ X1)
% 0.22/0.51           = (k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X2 @ X1)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['13', '14'])).
% 0.22/0.51  thf(t71_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 0.22/0.51  thf('16', plain,
% 0.22/0.51      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.22/0.51         ((k2_enumset1 @ X37 @ X37 @ X38 @ X39)
% 0.22/0.51           = (k1_enumset1 @ X37 @ X38 @ X39))),
% 0.22/0.51      inference('cnf', [status(esa)], [t71_enumset1])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (((k1_enumset1 @ sk_A @ sk_B @ sk_C) = (k2_tarski @ sk_B @ sk_C))),
% 0.22/0.51      inference('demod', [status(thm)], ['12', '15', '16'])).
% 0.22/0.51  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.51  thf(zf_stmt_3, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.22/0.51       ( ![E:$i]:
% 0.22/0.51         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.51         ((zip_tseitin_0 @ X15 @ X16 @ X17 @ X18)
% 0.22/0.51          | (r2_hidden @ X15 @ X19)
% 0.22/0.51          | ((X19) != (k1_enumset1 @ X18 @ X17 @ X16)))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.51         ((r2_hidden @ X15 @ (k1_enumset1 @ X18 @ X17 @ X16))
% 0.22/0.51          | (zip_tseitin_0 @ X15 @ X16 @ X17 @ X18))),
% 0.22/0.51      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_C))
% 0.22/0.51          | (zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A))),
% 0.22/0.51      inference('sup+', [status(thm)], ['17', '19'])).
% 0.22/0.51  thf(t70_enumset1, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X35 : $i, X36 : $i]:
% 0.22/0.52         ((k1_enumset1 @ X35 @ X35 @ X36) = (k2_tarski @ X35 @ X36))),
% 0.22/0.52      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X20 @ X19)
% 0.22/0.52          | ~ (zip_tseitin_0 @ X20 @ X16 @ X17 @ X18)
% 0.22/0.52          | ((X19) != (k1_enumset1 @ X18 @ X17 @ X16)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X16 : $i, X17 : $i, X18 : $i, X20 : $i]:
% 0.22/0.52         (~ (zip_tseitin_0 @ X20 @ X16 @ X17 @ X18)
% 0.22/0.52          | ~ (r2_hidden @ X20 @ (k1_enumset1 @ X18 @ X17 @ X16)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['22'])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.22/0.52          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['21', '23'])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A)
% 0.22/0.52          | ~ (zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['20', '24'])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((X0) = (sk_B))
% 0.22/0.52          | ((X0) = (sk_B))
% 0.22/0.52          | ((X0) = (sk_C))
% 0.22/0.52          | (zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '25'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((zip_tseitin_0 @ X0 @ sk_C @ sk_B @ sk_A)
% 0.22/0.52          | ((X0) = (sk_C))
% 0.22/0.52          | ((X0) = (sk_B)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['26'])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.52         (((X11) != (X10)) | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X10 : $i, X12 : $i, X13 : $i]:
% 0.22/0.52         ~ (zip_tseitin_0 @ X10 @ X12 @ X13 @ X10)),
% 0.22/0.52      inference('simplify', [status(thm)], ['28'])).
% 0.22/0.52  thf('30', plain, ((((sk_A) = (sk_B)) | ((sk_A) = (sk_C)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['27', '29'])).
% 0.22/0.52  thf('31', plain, (((sk_A) != (sk_C))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.52  thf('32', plain, (((sk_A) != (sk_B))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.22/0.52  thf('33', plain, ($false),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['30', '31', '32'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
