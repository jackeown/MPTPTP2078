%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uf7Rf32qEK

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   57 (  67 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :  378 ( 467 expanded)
%              Number of equality atoms :   36 (  46 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t63_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        = ( k2_tarski @ A @ B ) )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k2_tarski @ A @ B ) )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t63_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k1_enumset1 @ X24 @ X24 @ X25 )
      = ( k2_tarski @ X24 @ X25 ) ) ),
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

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 )
      | ( r2_hidden @ X17 @ X21 )
      | ( X21
       != ( k1_enumset1 @ X20 @ X19 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ ( k1_enumset1 @ X20 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ X17 @ X18 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X13 != X14 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    ! [X12: $i,X14: $i,X15: $i] :
      ~ ( zip_tseitin_0 @ X14 @ X14 @ X15 @ X12 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf('11',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_B @ sk_A ) @ sk_C_1 )
    = ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t95_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X8 @ X9 ) @ ( k2_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t95_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('15',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X10: $i,X11: $i] :
      ( ( k2_tarski @ X11 @ X10 )
      = ( k2_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X51 @ X52 ) )
      = ( k2_xboole_0 @ X51 @ X52 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k3_xboole_0 @ X8 @ X9 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X8 @ X9 ) @ ( k5_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ ( k5_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ X1 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','23'])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_B @ sk_A ) )
    = ( k2_tarski @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['11','24'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('26',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_B @ sk_A ) )
      | ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sup-',[status(thm)],['7','29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uf7Rf32qEK
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 134 iterations in 0.058s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.51  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.51  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.51  thf(t63_zfmisc_1, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.21/0.51       ( r2_hidden @ A @ C ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.51        ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k2_tarski @ A @ B ) ) =>
% 0.21/0.51          ( r2_hidden @ A @ C ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t63_zfmisc_1])).
% 0.21/0.51  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C_1)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t70_enumset1, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X24 : $i, X25 : $i]:
% 0.21/0.51         ((k1_enumset1 @ X24 @ X24 @ X25) = (k2_tarski @ X24 @ X25))),
% 0.21/0.51      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.51  thf(d1_enumset1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.51       ( ![E:$i]:
% 0.21/0.51         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.51           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.51  thf(zf_stmt_2, axiom,
% 0.21/0.51    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.51     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.51       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_3, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.51       ( ![E:$i]:
% 0.21/0.51         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.51         ((zip_tseitin_0 @ X17 @ X18 @ X19 @ X20)
% 0.21/0.51          | (r2_hidden @ X17 @ X21)
% 0.21/0.51          | ((X21) != (k1_enumset1 @ X20 @ X19 @ X18)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 0.21/0.51         ((r2_hidden @ X17 @ (k1_enumset1 @ X20 @ X19 @ X18))
% 0.21/0.51          | (zip_tseitin_0 @ X17 @ X18 @ X19 @ X20))),
% 0.21/0.51      inference('simplify', [status(thm)], ['2'])).
% 0.21/0.51  thf('4', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.51          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['1', '3'])).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         (((X13) != (X14)) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X12 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         ~ (zip_tseitin_0 @ X14 @ X14 @ X15 @ X12)),
% 0.21/0.51      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)
% 0.21/0.51         = (k2_tarski @ sk_A @ sk_B))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(commutativity_k2_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (((k3_xboole_0 @ (k2_tarski @ sk_B @ sk_A) @ sk_C_1)
% 0.21/0.51         = (k2_tarski @ sk_B @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.21/0.51  thf(commutativity_k5_xboole_0, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.51  thf(t95_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k3_xboole_0 @ A @ B ) =
% 0.21/0.51       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k2_xboole_0 @ A @ B ) ) ))).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         ((k3_xboole_0 @ X8 @ X9)
% 0.21/0.51           = (k5_xboole_0 @ (k5_xboole_0 @ X8 @ X9) @ (k2_xboole_0 @ X8 @ X9)))),
% 0.21/0.51      inference('cnf', [status(esa)], [t95_xboole_1])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         ((k3_xboole_0 @ X8 @ X9)
% 0.21/0.51           = (k5_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ (k5_xboole_0 @ X8 @ X9)))),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k3_xboole_0 @ X0 @ X1)
% 0.21/0.51           = (k5_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ (k5_xboole_0 @ X1 @ X0)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['12', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         ((k2_tarski @ X11 @ X10) = (k2_tarski @ X10 @ X11))),
% 0.21/0.51      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.51  thf(l51_zfmisc_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X51 : $i, X52 : $i]:
% 0.21/0.51         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.21/0.51      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X51 : $i, X52 : $i]:
% 0.21/0.51         ((k3_tarski @ (k2_tarski @ X51 @ X52)) = (k2_xboole_0 @ X51 @ X52))),
% 0.21/0.51      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.21/0.51      inference('sup+', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         ((k3_xboole_0 @ X8 @ X9)
% 0.21/0.51           = (k5_xboole_0 @ (k2_xboole_0 @ X8 @ X9) @ (k5_xboole_0 @ X8 @ X9)))),
% 0.21/0.51      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((k3_xboole_0 @ X0 @ X1)
% 0.21/0.51           = (k5_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ (k5_xboole_0 @ X0 @ X1)))),
% 0.21/0.51      inference('sup+', [status(thm)], ['21', '22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X0 @ X1) = (k3_xboole_0 @ X1 @ X0))),
% 0.21/0.51      inference('sup+', [status(thm)], ['16', '23'])).
% 0.21/0.51  thf('25', plain,
% 0.21/0.51      (((k3_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_B @ sk_A))
% 0.21/0.51         = (k2_tarski @ sk_B @ sk_A))),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '24'])).
% 0.21/0.51  thf(t17_xboole_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 0.21/0.51      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.21/0.51  thf(d3_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X2 @ X3)
% 0.21/0.51          | (r2_hidden @ X2 @ X4)
% 0.21/0.51          | ~ (r1_tarski @ X3 @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         ((r2_hidden @ X2 @ X0) | ~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X0 @ (k2_tarski @ sk_B @ sk_A))
% 0.21/0.51          | (r2_hidden @ X0 @ sk_C_1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '28'])).
% 0.21/0.51  thf('30', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.21/0.51      inference('sup-', [status(thm)], ['7', '29'])).
% 0.21/0.51  thf('31', plain, ($false), inference('demod', [status(thm)], ['0', '30'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
