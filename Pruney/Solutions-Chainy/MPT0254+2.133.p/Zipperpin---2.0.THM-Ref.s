%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7ex6zfgjIB

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 (  79 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :  291 ( 481 expanded)
%              Number of equality atoms :    8 (  22 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t49_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t49_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X21: $i] :
      ( ( k2_tarski @ X21 @ X21 )
      = ( k1_tarski @ X21 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t47_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
     => ( r2_hidden @ A @ C ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ X22 @ X24 ) @ X23 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t47_zfmisc_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) @ X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('5',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('6',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ~ ( ~ ( r2_hidden @ C @ A )
            & ( r2_hidden @ C @ B ) )
        & ~ ( ~ ( r2_hidden @ C @ B )
            & ( r2_hidden @ C @ A ) )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ( r1_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( r2_hidden @ C @ A )
        & ~ ( r2_hidden @ C @ B ) ) ) )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ C @ B @ A )
     => ( ( r2_hidden @ C @ B )
        & ~ ( r2_hidden @ C @ A ) ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ A @ B )
        & ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) )
        & ~ ( zip_tseitin_1 @ C @ B @ A )
        & ~ ( zip_tseitin_0 @ C @ B @ A ) ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ X13 )
      | ( zip_tseitin_0 @ X14 @ X13 @ X12 )
      | ( zip_tseitin_1 @ X14 @ X13 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k2_xboole_0 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_A @ sk_B @ X0 )
      | ( zip_tseitin_0 @ sk_A @ sk_B @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i,X20: $i] :
      ( ( r1_xboole_0 @ X17 @ X20 )
      | ~ ( r1_xboole_0 @ X17 @ ( k2_xboole_0 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('16',plain,(
    ! [X16: $i] :
      ( r1_xboole_0 @ X16 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ sk_B ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_A @ sk_B @ X0 )
      | ( zip_tseitin_0 @ sk_A @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['12','17'])).

thf('19',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X11 )
      | ~ ( zip_tseitin_1 @ X9 @ X11 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ sk_B @ X0 )
      | ~ ( r2_hidden @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference(demod,[status(thm)],['4','5'])).

thf('22',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_A @ sk_B @ X0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X8 )
      | ~ ( zip_tseitin_0 @ X6 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    $false ),
    inference('sup-',[status(thm)],['9','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7ex6zfgjIB
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:10:44 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running portfolio for 600 s
% 0.20/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.34  % Python version: Python 3.6.8
% 0.20/0.34  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 202 iterations in 0.088s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.55  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.55  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.55  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $o).
% 0.20/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.55  thf(t49_zfmisc_1, conjecture,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i,B:$i]:
% 0.20/0.55        ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t49_zfmisc_1])).
% 0.20/0.55  thf('0', plain,
% 0.20/0.55      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t69_enumset1, axiom,
% 0.20/0.55    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.55  thf('1', plain, (![X21 : $i]: ((k2_tarski @ X21 @ X21) = (k1_tarski @ X21))),
% 0.20/0.55      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.55  thf(t47_zfmisc_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.20/0.55       ( r2_hidden @ A @ C ) ))).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.55         ((r2_hidden @ X22 @ X23)
% 0.20/0.55          | ~ (r1_tarski @ (k2_xboole_0 @ (k2_tarski @ X22 @ X24) @ X23) @ X23))),
% 0.20/0.55      inference('cnf', [status(esa)], [t47_zfmisc_1])).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         (~ (r1_tarski @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1) @ X1)
% 0.20/0.55          | (r2_hidden @ X0 @ X1))),
% 0.20/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      ((~ (r1_tarski @ k1_xboole_0 @ sk_B) | (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.55  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.55  thf('5', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 0.20/0.55      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.55  thf('6', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.55  thf(d3_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.20/0.55       ( ![D:$i]:
% 0.20/0.55         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.55           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.55          | (r2_hidden @ X0 @ X2)
% 0.20/0.55          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.20/0.55      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.20/0.55         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.55      inference('simplify', [status(thm)], ['7'])).
% 0.20/0.55  thf('9', plain, (![X0 : $i]: (r2_hidden @ sk_A @ (k2_xboole_0 @ X0 @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['6', '8'])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (![X0 : $i]: (r2_hidden @ sk_A @ (k2_xboole_0 @ X0 @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['6', '8'])).
% 0.20/0.55  thf(t5_xboole_0, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ~( ( ~( ( ~( r2_hidden @ C @ A ) ) & ( r2_hidden @ C @ B ) ) ) & 
% 0.20/0.55          ( ~( ( ~( r2_hidden @ C @ B ) ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.55          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & ( r1_xboole_0 @ A @ B ) ) ))).
% 0.20/0.55  thf(zf_stmt_1, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.55  thf(zf_stmt_2, axiom,
% 0.20/0.55    (![C:$i,B:$i,A:$i]:
% 0.20/0.55     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.55       ( ( r2_hidden @ C @ A ) & ( ~( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $i > $o).
% 0.20/0.55  thf(zf_stmt_4, axiom,
% 0.20/0.55    (![C:$i,B:$i,A:$i]:
% 0.20/0.55     ( ( zip_tseitin_0 @ C @ B @ A ) =>
% 0.20/0.55       ( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_5, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ~( ( r1_xboole_0 @ A @ B ) & 
% 0.20/0.55          ( r2_hidden @ C @ ( k2_xboole_0 @ A @ B ) ) & 
% 0.20/0.55          ( ~( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.55          ( ~( zip_tseitin_0 @ C @ B @ A ) ) ) ))).
% 0.20/0.55  thf('11', plain,
% 0.20/0.55      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.55         (~ (r1_xboole_0 @ X12 @ X13)
% 0.20/0.55          | (zip_tseitin_0 @ X14 @ X13 @ X12)
% 0.20/0.55          | (zip_tseitin_1 @ X14 @ X13 @ X12)
% 0.20/0.55          | ~ (r2_hidden @ X14 @ (k2_xboole_0 @ X12 @ X13)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.55  thf('12', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((zip_tseitin_1 @ sk_A @ sk_B @ X0)
% 0.20/0.55          | (zip_tseitin_0 @ sk_A @ sk_B @ X0)
% 0.20/0.55          | ~ (r1_xboole_0 @ X0 @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (((k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) = (k1_xboole_0))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t70_xboole_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 0.20/0.55            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 0.20/0.55       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 0.20/0.55            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      (![X17 : $i, X18 : $i, X20 : $i]:
% 0.20/0.55         ((r1_xboole_0 @ X17 @ X20)
% 0.20/0.55          | ~ (r1_xboole_0 @ X17 @ (k2_xboole_0 @ X18 @ X20)))),
% 0.20/0.55      inference('cnf', [status(esa)], [t70_xboole_1])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (r1_xboole_0 @ X0 @ k1_xboole_0) | (r1_xboole_0 @ X0 @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.55  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.55  thf('16', plain, (![X16 : $i]: (r1_xboole_0 @ X16 @ k1_xboole_0)),
% 0.20/0.55      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.55  thf('17', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ sk_B)),
% 0.20/0.55      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.55  thf('18', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((zip_tseitin_1 @ sk_A @ sk_B @ X0)
% 0.20/0.55          | (zip_tseitin_0 @ sk_A @ sk_B @ X0))),
% 0.20/0.55      inference('demod', [status(thm)], ['12', '17'])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X9 @ X11) | ~ (zip_tseitin_1 @ X9 @ X11 @ X10))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((zip_tseitin_0 @ sk_A @ sk_B @ X0) | ~ (r2_hidden @ sk_A @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.55  thf('21', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.20/0.55      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.55  thf('22', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_A @ sk_B @ X0)),
% 0.20/0.55      inference('demod', [status(thm)], ['20', '21'])).
% 0.20/0.55  thf('23', plain,
% 0.20/0.55      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.55         (~ (r2_hidden @ X6 @ X8) | ~ (zip_tseitin_0 @ X6 @ X7 @ X8))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.20/0.55  thf('24', plain, (![X0 : $i]: ~ (r2_hidden @ sk_A @ X0)),
% 0.20/0.55      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.55  thf('25', plain, ($false), inference('sup-', [status(thm)], ['9', '24'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
