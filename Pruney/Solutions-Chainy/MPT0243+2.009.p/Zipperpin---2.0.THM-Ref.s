%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nXG8lKoqyb

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:09 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 (  97 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  462 ( 829 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t38_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ C )
          & ( r2_hidden @ B @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t38_zfmisc_1])).

thf('0',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i] :
      ( ( k1_enumset1 @ X22 @ X22 @ X23 )
      = ( k2_tarski @ X22 @ X23 ) ) ),
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

thf('3',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 )
      | ( r2_hidden @ X12 @ X16 )
      | ( X16
       != ( k1_enumset1 @ X15 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ ( k1_enumset1 @ X15 @ X14 @ X13 ) )
      | ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X9 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ~ ( zip_tseitin_0 @ X9 @ X9 @ X10 @ X7 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','12'])).

thf('14',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['14'])).

thf('16',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['14'])).

thf('18',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('19',plain,(
    ! [X24: $i,X26: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X24 ) @ X26 )
      | ~ ( r2_hidden @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('20',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('22',plain,(
    ! [X24: $i,X26: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X24 ) @ X26 )
      | ~ ( r2_hidden @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('23',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X6 @ X5 )
      | ( r1_tarski @ ( k2_xboole_0 @ X4 @ X6 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('25',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ sk_C_1 )
        | ~ ( r1_tarski @ X0 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ sk_C_1 )
   <= ( ( r2_hidden @ sk_A @ sk_C_1 )
      & ( r2_hidden @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('27',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_tarski @ X19 @ X20 )
      = ( k2_xboole_0 @ ( k1_tarski @ X19 ) @ ( k1_tarski @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('28',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( ( r2_hidden @ sk_A @ sk_C_1 )
      & ( r2_hidden @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['14'])).

thf('30',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X8 != X7 )
      | ~ ( zip_tseitin_0 @ X8 @ X9 @ X10 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ~ ( zip_tseitin_0 @ X7 @ X9 @ X10 @ X7 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('37',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['14'])).

thf('39',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','16','17','30','31','39'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.nXG8lKoqyb
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 171 iterations in 0.113s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.57  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.57  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.21/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.57  thf(t38_zfmisc_1, conjecture,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.57       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.57        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.57          ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (((r2_hidden @ sk_B @ sk_C_1)
% 0.21/0.57        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)) | 
% 0.21/0.57       ((r2_hidden @ sk_B @ sk_C_1))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf(t70_enumset1, axiom,
% 0.21/0.57    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X22 : $i, X23 : $i]:
% 0.21/0.57         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.21/0.57      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.21/0.57  thf(d1_enumset1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.57       ( ![E:$i]:
% 0.21/0.57         ( ( r2_hidden @ E @ D ) <=>
% 0.21/0.57           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.57  thf(zf_stmt_2, axiom,
% 0.21/0.57    (![E:$i,C:$i,B:$i,A:$i]:
% 0.21/0.57     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.21/0.57       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_3, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.57     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.21/0.57       ( ![E:$i]:
% 0.21/0.57         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.57         ((zip_tseitin_0 @ X12 @ X13 @ X14 @ X15)
% 0.21/0.57          | (r2_hidden @ X12 @ X16)
% 0.21/0.57          | ((X16) != (k1_enumset1 @ X15 @ X14 @ X13)))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.57         ((r2_hidden @ X12 @ (k1_enumset1 @ X15 @ X14 @ X13))
% 0.21/0.57          | (zip_tseitin_0 @ X12 @ X13 @ X14 @ X15))),
% 0.21/0.57      inference('simplify', [status(thm)], ['3'])).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.57          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.57      inference('sup+', [status(thm)], ['2', '4'])).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.57         (((X8) != (X9)) | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X7))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.57  thf('7', plain,
% 0.21/0.57      (![X7 : $i, X9 : $i, X10 : $i]: ~ (zip_tseitin_0 @ X9 @ X9 @ X10 @ X7)),
% 0.21/0.57      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['5', '7'])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      (((r2_hidden @ sk_A @ sk_C_1)
% 0.21/0.57        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('10', plain,
% 0.21/0.57      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.21/0.57         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.21/0.57      inference('split', [status(esa)], ['9'])).
% 0.21/0.57  thf(d3_tarski, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.57  thf('11', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.57          | (r2_hidden @ X0 @ X2)
% 0.21/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.57  thf('12', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          ((r2_hidden @ X0 @ sk_C_1)
% 0.21/0.57           | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))))
% 0.21/0.57         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.57  thf('13', plain,
% 0.21/0.57      (((r2_hidden @ sk_B @ sk_C_1))
% 0.21/0.57         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['8', '12'])).
% 0.21/0.57  thf('14', plain,
% 0.21/0.57      ((~ (r2_hidden @ sk_B @ sk_C_1)
% 0.21/0.57        | ~ (r2_hidden @ sk_A @ sk_C_1)
% 0.21/0.57        | ~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('15', plain,
% 0.21/0.57      ((~ (r2_hidden @ sk_B @ sk_C_1)) <= (~ ((r2_hidden @ sk_B @ sk_C_1)))),
% 0.21/0.57      inference('split', [status(esa)], ['14'])).
% 0.21/0.57  thf('16', plain,
% 0.21/0.57      (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)) | 
% 0.21/0.57       ((r2_hidden @ sk_B @ sk_C_1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['13', '15'])).
% 0.21/0.57  thf('17', plain,
% 0.21/0.57      (~ ((r2_hidden @ sk_A @ sk_C_1)) | 
% 0.21/0.57       ~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)) | 
% 0.21/0.57       ~ ((r2_hidden @ sk_B @ sk_C_1))),
% 0.21/0.57      inference('split', [status(esa)], ['14'])).
% 0.21/0.57  thf('18', plain,
% 0.21/0.57      (((r2_hidden @ sk_B @ sk_C_1)) <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 0.21/0.57      inference('split', [status(esa)], ['0'])).
% 0.21/0.57  thf(l1_zfmisc_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.21/0.57  thf('19', plain,
% 0.21/0.57      (![X24 : $i, X26 : $i]:
% 0.21/0.57         ((r1_tarski @ (k1_tarski @ X24) @ X26) | ~ (r2_hidden @ X24 @ X26))),
% 0.21/0.57      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.57  thf('20', plain,
% 0.21/0.57      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_C_1))
% 0.21/0.57         <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.57  thf('21', plain,
% 0.21/0.57      (((r2_hidden @ sk_A @ sk_C_1)) <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 0.21/0.57      inference('split', [status(esa)], ['9'])).
% 0.21/0.57  thf('22', plain,
% 0.21/0.57      (![X24 : $i, X26 : $i]:
% 0.21/0.57         ((r1_tarski @ (k1_tarski @ X24) @ X26) | ~ (r2_hidden @ X24 @ X26))),
% 0.21/0.57      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.21/0.57  thf('23', plain,
% 0.21/0.57      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1))
% 0.21/0.57         <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.57  thf(t8_xboole_1, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.21/0.57       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.21/0.57  thf('24', plain,
% 0.21/0.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.57         (~ (r1_tarski @ X4 @ X5)
% 0.21/0.57          | ~ (r1_tarski @ X6 @ X5)
% 0.21/0.57          | (r1_tarski @ (k2_xboole_0 @ X4 @ X6) @ X5))),
% 0.21/0.57      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.21/0.57  thf('25', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ sk_C_1)
% 0.21/0.57           | ~ (r1_tarski @ X0 @ sk_C_1)))
% 0.21/0.57         <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['23', '24'])).
% 0.21/0.57  thf('26', plain,
% 0.21/0.57      (((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 0.21/0.57         sk_C_1))
% 0.21/0.57         <= (((r2_hidden @ sk_A @ sk_C_1)) & ((r2_hidden @ sk_B @ sk_C_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['20', '25'])).
% 0.21/0.57  thf(t41_enumset1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ( k2_tarski @ A @ B ) =
% 0.21/0.57       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.21/0.57  thf('27', plain,
% 0.21/0.57      (![X19 : $i, X20 : $i]:
% 0.21/0.57         ((k2_tarski @ X19 @ X20)
% 0.21/0.57           = (k2_xboole_0 @ (k1_tarski @ X19) @ (k1_tarski @ X20)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.21/0.57  thf('28', plain,
% 0.21/0.57      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.21/0.57         <= (((r2_hidden @ sk_A @ sk_C_1)) & ((r2_hidden @ sk_B @ sk_C_1)))),
% 0.21/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.21/0.57  thf('29', plain,
% 0.21/0.57      ((~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.21/0.57         <= (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.21/0.57      inference('split', [status(esa)], ['14'])).
% 0.21/0.57  thf('30', plain,
% 0.21/0.57      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)) | 
% 0.21/0.57       ~ ((r2_hidden @ sk_A @ sk_C_1)) | ~ ((r2_hidden @ sk_B @ sk_C_1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.57  thf('31', plain,
% 0.21/0.57      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)) | 
% 0.21/0.57       ((r2_hidden @ sk_A @ sk_C_1))),
% 0.21/0.57      inference('split', [status(esa)], ['9'])).
% 0.21/0.57  thf('32', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.57         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.21/0.57          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.21/0.57      inference('sup+', [status(thm)], ['2', '4'])).
% 0.21/0.57  thf('33', plain,
% 0.21/0.57      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.57         (((X8) != (X7)) | ~ (zip_tseitin_0 @ X8 @ X9 @ X10 @ X7))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.57  thf('34', plain,
% 0.21/0.57      (![X7 : $i, X9 : $i, X10 : $i]: ~ (zip_tseitin_0 @ X7 @ X9 @ X10 @ X7)),
% 0.21/0.57      inference('simplify', [status(thm)], ['33'])).
% 0.21/0.57  thf('35', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.21/0.57      inference('sup-', [status(thm)], ['32', '34'])).
% 0.21/0.57  thf('36', plain,
% 0.21/0.57      ((![X0 : $i]:
% 0.21/0.57          ((r2_hidden @ X0 @ sk_C_1)
% 0.21/0.57           | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))))
% 0.21/0.58         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.58  thf('37', plain,
% 0.21/0.58      (((r2_hidden @ sk_A @ sk_C_1))
% 0.21/0.58         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.58  thf('38', plain,
% 0.21/0.58      ((~ (r2_hidden @ sk_A @ sk_C_1)) <= (~ ((r2_hidden @ sk_A @ sk_C_1)))),
% 0.21/0.58      inference('split', [status(esa)], ['14'])).
% 0.21/0.58  thf('39', plain,
% 0.21/0.58      (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)) | 
% 0.21/0.58       ((r2_hidden @ sk_A @ sk_C_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.58  thf('40', plain, ($false),
% 0.21/0.58      inference('sat_resolution*', [status(thm)],
% 0.21/0.58                ['1', '16', '17', '30', '31', '39'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.21/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
