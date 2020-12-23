%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ctptmoeBXh

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:09 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 101 expanded)
%              Number of leaves         :   21 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  522 ( 830 expanded)
%              Number of equality atoms :   18 (  19 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

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
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('3',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_tarski @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ ( k1_tarski @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
    | ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
   <= ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('13',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    ! [X27: $i,X29: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X27 ) @ X29 )
      | ~ ( r2_hidden @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('16',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_C )
   <= ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ sk_A @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,(
    ! [X27: $i,X29: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X27 ) @ X29 )
      | ~ ( r2_hidden @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('19',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ~ ( r1_tarski @ X7 @ X6 )
      | ( r1_tarski @ ( k2_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ sk_C )
        | ~ ( r1_tarski @ X0 @ sk_C ) )
   <= ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ sk_C )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf('23',plain,(
    ! [X20: $i,X21: $i] :
      ( ( k2_tarski @ X20 @ X21 )
      = ( k2_xboole_0 @ ( k1_tarski @ X20 ) @ ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('24',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( ( r2_hidden @ sk_A @ sk_C )
      & ( r2_hidden @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    | ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['13'])).

thf('28',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('29',plain,(
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

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 )
      | ( r2_hidden @ X13 @ X17 )
      | ( X17
       != ( k1_enumset1 @ X16 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X13 @ ( k1_enumset1 @ X16 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X9 != X10 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ~ ( zip_tseitin_0 @ X10 @ X10 @ X11 @ X8 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X27: $i,X29: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X27 ) @ X29 )
      | ~ ( r2_hidden @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('38',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_xboole_0 @ X4 @ X3 )
        = X3 )
      | ~ ( r1_tarski @ X4 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['28','41'])).

thf('43',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ ( k1_tarski @ X27 ) @ X28 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('44',plain,
    ( ( r2_hidden @ sk_B @ sk_C )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C )
   <= ~ ( r2_hidden @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['9'])).

thf('46',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    | ( r2_hidden @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','11','12','26','27','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ctptmoeBXh
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 365 iterations in 0.146s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.38/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.60  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.38/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.38/0.60  thf(t38_zfmisc_1, conjecture,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.38/0.60       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.38/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.60        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.38/0.60          ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ) )),
% 0.38/0.60    inference('cnf.neg', [status(esa)], [t38_zfmisc_1])).
% 0.38/0.60  thf('0', plain,
% 0.38/0.60      (((r2_hidden @ sk_A @ sk_C)
% 0.38/0.60        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('1', plain,
% 0.38/0.60      (((r2_hidden @ sk_A @ sk_C)) | 
% 0.38/0.60       ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.38/0.60      inference('split', [status(esa)], ['0'])).
% 0.38/0.60  thf('2', plain,
% 0.38/0.60      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.38/0.60         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.38/0.60      inference('split', [status(esa)], ['0'])).
% 0.38/0.60  thf(t41_enumset1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( k2_tarski @ A @ B ) =
% 0.38/0.60       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.38/0.60  thf('3', plain,
% 0.38/0.60      (![X20 : $i, X21 : $i]:
% 0.38/0.60         ((k2_tarski @ X20 @ X21)
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X21)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.38/0.60  thf(t11_xboole_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.38/0.60  thf('4', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.38/0.60      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.38/0.60  thf('5', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.38/0.60          | (r1_tarski @ (k1_tarski @ X1) @ X2))),
% 0.38/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.38/0.60  thf('6', plain,
% 0.38/0.60      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C))
% 0.38/0.60         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['2', '5'])).
% 0.38/0.60  thf(l1_zfmisc_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.38/0.60  thf('7', plain,
% 0.38/0.60      (![X27 : $i, X28 : $i]:
% 0.38/0.60         ((r2_hidden @ X27 @ X28) | ~ (r1_tarski @ (k1_tarski @ X27) @ X28))),
% 0.38/0.60      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.38/0.60  thf('8', plain,
% 0.38/0.60      (((r2_hidden @ sk_A @ sk_C))
% 0.38/0.60         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.38/0.60  thf('9', plain,
% 0.38/0.60      ((~ (r2_hidden @ sk_B @ sk_C)
% 0.38/0.60        | ~ (r2_hidden @ sk_A @ sk_C)
% 0.38/0.60        | ~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('10', plain,
% 0.38/0.60      ((~ (r2_hidden @ sk_A @ sk_C)) <= (~ ((r2_hidden @ sk_A @ sk_C)))),
% 0.38/0.60      inference('split', [status(esa)], ['9'])).
% 0.38/0.60  thf('11', plain,
% 0.38/0.60      (((r2_hidden @ sk_A @ sk_C)) | 
% 0.38/0.60       ~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['8', '10'])).
% 0.38/0.60  thf('12', plain,
% 0.38/0.60      (~ ((r2_hidden @ sk_A @ sk_C)) | 
% 0.38/0.60       ~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)) | 
% 0.38/0.60       ~ ((r2_hidden @ sk_B @ sk_C))),
% 0.38/0.60      inference('split', [status(esa)], ['9'])).
% 0.38/0.60  thf('13', plain,
% 0.38/0.60      (((r2_hidden @ sk_B @ sk_C)
% 0.38/0.60        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.60  thf('14', plain,
% 0.38/0.60      (((r2_hidden @ sk_B @ sk_C)) <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.38/0.60      inference('split', [status(esa)], ['13'])).
% 0.38/0.60  thf('15', plain,
% 0.38/0.60      (![X27 : $i, X29 : $i]:
% 0.38/0.60         ((r1_tarski @ (k1_tarski @ X27) @ X29) | ~ (r2_hidden @ X27 @ X29))),
% 0.38/0.60      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.38/0.60  thf('16', plain,
% 0.38/0.60      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_C))
% 0.38/0.60         <= (((r2_hidden @ sk_B @ sk_C)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['14', '15'])).
% 0.38/0.60  thf('17', plain,
% 0.38/0.60      (((r2_hidden @ sk_A @ sk_C)) <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.38/0.60      inference('split', [status(esa)], ['0'])).
% 0.38/0.60  thf('18', plain,
% 0.38/0.60      (![X27 : $i, X29 : $i]:
% 0.38/0.60         ((r1_tarski @ (k1_tarski @ X27) @ X29) | ~ (r2_hidden @ X27 @ X29))),
% 0.38/0.60      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.38/0.60  thf('19', plain,
% 0.38/0.60      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C))
% 0.38/0.60         <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['17', '18'])).
% 0.38/0.60  thf(t8_xboole_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 0.38/0.60       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 0.38/0.60  thf('20', plain,
% 0.38/0.60      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.38/0.60         (~ (r1_tarski @ X5 @ X6)
% 0.38/0.60          | ~ (r1_tarski @ X7 @ X6)
% 0.38/0.60          | (r1_tarski @ (k2_xboole_0 @ X5 @ X7) @ X6))),
% 0.38/0.60      inference('cnf', [status(esa)], [t8_xboole_1])).
% 0.38/0.60  thf('21', plain,
% 0.38/0.60      ((![X0 : $i]:
% 0.38/0.60          ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ sk_C)
% 0.38/0.60           | ~ (r1_tarski @ X0 @ sk_C)))
% 0.38/0.60         <= (((r2_hidden @ sk_A @ sk_C)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.60  thf('22', plain,
% 0.38/0.60      (((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 0.38/0.60         sk_C)) <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['16', '21'])).
% 0.38/0.60  thf('23', plain,
% 0.38/0.60      (![X20 : $i, X21 : $i]:
% 0.38/0.60         ((k2_tarski @ X20 @ X21)
% 0.38/0.60           = (k2_xboole_0 @ (k1_tarski @ X20) @ (k1_tarski @ X21)))),
% 0.38/0.60      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.38/0.60  thf('24', plain,
% 0.38/0.60      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.38/0.60         <= (((r2_hidden @ sk_A @ sk_C)) & ((r2_hidden @ sk_B @ sk_C)))),
% 0.38/0.60      inference('demod', [status(thm)], ['22', '23'])).
% 0.38/0.60  thf('25', plain,
% 0.38/0.60      ((~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.38/0.60         <= (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.38/0.60      inference('split', [status(esa)], ['9'])).
% 0.38/0.60  thf('26', plain,
% 0.38/0.60      (~ ((r2_hidden @ sk_A @ sk_C)) | 
% 0.38/0.60       ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)) | 
% 0.38/0.60       ~ ((r2_hidden @ sk_B @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.60  thf('27', plain,
% 0.38/0.60      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)) | 
% 0.38/0.60       ((r2_hidden @ sk_B @ sk_C))),
% 0.38/0.60      inference('split', [status(esa)], ['13'])).
% 0.38/0.60  thf('28', plain,
% 0.38/0.60      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.38/0.60         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.38/0.60      inference('split', [status(esa)], ['0'])).
% 0.38/0.60  thf(t70_enumset1, axiom,
% 0.38/0.60    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.38/0.60  thf('29', plain,
% 0.38/0.60      (![X22 : $i, X23 : $i]:
% 0.38/0.60         ((k1_enumset1 @ X22 @ X22 @ X23) = (k2_tarski @ X22 @ X23))),
% 0.38/0.60      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.38/0.60  thf(d1_enumset1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.38/0.60       ( ![E:$i]:
% 0.38/0.60         ( ( r2_hidden @ E @ D ) <=>
% 0.38/0.60           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.38/0.60  thf(zf_stmt_2, axiom,
% 0.38/0.60    (![E:$i,C:$i,B:$i,A:$i]:
% 0.38/0.60     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.38/0.60       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_3, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.60     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.38/0.60       ( ![E:$i]:
% 0.38/0.60         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.38/0.60  thf('30', plain,
% 0.38/0.60      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.60         ((zip_tseitin_0 @ X13 @ X14 @ X15 @ X16)
% 0.38/0.60          | (r2_hidden @ X13 @ X17)
% 0.38/0.60          | ((X17) != (k1_enumset1 @ X16 @ X15 @ X14)))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.60  thf('31', plain,
% 0.38/0.60      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.38/0.60         ((r2_hidden @ X13 @ (k1_enumset1 @ X16 @ X15 @ X14))
% 0.38/0.60          | (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16))),
% 0.38/0.60      inference('simplify', [status(thm)], ['30'])).
% 0.38/0.60  thf('32', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.38/0.60          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.38/0.60      inference('sup+', [status(thm)], ['29', '31'])).
% 0.38/0.60  thf('33', plain,
% 0.38/0.60      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.38/0.60         (((X9) != (X10)) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.38/0.60      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.60  thf('34', plain,
% 0.38/0.60      (![X8 : $i, X10 : $i, X11 : $i]: ~ (zip_tseitin_0 @ X10 @ X10 @ X11 @ X8)),
% 0.38/0.60      inference('simplify', [status(thm)], ['33'])).
% 0.38/0.60  thf('35', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.38/0.60      inference('sup-', [status(thm)], ['32', '34'])).
% 0.38/0.60  thf('36', plain,
% 0.38/0.60      (![X27 : $i, X29 : $i]:
% 0.38/0.60         ((r1_tarski @ (k1_tarski @ X27) @ X29) | ~ (r2_hidden @ X27 @ X29))),
% 0.38/0.60      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.38/0.60  thf('37', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         (r1_tarski @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['35', '36'])).
% 0.38/0.60  thf(t12_xboole_1, axiom,
% 0.38/0.60    (![A:$i,B:$i]:
% 0.38/0.60     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.38/0.60  thf('38', plain,
% 0.38/0.60      (![X3 : $i, X4 : $i]:
% 0.38/0.60         (((k2_xboole_0 @ X4 @ X3) = (X3)) | ~ (r1_tarski @ X4 @ X3))),
% 0.38/0.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.38/0.60  thf('39', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i]:
% 0.38/0.60         ((k2_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.38/0.60           = (k2_tarski @ X1 @ X0))),
% 0.38/0.60      inference('sup-', [status(thm)], ['37', '38'])).
% 0.38/0.60  thf('40', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         ((r1_tarski @ X0 @ X1) | ~ (r1_tarski @ (k2_xboole_0 @ X0 @ X2) @ X1))),
% 0.38/0.60      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.38/0.60  thf('41', plain,
% 0.38/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.60         (~ (r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.38/0.60          | (r1_tarski @ (k1_tarski @ X0) @ X2))),
% 0.38/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.38/0.60  thf('42', plain,
% 0.38/0.60      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_C))
% 0.38/0.60         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['28', '41'])).
% 0.38/0.60  thf('43', plain,
% 0.38/0.60      (![X27 : $i, X28 : $i]:
% 0.38/0.60         ((r2_hidden @ X27 @ X28) | ~ (r1_tarski @ (k1_tarski @ X27) @ X28))),
% 0.38/0.60      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.38/0.60  thf('44', plain,
% 0.38/0.60      (((r2_hidden @ sk_B @ sk_C))
% 0.38/0.60         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.38/0.60      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.60  thf('45', plain,
% 0.38/0.60      ((~ (r2_hidden @ sk_B @ sk_C)) <= (~ ((r2_hidden @ sk_B @ sk_C)))),
% 0.38/0.60      inference('split', [status(esa)], ['9'])).
% 0.38/0.60  thf('46', plain,
% 0.38/0.60      (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)) | 
% 0.38/0.60       ((r2_hidden @ sk_B @ sk_C))),
% 0.38/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.38/0.60  thf('47', plain, ($false),
% 0.38/0.60      inference('sat_resolution*', [status(thm)],
% 0.38/0.60                ['1', '11', '12', '26', '27', '46'])).
% 0.38/0.60  
% 0.38/0.60  % SZS output end Refutation
% 0.38/0.60  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
