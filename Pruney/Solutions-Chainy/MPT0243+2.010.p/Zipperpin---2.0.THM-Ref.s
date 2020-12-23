%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3YsiqsqTaW

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:09 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 211 expanded)
%              Number of leaves         :   16 (  61 expanded)
%              Depth                    :   13
%              Number of atoms          :  575 (1978 expanded)
%              Number of equality atoms :   26 (  70 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

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
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X16 @ X16 @ X17 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
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

thf('4',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 )
      | ( r2_hidden @ X9 @ X13 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('5',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) )
      | ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X4 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['9','13'])).

thf('15',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('18',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X6 )
      | ~ ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X4 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ~ ( zip_tseitin_0 @ X6 @ X6 @ X7 @ X4 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('22',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['2','16','24'])).

thf('26',plain,(
    ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['1','25'])).

thf('27',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('28',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('29',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','16','24','28'])).

thf('30',plain,(
    r2_hidden @ sk_A @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['27','29'])).

thf('31',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['31'])).

thf('34',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference('sat_resolution*',[status(thm)],['2','16','24','33'])).

thf('35',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(simpl_trail,[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( X5 = X6 )
      | ( X5 = X7 )
      | ( X5 = X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('37',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('38',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_enumset1 @ X16 @ X16 @ X17 )
      = ( k2_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('39',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ( X13
       != ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ~ ( zip_tseitin_0 @ X14 @ X10 @ X11 @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k1_enumset1 @ X12 @ X11 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['38','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X1 @ X0 ) @ X2 )
      | ~ ( zip_tseitin_0 @ ( sk_C @ X2 @ ( k2_tarski @ X1 @ X0 ) ) @ X0 @ X1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X0 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X0 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X0 @ X1 ) @ X2 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X1 )
      | ( ( sk_C @ X2 @ ( k2_tarski @ X0 @ X1 ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( ( sk_C @ X1 @ ( k2_tarski @ X2 @ X0 ) )
        = X2 )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X0 ) @ X1 )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X2 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_tarski @ X2 @ X0 ) )
        = X2 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( sk_C @ sk_C_1 @ ( k2_tarski @ X0 @ sk_B ) )
        = X0 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['35','47'])).

thf('49',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_C_1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B ) @ sk_C_1 )
      | ( r1_tarski @ ( k2_tarski @ X0 @ sk_B ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X0 @ sk_B ) @ sk_C_1 )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['30','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['26','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3YsiqsqTaW
% 0.13/0.37  % Computer   : n015.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 18:50:38 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 231 iterations in 0.127s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.61  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.41/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.41/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(t38_zfmisc_1, conjecture,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.41/0.61       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.61        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.41/0.61          ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t38_zfmisc_1])).
% 0.41/0.61  thf('0', plain,
% 0.41/0.61      ((~ (r2_hidden @ sk_B @ sk_C_1)
% 0.41/0.61        | ~ (r2_hidden @ sk_A @ sk_C_1)
% 0.41/0.61        | ~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('1', plain,
% 0.41/0.61      ((~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.41/0.61         <= (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf('2', plain,
% 0.41/0.61      (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)) | 
% 0.41/0.61       ~ ((r2_hidden @ sk_B @ sk_C_1)) | ~ ((r2_hidden @ sk_A @ sk_C_1))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf(t70_enumset1, axiom,
% 0.41/0.61    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.41/0.61  thf('3', plain,
% 0.41/0.61      (![X16 : $i, X17 : $i]:
% 0.41/0.61         ((k1_enumset1 @ X16 @ X16 @ X17) = (k2_tarski @ X16 @ X17))),
% 0.41/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.41/0.61  thf(d1_enumset1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.41/0.61       ( ![E:$i]:
% 0.41/0.61         ( ( r2_hidden @ E @ D ) <=>
% 0.41/0.61           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.41/0.61  thf(zf_stmt_2, axiom,
% 0.41/0.61    (![E:$i,C:$i,B:$i,A:$i]:
% 0.41/0.61     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.41/0.61       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_3, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.61     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.41/0.61       ( ![E:$i]:
% 0.41/0.61         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.41/0.61  thf('4', plain,
% 0.41/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.41/0.61         ((zip_tseitin_0 @ X9 @ X10 @ X11 @ X12)
% 0.41/0.61          | (r2_hidden @ X9 @ X13)
% 0.41/0.61          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.41/0.61  thf('5', plain,
% 0.41/0.61      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.61         ((r2_hidden @ X9 @ (k1_enumset1 @ X12 @ X11 @ X10))
% 0.41/0.61          | (zip_tseitin_0 @ X9 @ X10 @ X11 @ X12))),
% 0.41/0.61      inference('simplify', [status(thm)], ['4'])).
% 0.41/0.61  thf('6', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.41/0.61          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.41/0.61      inference('sup+', [status(thm)], ['3', '5'])).
% 0.41/0.61  thf('7', plain,
% 0.41/0.61      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.61         (((X5) != (X4)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.41/0.61  thf('8', plain,
% 0.41/0.61      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X4 @ X6 @ X7 @ X4)),
% 0.41/0.61      inference('simplify', [status(thm)], ['7'])).
% 0.41/0.61  thf('9', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['6', '8'])).
% 0.41/0.61  thf('10', plain,
% 0.41/0.61      (((r2_hidden @ sk_A @ sk_C_1)
% 0.41/0.61        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('11', plain,
% 0.41/0.61      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 0.41/0.61         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.41/0.61      inference('split', [status(esa)], ['10'])).
% 0.41/0.61  thf(d3_tarski, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.41/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.41/0.61          | (r2_hidden @ X0 @ X2)
% 0.41/0.61          | ~ (r1_tarski @ X1 @ X2))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      ((![X0 : $i]:
% 0.41/0.61          ((r2_hidden @ X0 @ sk_C_1)
% 0.41/0.61           | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))))
% 0.41/0.61         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.61  thf('14', plain,
% 0.41/0.61      (((r2_hidden @ sk_A @ sk_C_1))
% 0.41/0.61         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['9', '13'])).
% 0.41/0.61  thf('15', plain,
% 0.41/0.61      ((~ (r2_hidden @ sk_A @ sk_C_1)) <= (~ ((r2_hidden @ sk_A @ sk_C_1)))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf('16', plain,
% 0.41/0.61      (((r2_hidden @ sk_A @ sk_C_1)) | 
% 0.41/0.61       ~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.41/0.61  thf('17', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.41/0.61          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.41/0.61      inference('sup+', [status(thm)], ['3', '5'])).
% 0.41/0.61  thf('18', plain,
% 0.41/0.61      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.41/0.61         (((X5) != (X6)) | ~ (zip_tseitin_0 @ X5 @ X6 @ X7 @ X4))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.41/0.61  thf('19', plain,
% 0.41/0.61      (![X4 : $i, X6 : $i, X7 : $i]: ~ (zip_tseitin_0 @ X6 @ X6 @ X7 @ X4)),
% 0.41/0.61      inference('simplify', [status(thm)], ['18'])).
% 0.41/0.61  thf('20', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['17', '19'])).
% 0.41/0.61  thf('21', plain,
% 0.41/0.61      ((![X0 : $i]:
% 0.41/0.61          ((r2_hidden @ X0 @ sk_C_1)
% 0.41/0.61           | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))))
% 0.41/0.61         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.61  thf('22', plain,
% 0.41/0.61      (((r2_hidden @ sk_B @ sk_C_1))
% 0.41/0.61         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['20', '21'])).
% 0.41/0.61  thf('23', plain,
% 0.41/0.61      ((~ (r2_hidden @ sk_B @ sk_C_1)) <= (~ ((r2_hidden @ sk_B @ sk_C_1)))),
% 0.41/0.61      inference('split', [status(esa)], ['0'])).
% 0.41/0.61  thf('24', plain,
% 0.41/0.61      (((r2_hidden @ sk_B @ sk_C_1)) | 
% 0.41/0.61       ~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.61  thf('25', plain, (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['2', '16', '24'])).
% 0.41/0.61  thf('26', plain, (~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['1', '25'])).
% 0.41/0.61  thf('27', plain,
% 0.41/0.61      (((r2_hidden @ sk_A @ sk_C_1)) <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 0.41/0.61      inference('split', [status(esa)], ['10'])).
% 0.41/0.61  thf('28', plain,
% 0.41/0.61      (((r2_hidden @ sk_A @ sk_C_1)) | 
% 0.41/0.61       ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.41/0.61      inference('split', [status(esa)], ['10'])).
% 0.41/0.61  thf('29', plain, (((r2_hidden @ sk_A @ sk_C_1))),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['2', '16', '24', '28'])).
% 0.41/0.61  thf('30', plain, ((r2_hidden @ sk_A @ sk_C_1)),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['27', '29'])).
% 0.41/0.61  thf('31', plain,
% 0.41/0.61      (((r2_hidden @ sk_B @ sk_C_1)
% 0.41/0.61        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('32', plain,
% 0.41/0.61      (((r2_hidden @ sk_B @ sk_C_1)) <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 0.41/0.61      inference('split', [status(esa)], ['31'])).
% 0.41/0.61  thf('33', plain,
% 0.41/0.61      (((r2_hidden @ sk_B @ sk_C_1)) | 
% 0.41/0.61       ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 0.41/0.61      inference('split', [status(esa)], ['31'])).
% 0.41/0.61  thf('34', plain, (((r2_hidden @ sk_B @ sk_C_1))),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['2', '16', '24', '33'])).
% 0.41/0.61  thf('35', plain, ((r2_hidden @ sk_B @ sk_C_1)),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['32', '34'])).
% 0.41/0.61  thf('36', plain,
% 0.41/0.61      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.41/0.61         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.41/0.61          | ((X5) = (X6))
% 0.41/0.61          | ((X5) = (X7))
% 0.41/0.61          | ((X5) = (X8)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.41/0.61  thf('37', plain,
% 0.41/0.61      (![X1 : $i, X3 : $i]:
% 0.41/0.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('38', plain,
% 0.41/0.61      (![X16 : $i, X17 : $i]:
% 0.41/0.61         ((k1_enumset1 @ X16 @ X16 @ X17) = (k2_tarski @ X16 @ X17))),
% 0.41/0.61      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.41/0.61  thf('39', plain,
% 0.41/0.61      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X14 @ X13)
% 0.41/0.61          | ~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.41/0.61          | ((X13) != (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.41/0.61  thf('40', plain,
% 0.41/0.61      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.41/0.61         (~ (zip_tseitin_0 @ X14 @ X10 @ X11 @ X12)
% 0.41/0.61          | ~ (r2_hidden @ X14 @ (k1_enumset1 @ X12 @ X11 @ X10)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['39'])).
% 0.41/0.61  thf('41', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.41/0.61          | ~ (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['38', '40'])).
% 0.41/0.61  thf('42', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((r1_tarski @ (k2_tarski @ X1 @ X0) @ X2)
% 0.41/0.61          | ~ (zip_tseitin_0 @ (sk_C @ X2 @ (k2_tarski @ X1 @ X0)) @ X0 @ X1 @ 
% 0.41/0.61               X1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['37', '41'])).
% 0.41/0.61  thf('43', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (((sk_C @ X2 @ (k2_tarski @ X0 @ X1)) = (X0))
% 0.41/0.61          | ((sk_C @ X2 @ (k2_tarski @ X0 @ X1)) = (X0))
% 0.41/0.61          | ((sk_C @ X2 @ (k2_tarski @ X0 @ X1)) = (X1))
% 0.41/0.61          | (r1_tarski @ (k2_tarski @ X0 @ X1) @ X2))),
% 0.41/0.61      inference('sup-', [status(thm)], ['36', '42'])).
% 0.41/0.61  thf('44', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((r1_tarski @ (k2_tarski @ X0 @ X1) @ X2)
% 0.41/0.61          | ((sk_C @ X2 @ (k2_tarski @ X0 @ X1)) = (X1))
% 0.41/0.61          | ((sk_C @ X2 @ (k2_tarski @ X0 @ X1)) = (X0)))),
% 0.41/0.61      inference('simplify', [status(thm)], ['43'])).
% 0.41/0.61  thf('45', plain,
% 0.41/0.61      (![X1 : $i, X3 : $i]:
% 0.41/0.61         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('46', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X0 @ X1)
% 0.41/0.61          | ((sk_C @ X1 @ (k2_tarski @ X2 @ X0)) = (X2))
% 0.41/0.61          | (r1_tarski @ (k2_tarski @ X2 @ X0) @ X1)
% 0.41/0.61          | (r1_tarski @ (k2_tarski @ X2 @ X0) @ X1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.41/0.61  thf('47', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((r1_tarski @ (k2_tarski @ X2 @ X0) @ X1)
% 0.41/0.61          | ((sk_C @ X1 @ (k2_tarski @ X2 @ X0)) = (X2))
% 0.41/0.61          | ~ (r2_hidden @ X0 @ X1))),
% 0.41/0.61      inference('simplify', [status(thm)], ['46'])).
% 0.41/0.61  thf('48', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (((sk_C @ sk_C_1 @ (k2_tarski @ X0 @ sk_B)) = (X0))
% 0.41/0.61          | (r1_tarski @ (k2_tarski @ X0 @ sk_B) @ sk_C_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['35', '47'])).
% 0.41/0.61  thf('49', plain,
% 0.41/0.61      (![X1 : $i, X3 : $i]:
% 0.41/0.61         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.41/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.61  thf('50', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X0 @ sk_C_1)
% 0.41/0.61          | (r1_tarski @ (k2_tarski @ X0 @ sk_B) @ sk_C_1)
% 0.41/0.61          | (r1_tarski @ (k2_tarski @ X0 @ sk_B) @ sk_C_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['48', '49'])).
% 0.41/0.61  thf('51', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((r1_tarski @ (k2_tarski @ X0 @ sk_B) @ sk_C_1)
% 0.41/0.61          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.41/0.61      inference('simplify', [status(thm)], ['50'])).
% 0.41/0.61  thf('52', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)),
% 0.41/0.61      inference('sup-', [status(thm)], ['30', '51'])).
% 0.41/0.61  thf('53', plain, ($false), inference('demod', [status(thm)], ['26', '52'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
