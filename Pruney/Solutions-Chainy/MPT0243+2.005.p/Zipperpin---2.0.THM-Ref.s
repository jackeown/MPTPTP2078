%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Jwq01vQka3

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:09 EST 2020

% Result     : Theorem 1.92s
% Output     : Refutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   62 (  92 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :  458 ( 763 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X42: $i,X43: $i] :
      ( r1_tarski @ ( k1_tarski @ X42 ) @ ( k2_tarski @ X42 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('3',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r2_hidden @ X39 @ X40 )
      | ~ ( r1_tarski @ ( k1_tarski @ X39 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('7',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf('9',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
    | ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('13',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    ! [X39: $i,X41: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X39 ) @ X41 )
      | ~ ( r2_hidden @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('16',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_B ) @ sk_C_1 )
   <= ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( r2_hidden @ sk_A @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference(split,[status(esa)],['0'])).

thf('18',plain,(
    ! [X39: $i,X41: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X39 ) @ X41 )
      | ~ ( r2_hidden @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('19',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ sk_C_1 )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t8_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B ) )
     => ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ) )).

thf('20',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ~ ( r1_tarski @ X22 @ X21 )
      | ( r1_tarski @ ( k2_xboole_0 @ X20 @ X22 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t8_xboole_1])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 ) @ sk_C_1 )
        | ~ ( r1_tarski @ X0 @ sk_C_1 ) )
   <= ( r2_hidden @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) @ sk_C_1 )
   <= ( ( r2_hidden @ sk_A @ sk_C_1 )
      & ( r2_hidden @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('23',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k2_tarski @ X35 @ X36 )
      = ( k2_xboole_0 @ ( k1_tarski @ X35 ) @ ( k1_tarski @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('24',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ( ( r2_hidden @ sk_A @ sk_C_1 )
      & ( r2_hidden @ sk_B @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
   <= ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('26',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_C_1 )
    | ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['13'])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_enumset1 @ X37 @ X37 @ X38 )
      = ( k2_tarski @ X37 @ X38 ) ) ),
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

thf('29',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 )
      | ( r2_hidden @ X28 @ X32 )
      | ( X32
       != ( k1_enumset1 @ X31 @ X30 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( r2_hidden @ X28 @ ( k1_enumset1 @ X31 @ X30 @ X29 ) )
      | ( zip_tseitin_0 @ X28 @ X29 @ X30 @ X31 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['28','30'])).

thf('32',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X24 != X25 )
      | ~ ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('33',plain,(
    ! [X23: $i,X25: $i,X26: $i] :
      ~ ( zip_tseitin_0 @ X25 @ X25 @ X26 @ X23 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ X0 @ sk_C_1 )
        | ~ ( r2_hidden @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('36',plain,
    ( ( r2_hidden @ sk_B @ sk_C_1 )
   <= ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( r2_hidden @ sk_B @ sk_C_1 )
   <= ~ ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference(split,[status(esa)],['9'])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    | ( r2_hidden @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','11','12','26','27','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Jwq01vQka3
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:49:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.92/2.16  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.92/2.16  % Solved by: fo/fo7.sh
% 1.92/2.16  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.92/2.16  % done 2908 iterations in 1.702s
% 1.92/2.16  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.92/2.16  % SZS output start Refutation
% 1.92/2.16  thf(sk_A_type, type, sk_A: $i).
% 1.92/2.16  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.92/2.16  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.92/2.16  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.92/2.16  thf(sk_B_type, type, sk_B: $i).
% 1.92/2.16  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.92/2.16  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 1.92/2.16  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.92/2.16  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.92/2.16  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.92/2.16  thf(t38_zfmisc_1, conjecture,
% 1.92/2.16    (![A:$i,B:$i,C:$i]:
% 1.92/2.16     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 1.92/2.16       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 1.92/2.16  thf(zf_stmt_0, negated_conjecture,
% 1.92/2.16    (~( ![A:$i,B:$i,C:$i]:
% 1.92/2.16        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 1.92/2.16          ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ) )),
% 1.92/2.16    inference('cnf.neg', [status(esa)], [t38_zfmisc_1])).
% 1.92/2.16  thf('0', plain,
% 1.92/2.16      (((r2_hidden @ sk_A @ sk_C_1)
% 1.92/2.16        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 1.92/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.16  thf('1', plain,
% 1.92/2.16      (((r2_hidden @ sk_A @ sk_C_1)) | 
% 1.92/2.16       ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 1.92/2.16      inference('split', [status(esa)], ['0'])).
% 1.92/2.16  thf(t12_zfmisc_1, axiom,
% 1.92/2.16    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 1.92/2.16  thf('2', plain,
% 1.92/2.16      (![X42 : $i, X43 : $i]:
% 1.92/2.16         (r1_tarski @ (k1_tarski @ X42) @ (k2_tarski @ X42 @ X43))),
% 1.92/2.16      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 1.92/2.16  thf(l1_zfmisc_1, axiom,
% 1.92/2.16    (![A:$i,B:$i]:
% 1.92/2.16     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 1.92/2.16  thf('3', plain,
% 1.92/2.16      (![X39 : $i, X40 : $i]:
% 1.92/2.16         ((r2_hidden @ X39 @ X40) | ~ (r1_tarski @ (k1_tarski @ X39) @ X40))),
% 1.92/2.16      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.92/2.16  thf('4', plain,
% 1.92/2.16      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 1.92/2.16      inference('sup-', [status(thm)], ['2', '3'])).
% 1.92/2.16  thf('5', plain,
% 1.92/2.16      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 1.92/2.16         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 1.92/2.16      inference('split', [status(esa)], ['0'])).
% 1.92/2.16  thf(d3_tarski, axiom,
% 1.92/2.16    (![A:$i,B:$i]:
% 1.92/2.16     ( ( r1_tarski @ A @ B ) <=>
% 1.92/2.16       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.92/2.16  thf('6', plain,
% 1.92/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.92/2.16         (~ (r2_hidden @ X0 @ X1)
% 1.92/2.16          | (r2_hidden @ X0 @ X2)
% 1.92/2.16          | ~ (r1_tarski @ X1 @ X2))),
% 1.92/2.16      inference('cnf', [status(esa)], [d3_tarski])).
% 1.92/2.16  thf('7', plain,
% 1.92/2.16      ((![X0 : $i]:
% 1.92/2.16          ((r2_hidden @ X0 @ sk_C_1)
% 1.92/2.16           | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))))
% 1.92/2.16         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 1.92/2.16      inference('sup-', [status(thm)], ['5', '6'])).
% 1.92/2.16  thf('8', plain,
% 1.92/2.16      (((r2_hidden @ sk_A @ sk_C_1))
% 1.92/2.16         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 1.92/2.16      inference('sup-', [status(thm)], ['4', '7'])).
% 1.92/2.16  thf('9', plain,
% 1.92/2.16      ((~ (r2_hidden @ sk_B @ sk_C_1)
% 1.92/2.16        | ~ (r2_hidden @ sk_A @ sk_C_1)
% 1.92/2.16        | ~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 1.92/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.16  thf('10', plain,
% 1.92/2.16      ((~ (r2_hidden @ sk_A @ sk_C_1)) <= (~ ((r2_hidden @ sk_A @ sk_C_1)))),
% 1.92/2.16      inference('split', [status(esa)], ['9'])).
% 1.92/2.16  thf('11', plain,
% 1.92/2.16      (((r2_hidden @ sk_A @ sk_C_1)) | 
% 1.92/2.16       ~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 1.92/2.16      inference('sup-', [status(thm)], ['8', '10'])).
% 1.92/2.16  thf('12', plain,
% 1.92/2.16      (~ ((r2_hidden @ sk_A @ sk_C_1)) | 
% 1.92/2.16       ~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)) | 
% 1.92/2.16       ~ ((r2_hidden @ sk_B @ sk_C_1))),
% 1.92/2.16      inference('split', [status(esa)], ['9'])).
% 1.92/2.16  thf('13', plain,
% 1.92/2.16      (((r2_hidden @ sk_B @ sk_C_1)
% 1.92/2.16        | (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))),
% 1.92/2.16      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.92/2.16  thf('14', plain,
% 1.92/2.16      (((r2_hidden @ sk_B @ sk_C_1)) <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 1.92/2.16      inference('split', [status(esa)], ['13'])).
% 1.92/2.16  thf('15', plain,
% 1.92/2.16      (![X39 : $i, X41 : $i]:
% 1.92/2.16         ((r1_tarski @ (k1_tarski @ X39) @ X41) | ~ (r2_hidden @ X39 @ X41))),
% 1.92/2.16      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.92/2.16  thf('16', plain,
% 1.92/2.16      (((r1_tarski @ (k1_tarski @ sk_B) @ sk_C_1))
% 1.92/2.16         <= (((r2_hidden @ sk_B @ sk_C_1)))),
% 1.92/2.16      inference('sup-', [status(thm)], ['14', '15'])).
% 1.92/2.16  thf('17', plain,
% 1.92/2.16      (((r2_hidden @ sk_A @ sk_C_1)) <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 1.92/2.16      inference('split', [status(esa)], ['0'])).
% 1.92/2.16  thf('18', plain,
% 1.92/2.16      (![X39 : $i, X41 : $i]:
% 1.92/2.16         ((r1_tarski @ (k1_tarski @ X39) @ X41) | ~ (r2_hidden @ X39 @ X41))),
% 1.92/2.16      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 1.92/2.16  thf('19', plain,
% 1.92/2.16      (((r1_tarski @ (k1_tarski @ sk_A) @ sk_C_1))
% 1.92/2.16         <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 1.92/2.16      inference('sup-', [status(thm)], ['17', '18'])).
% 1.92/2.16  thf(t8_xboole_1, axiom,
% 1.92/2.16    (![A:$i,B:$i,C:$i]:
% 1.92/2.16     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) ) =>
% 1.92/2.16       ( r1_tarski @ ( k2_xboole_0 @ A @ C ) @ B ) ))).
% 1.92/2.16  thf('20', plain,
% 1.92/2.16      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.92/2.16         (~ (r1_tarski @ X20 @ X21)
% 1.92/2.16          | ~ (r1_tarski @ X22 @ X21)
% 1.92/2.16          | (r1_tarski @ (k2_xboole_0 @ X20 @ X22) @ X21))),
% 1.92/2.16      inference('cnf', [status(esa)], [t8_xboole_1])).
% 1.92/2.16  thf('21', plain,
% 1.92/2.16      ((![X0 : $i]:
% 1.92/2.16          ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ X0) @ sk_C_1)
% 1.92/2.16           | ~ (r1_tarski @ X0 @ sk_C_1)))
% 1.92/2.16         <= (((r2_hidden @ sk_A @ sk_C_1)))),
% 1.92/2.16      inference('sup-', [status(thm)], ['19', '20'])).
% 1.92/2.16  thf('22', plain,
% 1.92/2.16      (((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)) @ 
% 1.92/2.16         sk_C_1))
% 1.92/2.16         <= (((r2_hidden @ sk_A @ sk_C_1)) & ((r2_hidden @ sk_B @ sk_C_1)))),
% 1.92/2.16      inference('sup-', [status(thm)], ['16', '21'])).
% 1.92/2.16  thf(t41_enumset1, axiom,
% 1.92/2.16    (![A:$i,B:$i]:
% 1.92/2.16     ( ( k2_tarski @ A @ B ) =
% 1.92/2.16       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 1.92/2.16  thf('23', plain,
% 1.92/2.16      (![X35 : $i, X36 : $i]:
% 1.92/2.16         ((k2_tarski @ X35 @ X36)
% 1.92/2.16           = (k2_xboole_0 @ (k1_tarski @ X35) @ (k1_tarski @ X36)))),
% 1.92/2.16      inference('cnf', [status(esa)], [t41_enumset1])).
% 1.92/2.16  thf('24', plain,
% 1.92/2.16      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 1.92/2.16         <= (((r2_hidden @ sk_A @ sk_C_1)) & ((r2_hidden @ sk_B @ sk_C_1)))),
% 1.92/2.16      inference('demod', [status(thm)], ['22', '23'])).
% 1.92/2.16  thf('25', plain,
% 1.92/2.16      ((~ (r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1))
% 1.92/2.16         <= (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 1.92/2.16      inference('split', [status(esa)], ['9'])).
% 1.92/2.16  thf('26', plain,
% 1.92/2.16      (~ ((r2_hidden @ sk_A @ sk_C_1)) | 
% 1.92/2.16       ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)) | 
% 1.92/2.16       ~ ((r2_hidden @ sk_B @ sk_C_1))),
% 1.92/2.16      inference('sup-', [status(thm)], ['24', '25'])).
% 1.92/2.16  thf('27', plain,
% 1.92/2.16      (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)) | 
% 1.92/2.16       ((r2_hidden @ sk_B @ sk_C_1))),
% 1.92/2.16      inference('split', [status(esa)], ['13'])).
% 1.92/2.16  thf(t70_enumset1, axiom,
% 1.92/2.16    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.92/2.16  thf('28', plain,
% 1.92/2.16      (![X37 : $i, X38 : $i]:
% 1.92/2.16         ((k1_enumset1 @ X37 @ X37 @ X38) = (k2_tarski @ X37 @ X38))),
% 1.92/2.16      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.92/2.16  thf(d1_enumset1, axiom,
% 1.92/2.16    (![A:$i,B:$i,C:$i,D:$i]:
% 1.92/2.16     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.92/2.16       ( ![E:$i]:
% 1.92/2.16         ( ( r2_hidden @ E @ D ) <=>
% 1.92/2.16           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 1.92/2.16  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 1.92/2.16  thf(zf_stmt_2, axiom,
% 1.92/2.16    (![E:$i,C:$i,B:$i,A:$i]:
% 1.92/2.16     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 1.92/2.16       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 1.92/2.16  thf(zf_stmt_3, axiom,
% 1.92/2.16    (![A:$i,B:$i,C:$i,D:$i]:
% 1.92/2.16     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.92/2.16       ( ![E:$i]:
% 1.92/2.16         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 1.92/2.16  thf('29', plain,
% 1.92/2.16      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.92/2.16         ((zip_tseitin_0 @ X28 @ X29 @ X30 @ X31)
% 1.92/2.16          | (r2_hidden @ X28 @ X32)
% 1.92/2.16          | ((X32) != (k1_enumset1 @ X31 @ X30 @ X29)))),
% 1.92/2.16      inference('cnf', [status(esa)], [zf_stmt_3])).
% 1.92/2.16  thf('30', plain,
% 1.92/2.16      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 1.92/2.16         ((r2_hidden @ X28 @ (k1_enumset1 @ X31 @ X30 @ X29))
% 1.92/2.16          | (zip_tseitin_0 @ X28 @ X29 @ X30 @ X31))),
% 1.92/2.16      inference('simplify', [status(thm)], ['29'])).
% 1.92/2.16  thf('31', plain,
% 1.92/2.16      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.92/2.16         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 1.92/2.16          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 1.92/2.16      inference('sup+', [status(thm)], ['28', '30'])).
% 1.92/2.16  thf('32', plain,
% 1.92/2.16      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 1.92/2.16         (((X24) != (X25)) | ~ (zip_tseitin_0 @ X24 @ X25 @ X26 @ X23))),
% 1.92/2.16      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.92/2.16  thf('33', plain,
% 1.92/2.16      (![X23 : $i, X25 : $i, X26 : $i]:
% 1.92/2.16         ~ (zip_tseitin_0 @ X25 @ X25 @ X26 @ X23)),
% 1.92/2.16      inference('simplify', [status(thm)], ['32'])).
% 1.92/2.16  thf('34', plain,
% 1.92/2.16      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X0 @ X1))),
% 1.92/2.16      inference('sup-', [status(thm)], ['31', '33'])).
% 1.92/2.16  thf('35', plain,
% 1.92/2.16      ((![X0 : $i]:
% 1.92/2.16          ((r2_hidden @ X0 @ sk_C_1)
% 1.92/2.16           | ~ (r2_hidden @ X0 @ (k2_tarski @ sk_A @ sk_B))))
% 1.92/2.16         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 1.92/2.16      inference('sup-', [status(thm)], ['5', '6'])).
% 1.92/2.16  thf('36', plain,
% 1.92/2.16      (((r2_hidden @ sk_B @ sk_C_1))
% 1.92/2.16         <= (((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)))),
% 1.92/2.16      inference('sup-', [status(thm)], ['34', '35'])).
% 1.92/2.16  thf('37', plain,
% 1.92/2.16      ((~ (r2_hidden @ sk_B @ sk_C_1)) <= (~ ((r2_hidden @ sk_B @ sk_C_1)))),
% 1.92/2.16      inference('split', [status(esa)], ['9'])).
% 1.92/2.16  thf('38', plain,
% 1.92/2.16      (~ ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1)) | 
% 1.92/2.16       ((r2_hidden @ sk_B @ sk_C_1))),
% 1.92/2.16      inference('sup-', [status(thm)], ['36', '37'])).
% 1.92/2.16  thf('39', plain, ($false),
% 1.92/2.16      inference('sat_resolution*', [status(thm)],
% 1.92/2.16                ['1', '11', '12', '26', '27', '38'])).
% 1.92/2.16  
% 1.92/2.16  % SZS output end Refutation
% 1.92/2.16  
% 1.92/2.17  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
