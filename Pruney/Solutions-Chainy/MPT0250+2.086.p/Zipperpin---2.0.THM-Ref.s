%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yI0CCHEciS

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:31:58 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   44 (  56 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :   10
%              Number of atoms          :  258 ( 377 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t45_zfmisc_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
     => ( r2_hidden @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B )
       => ( r2_hidden @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t45_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X40: $i] :
      ( ( k2_tarski @ X40 @ X40 )
      = ( k1_tarski @ X40 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X41: $i,X42: $i] :
      ( ( k1_enumset1 @ X41 @ X41 @ X42 )
      = ( k2_tarski @ X41 @ X42 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 )
      | ( r2_hidden @ X14 @ X18 )
      | ( X18
       != ( k1_enumset1 @ X17 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('4',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ X14 @ ( k1_enumset1 @ X17 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X10 != X9 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ~ ( zip_tseitin_0 @ X9 @ X11 @ X12 @ X9 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('11',plain,(
    ! [X68: $i,X69: $i] :
      ( ( r1_tarski @ X68 @ ( k3_tarski @ X69 ) )
      | ~ ( r2_hidden @ X68 @ X69 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('13',plain,(
    ! [X70: $i,X71: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X70 @ X71 ) )
      = ( k2_xboole_0 @ X70 @ X71 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['9','16'])).

thf('18',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['0','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.yI0CCHEciS
% 0.13/0.36  % Computer   : n019.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 16:32:23 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.44/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.65  % Solved by: fo/fo7.sh
% 0.44/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.65  % done 209 iterations in 0.172s
% 0.44/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.65  % SZS output start Refutation
% 0.44/0.65  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.65  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.44/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.65  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.44/0.65  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.44/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.65  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.65  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.44/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.65  thf(t45_zfmisc_1, conjecture,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.44/0.65       ( r2_hidden @ A @ B ) ))).
% 0.44/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.65    (~( ![A:$i,B:$i]:
% 0.44/0.65        ( ( r1_tarski @ ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) @ B ) =>
% 0.44/0.65          ( r2_hidden @ A @ B ) ) )),
% 0.44/0.65    inference('cnf.neg', [status(esa)], [t45_zfmisc_1])).
% 0.44/0.65  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf(t69_enumset1, axiom,
% 0.44/0.65    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.44/0.65  thf('1', plain, (![X40 : $i]: ((k2_tarski @ X40 @ X40) = (k1_tarski @ X40))),
% 0.44/0.65      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.44/0.65  thf(t70_enumset1, axiom,
% 0.44/0.65    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.44/0.65  thf('2', plain,
% 0.44/0.65      (![X41 : $i, X42 : $i]:
% 0.44/0.65         ((k1_enumset1 @ X41 @ X41 @ X42) = (k2_tarski @ X41 @ X42))),
% 0.44/0.65      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.44/0.65  thf(d1_enumset1, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.65     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.44/0.65       ( ![E:$i]:
% 0.44/0.65         ( ( r2_hidden @ E @ D ) <=>
% 0.44/0.65           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.44/0.65  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.44/0.65  thf(zf_stmt_2, axiom,
% 0.44/0.65    (![E:$i,C:$i,B:$i,A:$i]:
% 0.44/0.65     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.44/0.65       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.44/0.65  thf(zf_stmt_3, axiom,
% 0.44/0.65    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.65     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.44/0.65       ( ![E:$i]:
% 0.44/0.65         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.44/0.65  thf('3', plain,
% 0.44/0.65      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.44/0.65         ((zip_tseitin_0 @ X14 @ X15 @ X16 @ X17)
% 0.44/0.65          | (r2_hidden @ X14 @ X18)
% 0.44/0.65          | ((X18) != (k1_enumset1 @ X17 @ X16 @ X15)))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.44/0.65  thf('4', plain,
% 0.44/0.65      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.44/0.65         ((r2_hidden @ X14 @ (k1_enumset1 @ X17 @ X16 @ X15))
% 0.44/0.65          | (zip_tseitin_0 @ X14 @ X15 @ X16 @ X17))),
% 0.44/0.65      inference('simplify', [status(thm)], ['3'])).
% 0.44/0.65  thf('5', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.44/0.65          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.44/0.65      inference('sup+', [status(thm)], ['2', '4'])).
% 0.44/0.65  thf('6', plain,
% 0.44/0.65      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.44/0.65         (((X10) != (X9)) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.44/0.65  thf('7', plain,
% 0.44/0.65      (![X9 : $i, X11 : $i, X12 : $i]: ~ (zip_tseitin_0 @ X9 @ X11 @ X12 @ X9)),
% 0.44/0.65      inference('simplify', [status(thm)], ['6'])).
% 0.44/0.65  thf('8', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['5', '7'])).
% 0.44/0.65  thf('9', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.44/0.65      inference('sup+', [status(thm)], ['1', '8'])).
% 0.44/0.65  thf('10', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['5', '7'])).
% 0.44/0.65  thf(l49_zfmisc_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.44/0.65  thf('11', plain,
% 0.44/0.65      (![X68 : $i, X69 : $i]:
% 0.44/0.65         ((r1_tarski @ X68 @ (k3_tarski @ X69)) | ~ (r2_hidden @ X68 @ X69))),
% 0.44/0.65      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.44/0.65  thf('12', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (r1_tarski @ X1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.65  thf(l51_zfmisc_1, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.44/0.65  thf('13', plain,
% 0.44/0.65      (![X70 : $i, X71 : $i]:
% 0.44/0.65         ((k3_tarski @ (k2_tarski @ X70 @ X71)) = (k2_xboole_0 @ X70 @ X71))),
% 0.44/0.65      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.44/0.65  thf('14', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.44/0.65      inference('demod', [status(thm)], ['12', '13'])).
% 0.44/0.65  thf(d3_tarski, axiom,
% 0.44/0.65    (![A:$i,B:$i]:
% 0.44/0.65     ( ( r1_tarski @ A @ B ) <=>
% 0.44/0.65       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.44/0.65  thf('15', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X0 @ X1)
% 0.44/0.65          | (r2_hidden @ X0 @ X2)
% 0.44/0.65          | ~ (r1_tarski @ X1 @ X2))),
% 0.44/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.65  thf('16', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['14', '15'])).
% 0.44/0.65  thf('17', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i]:
% 0.44/0.65         (r2_hidden @ X0 @ (k2_xboole_0 @ (k1_tarski @ X0) @ X1))),
% 0.44/0.65      inference('sup-', [status(thm)], ['9', '16'])).
% 0.44/0.65  thf('18', plain,
% 0.44/0.65      ((r1_tarski @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B) @ sk_B)),
% 0.44/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.65  thf('19', plain,
% 0.44/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.65         (~ (r2_hidden @ X0 @ X1)
% 0.44/0.65          | (r2_hidden @ X0 @ X2)
% 0.44/0.65          | ~ (r1_tarski @ X1 @ X2))),
% 0.44/0.65      inference('cnf', [status(esa)], [d3_tarski])).
% 0.44/0.65  thf('20', plain,
% 0.44/0.65      (![X0 : $i]:
% 0.44/0.65         ((r2_hidden @ X0 @ sk_B)
% 0.44/0.65          | ~ (r2_hidden @ X0 @ (k2_xboole_0 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.44/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.65  thf('21', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.44/0.65      inference('sup-', [status(thm)], ['17', '20'])).
% 0.44/0.65  thf('22', plain, ($false), inference('demod', [status(thm)], ['0', '21'])).
% 0.44/0.65  
% 0.44/0.65  % SZS output end Refutation
% 0.44/0.65  
% 0.48/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
