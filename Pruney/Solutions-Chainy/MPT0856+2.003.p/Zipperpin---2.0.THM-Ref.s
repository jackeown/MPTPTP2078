%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zligvVpDMF

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:42 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   54 (  70 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :   10
%              Number of atoms          :  313 ( 510 expanded)
%              Number of equality atoms :   17 (  29 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('0',plain,(
    ! [X37: $i] :
      ( ( k1_ordinal1 @ X37 )
      = ( k2_xboole_0 @ X37 @ ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t12_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) )
       => ( ( ( k1_mcart_1 @ A )
            = B )
          & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_mcart_1])).

thf('1',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('2',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X43 ) @ X44 )
      | ~ ( r2_hidden @ X43 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('3',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['3','5'])).

thf('7',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_ordinal1 @ sk_B ) ),
    inference('sup+',[status(thm)],['0','6'])).

thf(t13_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) )
    <=> ( ( r2_hidden @ A @ B )
        | ( A = B ) ) ) )).

thf('8',plain,(
    ! [X38: $i,X39: $i] :
      ( ( X39 = X38 )
      | ( r2_hidden @ X39 @ X38 )
      | ~ ( r2_hidden @ X39 @ ( k1_ordinal1 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[t13_ordinal1])).

thf('9',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X43 ) @ X45 )
      | ~ ( r2_hidden @ X43 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('14',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 )
   <= ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('16',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ~ ( r2_hidden @ ( k2_mcart_1 @ sk_A ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['10'])).

thf('18',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['16','17'])).

thf('19',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['11','18'])).

thf('20',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['9','19'])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('21',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X26 ) @ X27 )
      | ( r2_hidden @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf('22',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('23',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ sk_B @ X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    r2_hidden @ sk_B @ sk_B ),
    inference('sup-',[status(thm)],['20','25'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('27',plain,(
    ! [X41: $i,X42: $i] :
      ( ~ ( r2_hidden @ X41 @ X42 )
      | ~ ( r1_tarski @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('28',plain,(
    ~ ( r1_tarski @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('30',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    $false ),
    inference(demod,[status(thm)],['28','30'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.zligvVpDMF
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:07:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.40/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.62  % Solved by: fo/fo7.sh
% 0.40/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.62  % done 304 iterations in 0.160s
% 0.40/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.62  % SZS output start Refutation
% 0.40/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.62  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.40/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.62  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.40/0.62  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.40/0.62  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.40/0.62  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.40/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.62  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.62  thf(d1_ordinal1, axiom,
% 0.40/0.62    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.40/0.62  thf('0', plain,
% 0.40/0.62      (![X37 : $i]:
% 0.40/0.62         ((k1_ordinal1 @ X37) = (k2_xboole_0 @ X37 @ (k1_tarski @ X37)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.40/0.62  thf(t12_mcart_1, conjecture,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.40/0.62       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.40/0.62         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.40/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.62        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ C ) ) =>
% 0.40/0.62          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.40/0.62            ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )),
% 0.40/0.62    inference('cnf.neg', [status(esa)], [t12_mcart_1])).
% 0.40/0.62  thf('1', plain,
% 0.40/0.62      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C_1))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf(t10_mcart_1, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.40/0.62       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.40/0.62         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.40/0.62  thf('2', plain,
% 0.40/0.62      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.40/0.62         ((r2_hidden @ (k1_mcart_1 @ X43) @ X44)
% 0.40/0.62          | ~ (r2_hidden @ X43 @ (k2_zfmisc_1 @ X44 @ X45)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.40/0.62  thf('3', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.62  thf(d3_xboole_0, axiom,
% 0.40/0.62    (![A:$i,B:$i,C:$i]:
% 0.40/0.62     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.40/0.62       ( ![D:$i]:
% 0.40/0.62         ( ( r2_hidden @ D @ C ) <=>
% 0.40/0.62           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.40/0.62  thf('4', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.62          | (r2_hidden @ X0 @ X2)
% 0.40/0.62          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.40/0.62  thf('5', plain,
% 0.40/0.62      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.40/0.62         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.40/0.62      inference('simplify', [status(thm)], ['4'])).
% 0.40/0.62  thf('6', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (r2_hidden @ (k1_mcart_1 @ sk_A) @ 
% 0.40/0.62          (k2_xboole_0 @ X0 @ (k1_tarski @ sk_B)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['3', '5'])).
% 0.40/0.62  thf('7', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_ordinal1 @ sk_B))),
% 0.40/0.62      inference('sup+', [status(thm)], ['0', '6'])).
% 0.40/0.62  thf(t13_ordinal1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( r2_hidden @ A @ ( k1_ordinal1 @ B ) ) <=>
% 0.40/0.62       ( ( r2_hidden @ A @ B ) | ( ( A ) = ( B ) ) ) ))).
% 0.40/0.62  thf('8', plain,
% 0.40/0.62      (![X38 : $i, X39 : $i]:
% 0.40/0.62         (((X39) = (X38))
% 0.40/0.62          | (r2_hidden @ X39 @ X38)
% 0.40/0.62          | ~ (r2_hidden @ X39 @ (k1_ordinal1 @ X38)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t13_ordinal1])).
% 0.40/0.62  thf('9', plain,
% 0.40/0.62      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)
% 0.40/0.62        | ((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.40/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.40/0.62  thf('10', plain,
% 0.40/0.62      ((((k1_mcart_1 @ sk_A) != (sk_B))
% 0.40/0.62        | ~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('11', plain,
% 0.40/0.62      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.40/0.62         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.40/0.62      inference('split', [status(esa)], ['10'])).
% 0.40/0.62  thf('12', plain,
% 0.40/0.62      ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ sk_C_1))),
% 0.40/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.62  thf('13', plain,
% 0.40/0.62      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.40/0.62         ((r2_hidden @ (k2_mcart_1 @ X43) @ X45)
% 0.40/0.62          | ~ (r2_hidden @ X43 @ (k2_zfmisc_1 @ X44 @ X45)))),
% 0.40/0.62      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.40/0.62  thf('14', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1)),
% 0.40/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.40/0.62  thf('15', plain,
% 0.40/0.62      ((~ (r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))
% 0.40/0.62         <= (~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1)))),
% 0.40/0.62      inference('split', [status(esa)], ['10'])).
% 0.40/0.62  thf('16', plain, (((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))),
% 0.40/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.62  thf('17', plain,
% 0.40/0.62      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.40/0.62       ~ ((r2_hidden @ (k2_mcart_1 @ sk_A) @ sk_C_1))),
% 0.40/0.62      inference('split', [status(esa)], ['10'])).
% 0.40/0.62  thf('18', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.40/0.62      inference('sat_resolution*', [status(thm)], ['16', '17'])).
% 0.40/0.62  thf('19', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.40/0.62      inference('simpl_trail', [status(thm)], ['11', '18'])).
% 0.40/0.62  thf('20', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ sk_B)),
% 0.40/0.62      inference('simplify_reflect-', [status(thm)], ['9', '19'])).
% 0.40/0.62  thf(l27_zfmisc_1, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.40/0.62  thf('21', plain,
% 0.40/0.62      (![X26 : $i, X27 : $i]:
% 0.40/0.62         ((r1_xboole_0 @ (k1_tarski @ X26) @ X27) | (r2_hidden @ X26 @ X27))),
% 0.40/0.62      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.40/0.62  thf('22', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.40/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.62  thf(t3_xboole_0, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.40/0.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.62            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.40/0.62  thf('23', plain,
% 0.40/0.62      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X8 @ X6)
% 0.40/0.62          | ~ (r2_hidden @ X8 @ X9)
% 0.40/0.62          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.40/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.62  thf('24', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         (~ (r1_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 0.40/0.62          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['22', '23'])).
% 0.40/0.62  thf('25', plain,
% 0.40/0.62      (![X0 : $i]:
% 0.40/0.62         ((r2_hidden @ sk_B @ X0) | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ X0))),
% 0.40/0.62      inference('sup-', [status(thm)], ['21', '24'])).
% 0.40/0.62  thf('26', plain, ((r2_hidden @ sk_B @ sk_B)),
% 0.40/0.62      inference('sup-', [status(thm)], ['20', '25'])).
% 0.40/0.62  thf(t7_ordinal1, axiom,
% 0.40/0.62    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.62  thf('27', plain,
% 0.40/0.62      (![X41 : $i, X42 : $i]:
% 0.40/0.62         (~ (r2_hidden @ X41 @ X42) | ~ (r1_tarski @ X42 @ X41))),
% 0.40/0.62      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.40/0.62  thf('28', plain, (~ (r1_tarski @ sk_B @ sk_B)),
% 0.40/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.40/0.62  thf(d10_xboole_0, axiom,
% 0.40/0.62    (![A:$i,B:$i]:
% 0.40/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.40/0.62  thf('29', plain,
% 0.40/0.62      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.40/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.40/0.62  thf('30', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.40/0.62      inference('simplify', [status(thm)], ['29'])).
% 0.40/0.62  thf('31', plain, ($false), inference('demod', [status(thm)], ['28', '30'])).
% 0.40/0.62  
% 0.40/0.62  % SZS output end Refutation
% 0.40/0.62  
% 0.49/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
