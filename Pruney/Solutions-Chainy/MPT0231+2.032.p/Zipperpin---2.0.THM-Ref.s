%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Tx89SUkib4

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:30:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 (  51 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :   14
%              Number of atoms          :  231 ( 286 expanded)
%              Number of equality atoms :   27 (  34 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t26_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
     => ( A = C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) )
       => ( A = C ) ) ),
    inference('cnf.neg',[status(esa)],[t26_zfmisc_1])).

thf('0',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('2',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B_1 ) @ ( k1_tarski @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i] :
      ( ( X38
        = ( k1_tarski @ X37 ) )
      | ( X38 = k1_xboole_0 )
      | ~ ( r1_tarski @ X38 @ ( k1_tarski @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('4',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( ( k2_tarski @ sk_A @ sk_B_1 )
      = ( k1_tarski @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t12_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) )).

thf('5',plain,(
    ! [X40: $i,X41: $i] :
      ( r1_tarski @ ( k1_tarski @ X40 ) @ ( k2_tarski @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t12_zfmisc_1])).

thf('6',plain,
    ( ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_C_1 ) )
    | ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t6_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
     => ( A = B ) ) )).

thf('7',plain,(
    ! [X49: $i,X50: $i] :
      ( ( X50 = X49 )
      | ~ ( r1_tarski @ ( k1_tarski @ X50 ) @ ( k1_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('8',plain,
    ( ( ( k2_tarski @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( sk_A = sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    sk_A != sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_tarski @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['8','9'])).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('11',plain,(
    ! [X42: $i,X43: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X42 ) @ ( k2_tarski @ X42 @ X43 ) )
      = ( k1_tarski @ X42 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('15',plain,(
    ! [X8: $i] :
      ( r1_xboole_0 @ X8 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('16',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','16'])).

thf('18',plain,(
    ! [X49: $i,X50: $i] :
      ( ( X50 = X49 )
      | ~ ( r1_tarski @ ( k1_tarski @ X50 ) @ ( k1_tarski @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[t6_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X0 ) )
      | ( sk_A = X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X38: $i,X39: $i] :
      ( ( r1_tarski @ X38 @ ( k1_tarski @ X39 ) )
      | ( X38 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('21',plain,(
    ! [X39: $i] :
      ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ X39 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] : ( sk_A = X0 ) ),
    inference(demod,[status(thm)],['19','21'])).

thf('23',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Tx89SUkib4
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:02:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 44 iterations in 0.030s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(t26_zfmisc_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.21/0.48       ( ( A ) = ( C ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.48        ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ C ) ) =>
% 0.21/0.48          ( ( A ) = ( C ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t26_zfmisc_1])).
% 0.21/0.48  thf('0', plain, (((sk_A) != (sk_C_1))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t7_xboole_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.48          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      (![X5 : $i]: (((X5) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X5) @ X5))),
% 0.21/0.48      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      ((r1_tarski @ (k2_tarski @ sk_A @ sk_B_1) @ (k1_tarski @ sk_C_1))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(l3_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.21/0.48       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X37 : $i, X38 : $i]:
% 0.21/0.48         (((X38) = (k1_tarski @ X37))
% 0.21/0.48          | ((X38) = (k1_xboole_0))
% 0.21/0.48          | ~ (r1_tarski @ X38 @ (k1_tarski @ X37)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      ((((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.21/0.48        | ((k2_tarski @ sk_A @ sk_B_1) = (k1_tarski @ sk_C_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf(t12_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ))).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (![X40 : $i, X41 : $i]:
% 0.21/0.48         (r1_tarski @ (k1_tarski @ X40) @ (k2_tarski @ X40 @ X41))),
% 0.21/0.48      inference('cnf', [status(esa)], [t12_zfmisc_1])).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (((r1_tarski @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_C_1))
% 0.21/0.48        | ((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.21/0.48      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.48  thf(t6_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =>
% 0.21/0.48       ( ( A ) = ( B ) ) ))).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X49 : $i, X50 : $i]:
% 0.21/0.48         (((X50) = (X49))
% 0.21/0.48          | ~ (r1_tarski @ (k1_tarski @ X50) @ (k1_tarski @ X49)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      ((((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0)) | ((sk_A) = (sk_C_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain, (((sk_A) != (sk_C_1))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('10', plain, (((k2_tarski @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf(t19_zfmisc_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.21/0.48       ( k1_tarski @ A ) ))).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (![X42 : $i, X43 : $i]:
% 0.21/0.48         ((k3_xboole_0 @ (k1_tarski @ X42) @ (k2_tarski @ X42 @ X43))
% 0.21/0.48           = (k1_tarski @ X42))),
% 0.21/0.48      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (((k3_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_tarski @ sk_A))),
% 0.21/0.48      inference('sup+', [status(thm)], ['10', '11'])).
% 0.21/0.48  thf(t4_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.48            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.21/0.48          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))
% 0.21/0.48          | ~ (r1_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.21/0.48  thf('15', plain, (![X8 : $i]: (r1_xboole_0 @ X8 @ k1_xboole_0)),
% 0.21/0.48      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.21/0.48  thf('16', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_tarski @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['14', '15'])).
% 0.21/0.48  thf('17', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X49 : $i, X50 : $i]:
% 0.21/0.48         (((X50) = (X49))
% 0.21/0.48          | ~ (r1_tarski @ (k1_tarski @ X50) @ (k1_tarski @ X49)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t6_zfmisc_1])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X0)) | ((sk_A) = (X0)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X38 : $i, X39 : $i]:
% 0.21/0.48         ((r1_tarski @ X38 @ (k1_tarski @ X39)) | ((X38) != (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X39 : $i]: (r1_tarski @ k1_xboole_0 @ (k1_tarski @ X39))),
% 0.21/0.48      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.48  thf('22', plain, (![X0 : $i]: ((sk_A) = (X0))),
% 0.21/0.48      inference('demod', [status(thm)], ['19', '21'])).
% 0.21/0.48  thf('23', plain, (((sk_A) != (sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['0', '22'])).
% 0.21/0.48  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
