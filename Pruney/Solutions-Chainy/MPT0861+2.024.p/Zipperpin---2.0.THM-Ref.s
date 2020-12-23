%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FopsXfI7YW

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   47 (  64 expanded)
%              Number of leaves         :   16 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  349 ( 651 expanded)
%              Number of equality atoms :   53 (  99 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t17_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( ( k2_mcart_1 @ A )
          = D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) )
       => ( ( ( ( k1_mcart_1 @ A )
              = B )
            | ( ( k1_mcart_1 @ A )
              = C ) )
          & ( ( k2_mcart_1 @ A )
            = D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_mcart_1])).

thf('0',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t15_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) )
     => ( ( ( ( k1_mcart_1 @ A )
            = B )
          | ( ( k1_mcart_1 @ A )
            = C ) )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ) )).

thf('3',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X34 ) @ X36 )
      | ~ ( r2_hidden @ X34 @ ( k2_zfmisc_1 @ ( k2_tarski @ X35 @ X33 ) @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t15_mcart_1])).

thf('4',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t129_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( B = D ) ) ) )).

thf('5',plain,(
    ! [X28: $i,X29: $i,X30: $i,X32: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X28 @ X30 ) @ ( k2_zfmisc_1 @ X29 @ ( k1_tarski @ X32 ) ) )
      | ( X30 != X32 )
      | ~ ( r2_hidden @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t129_zfmisc_1])).

thf('6',plain,(
    ! [X28: $i,X29: $i,X32: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ( r2_hidden @ ( k4_tarski @ X28 @ X32 ) @ ( k2_zfmisc_1 @ X29 @ ( k1_tarski @ X32 ) ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ ( k2_mcart_1 @ sk_A ) @ X0 ) @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_D ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('9',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_mcart_1 @ X34 )
        = X33 )
      | ( ( k1_mcart_1 @ X34 )
        = X35 )
      | ~ ( r2_hidden @ X34 @ ( k2_zfmisc_1 @ ( k2_tarski @ X35 @ X33 ) @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t15_mcart_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 ) )
      | ( ( k1_mcart_1 @ X2 )
        = X0 )
      | ( ( k1_mcart_1 @ X2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_mcart_1 @ X2 )
        = X0 )
      | ~ ( r2_hidden @ X2 @ ( k2_zfmisc_1 @ ( k1_tarski @ X0 ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ ( k2_mcart_1 @ sk_A ) @ X0 ) )
      = sk_D ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf(t7_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) )
        = B )
      & ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) )
        = A ) ) )).

thf('13',plain,(
    ! [X37: $i,X38: $i] :
      ( ( k1_mcart_1 @ ( k4_tarski @ X37 @ X38 ) )
      = X37 ) ),
    inference(cnf,[status(esa)],[t7_mcart_1])).

thf('14',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ( sk_D != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['15'])).

thf('20',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_mcart_1 @ X34 )
        = X33 )
      | ( ( k1_mcart_1 @ X34 )
        = X35 )
      | ~ ( r2_hidden @ X34 @ ( k2_zfmisc_1 @ ( k2_tarski @ X35 @ X33 ) @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[t15_mcart_1])).

thf('22',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( ( sk_C != sk_C )
      | ( ( k1_mcart_1 @ sk_A )
        = sk_B ) )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['15'])).

thf('27',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k1_mcart_1 @ sk_A )
       != sk_C )
      & ( ( k1_mcart_1 @ sk_A )
       != sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k1_mcart_1 @ sk_A )
      = sk_B )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','18','19','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FopsXfI7YW
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:07:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 41 iterations in 0.020s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.47  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(t17_mcart_1, conjecture,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( r2_hidden @
% 0.21/0.47         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.21/0.47       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.21/0.47         ( ( k2_mcart_1 @ A ) = ( D ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47        ( ( r2_hidden @
% 0.21/0.47            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.21/0.47          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.21/0.47            ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t17_mcart_1])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | ~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      ((r2_hidden @ sk_A @ 
% 0.21/0.47        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t15_mcart_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ D ) ) =>
% 0.21/0.47       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.21/0.47         ( r2_hidden @ ( k2_mcart_1 @ A ) @ D ) ) ))).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.47         ((r2_hidden @ (k2_mcart_1 @ X34) @ X36)
% 0.21/0.47          | ~ (r2_hidden @ X34 @ (k2_zfmisc_1 @ (k2_tarski @ X35 @ X33) @ X36)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t15_mcart_1])).
% 0.21/0.47  thf('4', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_D))),
% 0.21/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.47  thf(t129_zfmisc_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.47     ( ( r2_hidden @
% 0.21/0.47         ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ ( k1_tarski @ D ) ) ) <=>
% 0.21/0.47       ( ( r2_hidden @ A @ C ) & ( ( B ) = ( D ) ) ) ))).
% 0.21/0.47  thf('5', plain,
% 0.21/0.47      (![X28 : $i, X29 : $i, X30 : $i, X32 : $i]:
% 0.21/0.47         ((r2_hidden @ (k4_tarski @ X28 @ X30) @ 
% 0.21/0.47           (k2_zfmisc_1 @ X29 @ (k1_tarski @ X32)))
% 0.21/0.47          | ((X30) != (X32))
% 0.21/0.47          | ~ (r2_hidden @ X28 @ X29))),
% 0.21/0.47      inference('cnf', [status(esa)], [t129_zfmisc_1])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      (![X28 : $i, X29 : $i, X32 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X28 @ X29)
% 0.21/0.47          | (r2_hidden @ (k4_tarski @ X28 @ X32) @ 
% 0.21/0.47             (k2_zfmisc_1 @ X29 @ (k1_tarski @ X32))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (r2_hidden @ (k4_tarski @ (k2_mcart_1 @ sk_A) @ X0) @ 
% 0.21/0.47          (k2_zfmisc_1 @ (k1_tarski @ sk_D) @ (k1_tarski @ X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.47  thf(t69_enumset1, axiom,
% 0.21/0.47    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.47  thf('8', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.47  thf('9', plain,
% 0.21/0.47      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.47         (((k1_mcart_1 @ X34) = (X33))
% 0.21/0.47          | ((k1_mcart_1 @ X34) = (X35))
% 0.21/0.47          | ~ (r2_hidden @ X34 @ (k2_zfmisc_1 @ (k2_tarski @ X35 @ X33) @ X36)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t15_mcart_1])).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ (k1_tarski @ X0) @ X1))
% 0.21/0.47          | ((k1_mcart_1 @ X2) = (X0))
% 0.21/0.47          | ((k1_mcart_1 @ X2) = (X0)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (((k1_mcart_1 @ X2) = (X0))
% 0.21/0.47          | ~ (r2_hidden @ X2 @ (k2_zfmisc_1 @ (k1_tarski @ X0) @ X1)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['10'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         ((k1_mcart_1 @ (k4_tarski @ (k2_mcart_1 @ sk_A) @ X0)) = (sk_D))),
% 0.21/0.47      inference('sup-', [status(thm)], ['7', '11'])).
% 0.21/0.47  thf(t7_mcart_1, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( k2_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( B ) ) & 
% 0.21/0.47       ( ( k1_mcart_1 @ ( k4_tarski @ A @ B ) ) = ( A ) ) ))).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X37 : $i, X38 : $i]: ((k1_mcart_1 @ (k4_tarski @ X37 @ X38)) = (X37))),
% 0.21/0.47      inference('cnf', [status(esa)], [t7_mcart_1])).
% 0.21/0.47  thf('14', plain, (((k2_mcart_1 @ sk_A) = (sk_D))),
% 0.21/0.47      inference('demod', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain,
% 0.21/0.47      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('16', plain,
% 0.21/0.47      ((((k2_mcart_1 @ sk_A) != (sk_D)))
% 0.21/0.47         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.21/0.47      inference('split', [status(esa)], ['15'])).
% 0.21/0.47  thf('17', plain,
% 0.21/0.47      ((((sk_D) != (sk_D))) <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['14', '16'])).
% 0.21/0.47  thf('18', plain, ((((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | ~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.21/0.47      inference('split', [status(esa)], ['15'])).
% 0.21/0.47  thf('20', plain,
% 0.21/0.47      ((r2_hidden @ sk_A @ 
% 0.21/0.47        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.47         (((k1_mcart_1 @ X34) = (X33))
% 0.21/0.47          | ((k1_mcart_1 @ X34) = (X35))
% 0.21/0.47          | ~ (r2_hidden @ X34 @ (k2_zfmisc_1 @ (k2_tarski @ X35 @ X33) @ X36)))),
% 0.21/0.47      inference('cnf', [status(esa)], [t15_mcart_1])).
% 0.21/0.47  thf('22', plain,
% 0.21/0.47      ((((k1_mcart_1 @ sk_A) = (sk_B)) | ((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.47  thf('23', plain,
% 0.21/0.47      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 0.21/0.47         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.47      inference('split', [status(esa)], ['0'])).
% 0.21/0.47  thf('24', plain,
% 0.21/0.47      (((((sk_C) != (sk_C)) | ((k1_mcart_1 @ sk_A) = (sk_B))))
% 0.21/0.47         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.47  thf('25', plain,
% 0.21/0.47      ((((k1_mcart_1 @ sk_A) = (sk_B))) <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.21/0.47      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.47  thf('26', plain,
% 0.21/0.47      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.21/0.47         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.47      inference('split', [status(esa)], ['15'])).
% 0.21/0.47  thf('27', plain,
% 0.21/0.47      ((((sk_B) != (sk_B)))
% 0.21/0.47         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))) & 
% 0.21/0.47             ~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.21/0.47      inference('sup-', [status(thm)], ['25', '26'])).
% 0.21/0.47  thf('28', plain,
% 0.21/0.47      ((((k1_mcart_1 @ sk_A) = (sk_B))) | (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.21/0.47      inference('simplify', [status(thm)], ['27'])).
% 0.21/0.47  thf('29', plain, ($false),
% 0.21/0.47      inference('sat_resolution*', [status(thm)], ['1', '18', '19', '28'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
