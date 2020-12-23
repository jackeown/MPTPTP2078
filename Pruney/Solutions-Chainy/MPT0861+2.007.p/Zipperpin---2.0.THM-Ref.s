%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wKqVoDN7ss

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 136 expanded)
%              Number of leaves         :   16 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  356 (1353 expanded)
%              Number of equality atoms :   51 ( 189 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X24 ) @ X25 )
      | ~ ( r2_hidden @ X24 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t23_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X18 @ X19 ) @ ( k1_tarski @ X19 ) )
        = ( k1_tarski @ X18 ) )
      | ( X18 = X19 ) ) ),
    inference(cnf,[status(esa)],[t23_zfmisc_1])).

thf('4',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k2_tarski @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i,X23: $i] :
      ( ( r2_hidden @ X20 @ ( k4_xboole_0 @ X21 @ ( k1_tarski @ X23 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k1_mcart_1 @ sk_A )
        = X0 )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k4_xboole_0 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( sk_B = sk_C )
    | ( ( k1_mcart_1 @ sk_A )
      = sk_C ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['8'])).

thf('10',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k2_tarski @ sk_B @ sk_C ) @ ( k1_tarski @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X24 ) @ X26 )
      | ~ ( r2_hidden @ X24 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('12',plain,(
    r2_hidden @ ( k2_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ ( k2_tarski @ X18 @ X19 ) @ ( k1_tarski @ X19 ) )
        = ( k1_tarski @ X18 ) )
      | ( X18 = X19 ) ) ),
    inference(cnf,[status(esa)],[t23_zfmisc_1])).

thf('14',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( X20 != X22 )
      | ~ ( r2_hidden @ X20 @ ( k4_xboole_0 @ X21 @ ( k1_tarski @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('15',plain,(
    ! [X21: $i,X22: $i] :
      ~ ( r2_hidden @ X22 @ ( k4_xboole_0 @ X21 @ ( k1_tarski @ X22 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,
    ( sk_D
    = ( k2_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','16'])).

thf('18',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['18'])).

thf('20',plain,
    ( ( sk_D != sk_D )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( k2_mcart_1 @ sk_A )
    = sk_D ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_C )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['8'])).

thf('23',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference('sat_resolution*',[status(thm)],['21','22'])).

thf('24',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_C ),
    inference(simpl_trail,[status(thm)],['9','23'])).

thf('25',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) )
    | ( sk_B = sk_C ) ),
    inference('simplify_reflect-',[status(thm)],['7','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('27',plain,
    ( ( sk_B = sk_C )
    | ( sk_B
      = ( k1_mcart_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['18'])).

thf('29',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D ) ),
    inference(split,[status(esa)],['18'])).

thf('30',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['21','29'])).

thf('31',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['28','30'])).

thf('32',plain,(
    sk_B = sk_C ),
    inference('simplify_reflect-',[status(thm)],['27','31'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('33',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['2','32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('36',plain,
    ( sk_B
    = ( k1_mcart_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['28','30'])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wKqVoDN7ss
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 58 iterations in 0.029s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.49  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.49  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.49  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.49  thf(t17_mcart_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( r2_hidden @
% 0.20/0.49         A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.20/0.49       ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.20/0.49         ( ( k2_mcart_1 @ A ) = ( D ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49        ( ( r2_hidden @
% 0.20/0.49            A @ ( k2_zfmisc_1 @ ( k2_tarski @ B @ C ) @ ( k1_tarski @ D ) ) ) =>
% 0.20/0.49          ( ( ( ( k1_mcart_1 @ A ) = ( B ) ) | ( ( k1_mcart_1 @ A ) = ( C ) ) ) & 
% 0.20/0.49            ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t17_mcart_1])).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      ((r2_hidden @ sk_A @ 
% 0.20/0.49        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t10_mcart_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.20/0.49       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.20/0.49         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.49         ((r2_hidden @ (k1_mcart_1 @ X24) @ X25)
% 0.20/0.49          | ~ (r2_hidden @ X24 @ (k2_zfmisc_1 @ X25 @ X26)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf(t23_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( A ) != ( B ) ) =>
% 0.20/0.49       ( ( k4_xboole_0 @ ( k2_tarski @ A @ B ) @ ( k1_tarski @ B ) ) =
% 0.20/0.49         ( k1_tarski @ A ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ (k2_tarski @ X18 @ X19) @ (k1_tarski @ X19))
% 0.20/0.49            = (k1_tarski @ X18))
% 0.20/0.49          | ((X18) = (X19)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t23_zfmisc_1])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k2_tarski @ sk_B @ sk_C))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.49  thf(t64_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.20/0.49       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X20 : $i, X21 : $i, X23 : $i]:
% 0.20/0.49         ((r2_hidden @ X20 @ (k4_xboole_0 @ X21 @ (k1_tarski @ X23)))
% 0.20/0.49          | ((X20) = (X23))
% 0.20/0.49          | ~ (r2_hidden @ X20 @ X21))),
% 0.20/0.49      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_mcart_1 @ sk_A) = (X0))
% 0.20/0.49          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ 
% 0.20/0.49             (k4_xboole_0 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ X0))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.49        | ((sk_B) = (sk_C))
% 0.20/0.49        | ((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.20/0.49      inference('sup+', [status(thm)], ['3', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      ((((k1_mcart_1 @ sk_A) != (sk_C)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      ((((k1_mcart_1 @ sk_A) != (sk_C)))
% 0.20/0.49         <= (~ (((k1_mcart_1 @ sk_A) = (sk_C))))),
% 0.20/0.49      inference('split', [status(esa)], ['8'])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      ((r2_hidden @ sk_A @ 
% 0.20/0.49        (k2_zfmisc_1 @ (k2_tarski @ sk_B @ sk_C) @ (k1_tarski @ sk_D)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.49         ((r2_hidden @ (k2_mcart_1 @ X24) @ X26)
% 0.20/0.49          | ~ (r2_hidden @ X24 @ (k2_zfmisc_1 @ X25 @ X26)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.20/0.49  thf('12', plain, ((r2_hidden @ (k2_mcart_1 @ sk_A) @ (k1_tarski @ sk_D))),
% 0.20/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X18 : $i, X19 : $i]:
% 0.20/0.49         (((k4_xboole_0 @ (k2_tarski @ X18 @ X19) @ (k1_tarski @ X19))
% 0.20/0.49            = (k1_tarski @ X18))
% 0.20/0.49          | ((X18) = (X19)))),
% 0.20/0.49      inference('cnf', [status(esa)], [t23_zfmisc_1])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.49         (((X20) != (X22))
% 0.20/0.49          | ~ (r2_hidden @ X20 @ (k4_xboole_0 @ X21 @ (k1_tarski @ X22))))),
% 0.20/0.49      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X21 : $i, X22 : $i]:
% 0.20/0.49         ~ (r2_hidden @ X22 @ (k4_xboole_0 @ X21 @ (k1_tarski @ X22)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '15'])).
% 0.20/0.49  thf('17', plain, (((sk_D) = (k2_mcart_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      ((((k2_mcart_1 @ sk_A) != (sk_D)))
% 0.20/0.49         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.20/0.49      inference('split', [status(esa)], ['18'])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      ((((sk_D) != (sk_D))) <= (~ (((k2_mcart_1 @ sk_A) = (sk_D))))),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '19'])).
% 0.20/0.49  thf('21', plain, ((((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (~ (((k1_mcart_1 @ sk_A) = (sk_C))) | ~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['8'])).
% 0.20/0.49  thf('23', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_C)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('24', plain, (((k1_mcart_1 @ sk_A) != (sk_C))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['9', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))
% 0.20/0.49        | ((sk_B) = (sk_C)))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['7', '24'])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '15'])).
% 0.20/0.49  thf('27', plain, ((((sk_B) = (sk_C)) | ((sk_B) = (k1_mcart_1 @ sk_A)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.20/0.49         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.20/0.49      inference('split', [status(esa)], ['18'])).
% 0.20/0.49  thf('29', plain,
% 0.20/0.49      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | ~ (((k2_mcart_1 @ sk_A) = (sk_D)))),
% 0.20/0.49      inference('split', [status(esa)], ['18'])).
% 0.20/0.49  thf('30', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.20/0.49      inference('sat_resolution*', [status(thm)], ['21', '29'])).
% 0.20/0.49  thf('31', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['28', '30'])).
% 0.20/0.49  thf('32', plain, (((sk_B) = (sk_C))),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['27', '31'])).
% 0.20/0.49  thf(t69_enumset1, axiom,
% 0.20/0.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.49  thf('34', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.20/0.49      inference('demod', [status(thm)], ['2', '32', '33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X1 @ (k1_tarski @ X0)) | ((X0) = (X1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '15'])).
% 0.20/0.49  thf('36', plain, (((sk_B) = (k1_mcart_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.49  thf('37', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.20/0.49      inference('simpl_trail', [status(thm)], ['28', '30'])).
% 0.20/0.49  thf('38', plain, ($false),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
