%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O0rJTq1luG

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   44 (  64 expanded)
%              Number of leaves         :   16 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  315 ( 649 expanded)
%              Number of equality atoms :   45 (  93 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t18_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) )
     => ( ( ( k1_mcart_1 @ A )
          = B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) )
       => ( ( ( k1_mcart_1 @ A )
            = B )
          & ( ( ( k2_mcart_1 @ A )
              = C )
            | ( ( k2_mcart_1 @ A )
              = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_mcart_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('2',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('4',plain,(
    ! [X12: $i,X13: $i,X15: $i] :
      ( ( r2_hidden @ X12 @ ( k4_xboole_0 @ X13 @ ( k1_tarski @ X15 ) ) )
      | ( X12 = X15 )
      | ~ ( r2_hidden @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k1_mcart_1 @ sk_A )
        = X0 )
      | ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k4_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('7',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k1_mcart_1 @ sk_A )
        = X0 )
      | ~ ( r2_hidden @ ( k1_mcart_1 @ sk_A ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,
    ( ( k1_mcart_1 @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
   <= ( ( k1_mcart_1 @ sk_A )
     != sk_B ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['10'])).

thf('13',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k1_mcart_1 @ sk_A )
     != sk_B )
    | ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_C @ sk_D_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t16_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( ( ( k2_mcart_1 @ A )
            = C )
          | ( ( k2_mcart_1 @ A )
            = D ) ) ) ) )).

thf('16',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_mcart_1 @ X19 )
        = X22 )
      | ( ( k2_mcart_1 @ X19 )
        = X21 )
      | ~ ( r2_hidden @ X19 @ ( k2_zfmisc_1 @ X20 @ ( k2_tarski @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[t16_mcart_1])).

thf('17',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(split,[status(esa)],['13'])).

thf('19',plain,
    ( ( ( sk_D_1 != sk_D_1 )
      | ( ( k2_mcart_1 @ sk_A )
        = sk_C ) )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_D_1 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( k2_mcart_1 @ sk_A )
     != sk_C )
   <= ( ( k2_mcart_1 @ sk_A )
     != sk_C ) ),
    inference(split,[status(esa)],['10'])).

thf('22',plain,
    ( ( sk_C != sk_C )
   <= ( ( ( k2_mcart_1 @ sk_A )
       != sk_D_1 )
      & ( ( k2_mcart_1 @ sk_A )
       != sk_C ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ( k2_mcart_1 @ sk_A )
      = sk_C )
    | ( ( k2_mcart_1 @ sk_A )
      = sk_D_1 ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference('sat_resolution*',[status(thm)],['12','14','23'])).

thf('25',plain,(
    ( k1_mcart_1 @ sk_A )
 != sk_B ),
    inference(simpl_trail,[status(thm)],['11','24'])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['9','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.O0rJTq1luG
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:47:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.56  % Solved by: fo/fo7.sh
% 0.22/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.56  % done 228 iterations in 0.125s
% 0.22/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.56  % SZS output start Refutation
% 0.22/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.56  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.56  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.56  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.56  thf(t18_mcart_1, conjecture,
% 0.22/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.56     ( ( r2_hidden @
% 0.22/0.56         A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) ) =>
% 0.22/0.56       ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.22/0.56         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.22/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.56        ( ( r2_hidden @
% 0.22/0.56            A @ ( k2_zfmisc_1 @ ( k1_tarski @ B ) @ ( k2_tarski @ C @ D ) ) ) =>
% 0.22/0.56          ( ( ( k1_mcart_1 @ A ) = ( B ) ) & 
% 0.22/0.56            ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ) )),
% 0.22/0.56    inference('cnf.neg', [status(esa)], [t18_mcart_1])).
% 0.22/0.56  thf('0', plain,
% 0.22/0.56      ((r2_hidden @ sk_A @ 
% 0.22/0.56        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(t10_mcart_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.22/0.56       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.22/0.56         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.22/0.56  thf('1', plain,
% 0.22/0.56      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.22/0.56         ((r2_hidden @ (k1_mcart_1 @ X16) @ X17)
% 0.22/0.56          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 0.22/0.56      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.22/0.56  thf('2', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.22/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.56  thf('3', plain, ((r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ sk_B))),
% 0.22/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.56  thf(t64_zfmisc_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.22/0.56       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.22/0.56  thf('4', plain,
% 0.22/0.56      (![X12 : $i, X13 : $i, X15 : $i]:
% 0.22/0.56         ((r2_hidden @ X12 @ (k4_xboole_0 @ X13 @ (k1_tarski @ X15)))
% 0.22/0.56          | ((X12) = (X15))
% 0.22/0.56          | ~ (r2_hidden @ X12 @ X13))),
% 0.22/0.56      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.22/0.56  thf('5', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (((k1_mcart_1 @ sk_A) = (X0))
% 0.22/0.56          | (r2_hidden @ (k1_mcart_1 @ sk_A) @ 
% 0.22/0.56             (k4_xboole_0 @ (k1_tarski @ sk_B) @ (k1_tarski @ X0))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.56  thf(d5_xboole_0, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.22/0.56       ( ![D:$i]:
% 0.22/0.56         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.56           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.22/0.56  thf('6', plain,
% 0.22/0.56      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.56         (~ (r2_hidden @ X4 @ X3)
% 0.22/0.56          | ~ (r2_hidden @ X4 @ X2)
% 0.22/0.56          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.56      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.22/0.56  thf('7', plain,
% 0.22/0.56      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.22/0.56         (~ (r2_hidden @ X4 @ X2)
% 0.22/0.56          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.56  thf('8', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (((k1_mcart_1 @ sk_A) = (X0))
% 0.22/0.56          | ~ (r2_hidden @ (k1_mcart_1 @ sk_A) @ (k1_tarski @ X0)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['5', '7'])).
% 0.22/0.56  thf('9', plain, (((k1_mcart_1 @ sk_A) = (sk_B))),
% 0.22/0.56      inference('sup-', [status(thm)], ['2', '8'])).
% 0.22/0.56  thf('10', plain,
% 0.22/0.56      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_C)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('11', plain,
% 0.22/0.56      ((((k1_mcart_1 @ sk_A) != (sk_B)))
% 0.22/0.56         <= (~ (((k1_mcart_1 @ sk_A) = (sk_B))))),
% 0.22/0.56      inference('split', [status(esa)], ['10'])).
% 0.22/0.56  thf('12', plain,
% 0.22/0.56      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | ~ (((k2_mcart_1 @ sk_A) = (sk_C)))),
% 0.22/0.56      inference('split', [status(esa)], ['10'])).
% 0.22/0.56  thf('13', plain,
% 0.22/0.56      ((((k1_mcart_1 @ sk_A) != (sk_B)) | ((k2_mcart_1 @ sk_A) != (sk_D_1)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('14', plain,
% 0.22/0.56      (~ (((k1_mcart_1 @ sk_A) = (sk_B))) | 
% 0.22/0.56       ~ (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.22/0.56      inference('split', [status(esa)], ['13'])).
% 0.22/0.56  thf('15', plain,
% 0.22/0.56      ((r2_hidden @ sk_A @ 
% 0.22/0.56        (k2_zfmisc_1 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_C @ sk_D_1)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(t16_mcart_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.56     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ ( k2_tarski @ C @ D ) ) ) =>
% 0.22/0.56       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.22/0.56         ( ( ( k2_mcart_1 @ A ) = ( C ) ) | ( ( k2_mcart_1 @ A ) = ( D ) ) ) ) ))).
% 0.22/0.56  thf('16', plain,
% 0.22/0.56      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.56         (((k2_mcart_1 @ X19) = (X22))
% 0.22/0.56          | ((k2_mcart_1 @ X19) = (X21))
% 0.22/0.56          | ~ (r2_hidden @ X19 @ (k2_zfmisc_1 @ X20 @ (k2_tarski @ X21 @ X22))))),
% 0.22/0.56      inference('cnf', [status(esa)], [t16_mcart_1])).
% 0.22/0.56  thf('17', plain,
% 0.22/0.56      ((((k2_mcart_1 @ sk_A) = (sk_C)) | ((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.56  thf('18', plain,
% 0.22/0.56      ((((k2_mcart_1 @ sk_A) != (sk_D_1)))
% 0.22/0.56         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.22/0.56      inference('split', [status(esa)], ['13'])).
% 0.22/0.56  thf('19', plain,
% 0.22/0.56      (((((sk_D_1) != (sk_D_1)) | ((k2_mcart_1 @ sk_A) = (sk_C))))
% 0.22/0.56         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.56  thf('20', plain,
% 0.22/0.56      ((((k2_mcart_1 @ sk_A) = (sk_C)))
% 0.22/0.56         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))))),
% 0.22/0.56      inference('simplify', [status(thm)], ['19'])).
% 0.22/0.56  thf('21', plain,
% 0.22/0.56      ((((k2_mcart_1 @ sk_A) != (sk_C)))
% 0.22/0.56         <= (~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.22/0.56      inference('split', [status(esa)], ['10'])).
% 0.22/0.56  thf('22', plain,
% 0.22/0.56      ((((sk_C) != (sk_C)))
% 0.22/0.56         <= (~ (((k2_mcart_1 @ sk_A) = (sk_D_1))) & 
% 0.22/0.56             ~ (((k2_mcart_1 @ sk_A) = (sk_C))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.56  thf('23', plain,
% 0.22/0.56      ((((k2_mcart_1 @ sk_A) = (sk_C))) | (((k2_mcart_1 @ sk_A) = (sk_D_1)))),
% 0.22/0.56      inference('simplify', [status(thm)], ['22'])).
% 0.22/0.56  thf('24', plain, (~ (((k1_mcart_1 @ sk_A) = (sk_B)))),
% 0.22/0.56      inference('sat_resolution*', [status(thm)], ['12', '14', '23'])).
% 0.22/0.56  thf('25', plain, (((k1_mcart_1 @ sk_A) != (sk_B))),
% 0.22/0.56      inference('simpl_trail', [status(thm)], ['11', '24'])).
% 0.22/0.56  thf('26', plain, ($false),
% 0.22/0.56      inference('simplify_reflect-', [status(thm)], ['9', '25'])).
% 0.22/0.56  
% 0.22/0.56  % SZS output end Refutation
% 0.22/0.56  
% 0.22/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
