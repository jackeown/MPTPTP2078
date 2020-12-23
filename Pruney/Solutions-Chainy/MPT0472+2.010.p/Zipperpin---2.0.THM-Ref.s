%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qojBfT5Awj

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 (  55 expanded)
%              Number of leaves         :   11 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  210 ( 408 expanded)
%              Number of equality atoms :   37 (  81 expanded)
%              Maximal formula depth    :    8 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t64_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( ( k1_relat_1 @ A )
              = k1_xboole_0 )
            | ( ( k2_relat_1 @ A )
              = k1_xboole_0 ) )
         => ( A = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_relat_1])).

thf('0',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( r1_tarski @ X4 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X4 ) @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('3',plain,
    ( ( ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('5',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( r1_tarski @ sk_A @ k1_xboole_0 )
   <= ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','5','6'])).

thf('8',plain,
    ( ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,(
    ! [X4: $i] :
      ( ( r1_tarski @ X4 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X4 ) @ ( k2_relat_1 @ X4 ) ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf('10',plain,
    ( ( ( r1_tarski @ sk_A @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_A ) )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('12',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( r1_tarski @ sk_A @ k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','12','13'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('16',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ( k1_relat_1 @ sk_A )
 != k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('20',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ sk_A @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['7','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('23',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qojBfT5Awj
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:25:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 12 iterations in 0.009s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.47  thf(t64_relat_1, conjecture,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ A ) =>
% 0.22/0.47       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.47           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.47         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i]:
% 0.22/0.47        ( ( v1_relat_1 @ A ) =>
% 0.22/0.47          ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.47              ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.47            ( ( A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t64_relat_1])).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      ((((k1_relat_1 @ sk_A) = (k1_xboole_0))
% 0.22/0.47        | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      ((((k2_relat_1 @ sk_A) = (k1_xboole_0)))
% 0.22/0.47         <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.47      inference('split', [status(esa)], ['0'])).
% 0.22/0.47  thf(t21_relat_1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ A ) =>
% 0.22/0.47       ( r1_tarski @
% 0.22/0.47         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X4 : $i]:
% 0.22/0.47         ((r1_tarski @ X4 @ 
% 0.22/0.47           (k2_zfmisc_1 @ (k1_relat_1 @ X4) @ (k2_relat_1 @ X4)))
% 0.22/0.47          | ~ (v1_relat_1 @ X4))),
% 0.22/0.47      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      ((((r1_tarski @ sk_A @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ k1_xboole_0))
% 0.22/0.47         | ~ (v1_relat_1 @ sk_A))) <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.47      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.47  thf(t113_zfmisc_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.47  thf('4', plain,
% 0.22/0.47      (![X2 : $i, X3 : $i]:
% 0.22/0.47         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.22/0.47      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.47  thf('5', plain,
% 0.22/0.47      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.47      inference('simplify', [status(thm)], ['4'])).
% 0.22/0.47  thf('6', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      (((r1_tarski @ sk_A @ k1_xboole_0))
% 0.22/0.47         <= ((((k2_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.47      inference('demod', [status(thm)], ['3', '5', '6'])).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      ((((k1_relat_1 @ sk_A) = (k1_xboole_0)))
% 0.22/0.47         <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.47      inference('split', [status(esa)], ['0'])).
% 0.22/0.47  thf('9', plain,
% 0.22/0.47      (![X4 : $i]:
% 0.22/0.47         ((r1_tarski @ X4 @ 
% 0.22/0.47           (k2_zfmisc_1 @ (k1_relat_1 @ X4) @ (k2_relat_1 @ X4)))
% 0.22/0.47          | ~ (v1_relat_1 @ X4))),
% 0.22/0.47      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.22/0.47  thf('10', plain,
% 0.22/0.47      ((((r1_tarski @ sk_A @ (k2_zfmisc_1 @ k1_xboole_0 @ (k2_relat_1 @ sk_A)))
% 0.22/0.47         | ~ (v1_relat_1 @ sk_A))) <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.47      inference('sup+', [status(thm)], ['8', '9'])).
% 0.22/0.47  thf('11', plain,
% 0.22/0.47      (![X2 : $i, X3 : $i]:
% 0.22/0.47         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.22/0.47      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.22/0.47      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.47  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('14', plain,
% 0.22/0.47      (((r1_tarski @ sk_A @ k1_xboole_0))
% 0.22/0.47         <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.47      inference('demod', [status(thm)], ['10', '12', '13'])).
% 0.22/0.47  thf(t3_xboole_1, axiom,
% 0.22/0.47    (![A:$i]:
% 0.22/0.47     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.47  thf('15', plain,
% 0.22/0.47      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.22/0.47  thf('16', plain,
% 0.22/0.47      ((((sk_A) = (k1_xboole_0))) <= ((((k1_relat_1 @ sk_A) = (k1_xboole_0))))),
% 0.22/0.47      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.47  thf('17', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('18', plain, (~ (((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.47      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.22/0.47  thf('19', plain,
% 0.22/0.47      ((((k2_relat_1 @ sk_A) = (k1_xboole_0))) | 
% 0.22/0.47       (((k1_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.47      inference('split', [status(esa)], ['0'])).
% 0.22/0.47  thf('20', plain, ((((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.22/0.47      inference('sat_resolution*', [status(thm)], ['18', '19'])).
% 0.22/0.47  thf('21', plain, ((r1_tarski @ sk_A @ k1_xboole_0)),
% 0.22/0.47      inference('simpl_trail', [status(thm)], ['7', '20'])).
% 0.22/0.47  thf('22', plain,
% 0.22/0.47      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.22/0.47  thf('23', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.47  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('25', plain, ($false),
% 0.22/0.47      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.34/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
