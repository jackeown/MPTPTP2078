%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UN8qWP6K2H

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  85 expanded)
%              Number of leaves         :   18 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  214 ( 680 expanded)
%              Number of equality atoms :   21 (  77 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t24_mcart_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
             => ( C
                = ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ~ ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) )
               => ( C
                  = ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t24_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k4_tarski @ ( k1_mcart_1 @ X7 ) @ ( k2_mcart_1 @ X7 ) ) )
      | ~ ( v1_relat_1 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('4',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('6',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    sk_C
 != ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('9',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('10',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[fc10_subset_1])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('14',plain,
    ( ( k2_zfmisc_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('18',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_xboole_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('22',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['22','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UN8qWP6K2H
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:05:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 17 iterations in 0.013s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.46  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.21/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.46  thf(t24_mcart_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.46          ( ~( ![C:$i]:
% 0.21/0.46               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.21/0.46                 ( ( C ) =
% 0.21/0.46                   ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i]:
% 0.21/0.46        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.46             ( ~( ![C:$i]:
% 0.21/0.46                  ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.21/0.46                    ( ( C ) =
% 0.21/0.46                      ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t24_mcart_1])).
% 0.21/0.46  thf('0', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t2_subset, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.46       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X3 : $i, X4 : $i]:
% 0.21/0.46         ((r2_hidden @ X3 @ X4)
% 0.21/0.46          | (v1_xboole_0 @ X4)
% 0.21/0.46          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.21/0.46      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.21/0.46        | (r2_hidden @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf(t23_mcart_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( v1_relat_1 @ B ) =>
% 0.21/0.46       ( ( r2_hidden @ A @ B ) =>
% 0.21/0.46         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X7 : $i, X8 : $i]:
% 0.21/0.46         (((X7) = (k4_tarski @ (k1_mcart_1 @ X7) @ (k2_mcart_1 @ X7)))
% 0.21/0.46          | ~ (v1_relat_1 @ X8)
% 0.21/0.46          | ~ (r2_hidden @ X7 @ X8))),
% 0.21/0.46      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.21/0.46  thf('4', plain,
% 0.21/0.46      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.21/0.46        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.21/0.46        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.21/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.46  thf(fc6_relat_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.21/0.46      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.21/0.46        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.21/0.46      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (((sk_C) != (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('8', plain, ((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf(l13_xboole_0, axiom,
% 0.21/0.46    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.46  thf('9', plain,
% 0.21/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.46  thf('10', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf(fc10_subset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.21/0.46       ( ~( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) ))).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X1 : $i, X2 : $i]:
% 0.21/0.46         ((v1_xboole_0 @ X1)
% 0.21/0.46          | (v1_xboole_0 @ X2)
% 0.21/0.46          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X2)))),
% 0.21/0.46      inference('cnf', [status(esa)], [fc10_subset_1])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.46        | (v1_xboole_0 @ sk_B)
% 0.21/0.46        | (v1_xboole_0 @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.46  thf('13', plain, ((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf('14', plain, (((k2_zfmisc_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.46  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.46      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.46  thf('16', plain, (((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.21/0.46      inference('demod', [status(thm)], ['12', '15'])).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.46  thf('18', plain, (((v1_xboole_0 @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.46  thf('19', plain, (((sk_B) != (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('20', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.21/0.46  thf('21', plain,
% 0.21/0.46      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.46  thf('22', plain, (((sk_A) = (k1_xboole_0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.46  thf('23', plain, (((sk_A) != (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('24', plain, ($false),
% 0.21/0.46      inference('simplify_reflect-', [status(thm)], ['22', '23'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
