%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GMMYXKtsF6

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:13 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   51 (  62 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :  244 ( 372 expanded)
%              Number of equality atoms :   21 (  41 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

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

thf('1',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['2'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('4',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('5',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference('simplify_reflect+',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( X8
        = ( k4_tarski @ ( k1_mcart_1 @ X8 ) @ ( k2_mcart_1 @ X8 ) ) )
      | ~ ( v1_relat_1 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_C
      = ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    sk_C
 != ( k4_tarski @ ( k1_mcart_1 @ sk_C ) @ ( k2_mcart_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( k1_xboole_0
    = ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(fc10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[fc10_subset_1])).

thf('20',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('22',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('24',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference('simplify_reflect+',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_xboole_0 @ sk_A ),
    inference(clc,[status(thm)],['22','28'])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['5','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.11  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GMMYXKtsF6
% 0.10/0.31  % Computer   : n025.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % DateTime   : Tue Dec  1 15:31:05 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.10/0.31  % Running portfolio for 600 s
% 0.10/0.31  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.10/0.32  % Number of cores: 8
% 0.10/0.32  % Python version: Python 3.6.8
% 0.10/0.32  % Running in FO mode
% 0.18/0.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.18/0.43  % Solved by: fo/fo7.sh
% 0.18/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.43  % done 33 iterations in 0.012s
% 0.18/0.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.18/0.43  % SZS output start Refutation
% 0.18/0.43  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.18/0.43  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.18/0.43  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.18/0.43  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.43  thf(sk_C_type, type, sk_C: $i).
% 0.18/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.18/0.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.18/0.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.18/0.43  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.18/0.43  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.18/0.43  thf(t8_boole, axiom,
% 0.18/0.43    (![A:$i,B:$i]:
% 0.18/0.43     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.18/0.43  thf('0', plain,
% 0.18/0.43      (![X0 : $i, X1 : $i]:
% 0.18/0.43         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.18/0.43      inference('cnf', [status(esa)], [t8_boole])).
% 0.18/0.43  thf(t24_mcart_1, conjecture,
% 0.18/0.43    (![A:$i,B:$i]:
% 0.18/0.43     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.18/0.43          ( ~( ![C:$i]:
% 0.18/0.43               ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.18/0.43                 ( ( C ) =
% 0.18/0.43                   ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) ) ) ))).
% 0.18/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.43    (~( ![A:$i,B:$i]:
% 0.18/0.43        ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.18/0.43             ( ~( ![C:$i]:
% 0.18/0.43                  ( ( m1_subset_1 @ C @ ( k2_zfmisc_1 @ A @ B ) ) =>
% 0.18/0.43                    ( ( C ) =
% 0.18/0.43                      ( k4_tarski @ ( k1_mcart_1 @ C ) @ ( k2_mcart_1 @ C ) ) ) ) ) ) ) ) )),
% 0.18/0.43    inference('cnf.neg', [status(esa)], [t24_mcart_1])).
% 0.18/0.43  thf('1', plain, (((sk_A) != (k1_xboole_0))),
% 0.18/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.43  thf('2', plain,
% 0.18/0.43      (![X0 : $i]:
% 0.18/0.43         (((X0) != (k1_xboole_0))
% 0.18/0.43          | ~ (v1_xboole_0 @ sk_A)
% 0.18/0.43          | ~ (v1_xboole_0 @ X0))),
% 0.18/0.43      inference('sup-', [status(thm)], ['0', '1'])).
% 0.18/0.43  thf('3', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_A))),
% 0.18/0.43      inference('simplify', [status(thm)], ['2'])).
% 0.18/0.43  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.18/0.43  thf('4', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.18/0.43      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.18/0.43  thf('5', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.18/0.43      inference('simplify_reflect+', [status(thm)], ['3', '4'])).
% 0.18/0.43  thf('6', plain, ((m1_subset_1 @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.18/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.43  thf(t2_subset, axiom,
% 0.18/0.43    (![A:$i,B:$i]:
% 0.18/0.43     ( ( m1_subset_1 @ A @ B ) =>
% 0.18/0.43       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.18/0.43  thf('7', plain,
% 0.18/0.43      (![X4 : $i, X5 : $i]:
% 0.18/0.43         ((r2_hidden @ X4 @ X5)
% 0.18/0.43          | (v1_xboole_0 @ X5)
% 0.18/0.43          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.18/0.43      inference('cnf', [status(esa)], [t2_subset])).
% 0.18/0.43  thf('8', plain,
% 0.18/0.43      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.18/0.43        | (r2_hidden @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.18/0.43      inference('sup-', [status(thm)], ['6', '7'])).
% 0.18/0.43  thf(t23_mcart_1, axiom,
% 0.18/0.43    (![A:$i,B:$i]:
% 0.18/0.43     ( ( v1_relat_1 @ B ) =>
% 0.18/0.43       ( ( r2_hidden @ A @ B ) =>
% 0.18/0.43         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.18/0.43  thf('9', plain,
% 0.18/0.43      (![X8 : $i, X9 : $i]:
% 0.18/0.43         (((X8) = (k4_tarski @ (k1_mcart_1 @ X8) @ (k2_mcart_1 @ X8)))
% 0.18/0.43          | ~ (v1_relat_1 @ X9)
% 0.18/0.43          | ~ (r2_hidden @ X8 @ X9))),
% 0.18/0.43      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.18/0.43  thf('10', plain,
% 0.18/0.43      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.18/0.43        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.18/0.43        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.18/0.43      inference('sup-', [status(thm)], ['8', '9'])).
% 0.18/0.43  thf(fc6_relat_1, axiom,
% 0.18/0.43    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.18/0.43  thf('11', plain,
% 0.18/0.43      (![X6 : $i, X7 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X6 @ X7))),
% 0.18/0.43      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.18/0.43  thf('12', plain,
% 0.18/0.43      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.18/0.43        | ((sk_C) = (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C))))),
% 0.18/0.43      inference('demod', [status(thm)], ['10', '11'])).
% 0.18/0.43  thf('13', plain,
% 0.18/0.43      (((sk_C) != (k4_tarski @ (k1_mcart_1 @ sk_C) @ (k2_mcart_1 @ sk_C)))),
% 0.18/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.43  thf('14', plain, ((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.18/0.43      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.18/0.43  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.18/0.43      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.18/0.43  thf('16', plain,
% 0.18/0.43      (![X0 : $i, X1 : $i]:
% 0.18/0.43         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.18/0.43      inference('cnf', [status(esa)], [t8_boole])).
% 0.18/0.43  thf('17', plain,
% 0.18/0.43      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.18/0.43      inference('sup-', [status(thm)], ['15', '16'])).
% 0.18/0.43  thf('18', plain, (((k1_xboole_0) = (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.18/0.43      inference('sup-', [status(thm)], ['14', '17'])).
% 0.18/0.43  thf(fc10_subset_1, axiom,
% 0.18/0.43    (![A:$i,B:$i]:
% 0.18/0.43     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.18/0.43       ( ~( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) ))).
% 0.18/0.43  thf('19', plain,
% 0.18/0.43      (![X2 : $i, X3 : $i]:
% 0.18/0.43         ((v1_xboole_0 @ X2)
% 0.18/0.43          | (v1_xboole_0 @ X3)
% 0.18/0.43          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X2 @ X3)))),
% 0.18/0.43      inference('cnf', [status(esa)], [fc10_subset_1])).
% 0.18/0.43  thf('20', plain,
% 0.18/0.43      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.18/0.43        | (v1_xboole_0 @ sk_B)
% 0.18/0.43        | (v1_xboole_0 @ sk_A))),
% 0.18/0.43      inference('sup-', [status(thm)], ['18', '19'])).
% 0.18/0.43  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.18/0.43      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.18/0.43  thf('22', plain, (((v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.18/0.43      inference('demod', [status(thm)], ['20', '21'])).
% 0.18/0.43  thf('23', plain,
% 0.18/0.43      (![X0 : $i, X1 : $i]:
% 0.18/0.43         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.18/0.43      inference('cnf', [status(esa)], [t8_boole])).
% 0.18/0.43  thf('24', plain, (((sk_B) != (k1_xboole_0))),
% 0.18/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.43  thf('25', plain,
% 0.18/0.43      (![X0 : $i]:
% 0.18/0.43         (((X0) != (k1_xboole_0))
% 0.18/0.43          | ~ (v1_xboole_0 @ sk_B)
% 0.18/0.43          | ~ (v1_xboole_0 @ X0))),
% 0.18/0.43      inference('sup-', [status(thm)], ['23', '24'])).
% 0.18/0.43  thf('26', plain, ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B))),
% 0.18/0.43      inference('simplify', [status(thm)], ['25'])).
% 0.18/0.43  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.18/0.43      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.18/0.43  thf('28', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.18/0.43      inference('simplify_reflect+', [status(thm)], ['26', '27'])).
% 0.18/0.43  thf('29', plain, ((v1_xboole_0 @ sk_A)),
% 0.18/0.43      inference('clc', [status(thm)], ['22', '28'])).
% 0.18/0.43  thf('30', plain, ($false), inference('demod', [status(thm)], ['5', '29'])).
% 0.18/0.43  
% 0.18/0.43  % SZS output end Refutation
% 0.18/0.43  
% 0.18/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
