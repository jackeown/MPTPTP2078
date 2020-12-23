%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7wD7gdzuDq

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  135 ( 147 expanded)
%              Number of equality atoms :    8 (  10 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_setfam_1_type,type,(
    r1_setfam_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t21_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( r1_setfam_1 @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( r1_setfam_1 @ A @ k1_xboole_0 )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t21_setfam_1])).

thf('1',plain,(
    r1_setfam_1 @ sk_A @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_setfam_1 @ A @ B )
    <=> ! [C: $i] :
          ~ ( ( r2_hidden @ C @ A )
            & ! [D: $i] :
                ~ ( ( r2_hidden @ D @ B )
                  & ( r1_tarski @ C @ D ) ) ) ) )).

thf('2',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ ( sk_D @ X11 @ X12 ) @ X12 )
      | ~ ( r2_hidden @ X11 @ X13 )
      | ~ ( r1_setfam_1 @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d2_setfam_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D @ ( sk_C @ X0 @ sk_A ) @ k1_xboole_0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X9: $i] :
      ( ( k1_subset_1 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(fc13_subset_1,axiom,(
    ! [A: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ A ) ) )).

thf('8',plain,(
    ! [X10: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc13_subset_1])).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ X0 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t135_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) )
        | ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t135_zfmisc_1])).

thf('12',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7wD7gdzuDq
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:46:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.43  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.43  % Solved by: fo/fo7.sh
% 0.20/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.43  % done 50 iterations in 0.012s
% 0.20/0.43  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.43  % SZS output start Refutation
% 0.20/0.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.43  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.43  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.43  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.20/0.43  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.43  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.20/0.43  thf(r1_setfam_1_type, type, r1_setfam_1: $i > $i > $o).
% 0.20/0.43  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.43  thf(d3_tarski, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.43       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.43  thf('0', plain,
% 0.20/0.43      (![X4 : $i, X6 : $i]:
% 0.20/0.43         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.20/0.43      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.43  thf(t21_setfam_1, conjecture,
% 0.20/0.43    (![A:$i]:
% 0.20/0.43     ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.43    (~( ![A:$i]:
% 0.20/0.43        ( ( r1_setfam_1 @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.43    inference('cnf.neg', [status(esa)], [t21_setfam_1])).
% 0.20/0.43  thf('1', plain, ((r1_setfam_1 @ sk_A @ k1_xboole_0)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf(d2_setfam_1, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( r1_setfam_1 @ A @ B ) <=>
% 0.20/0.43       ( ![C:$i]:
% 0.20/0.43         ( ~( ( r2_hidden @ C @ A ) & 
% 0.20/0.43              ( ![D:$i]: ( ~( ( r2_hidden @ D @ B ) & ( r1_tarski @ C @ D ) ) ) ) ) ) ) ))).
% 0.20/0.43  thf('2', plain,
% 0.20/0.43      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.43         ((r2_hidden @ (sk_D @ X11 @ X12) @ X12)
% 0.20/0.43          | ~ (r2_hidden @ X11 @ X13)
% 0.20/0.43          | ~ (r1_setfam_1 @ X13 @ X12))),
% 0.20/0.43      inference('cnf', [status(esa)], [d2_setfam_1])).
% 0.20/0.43  thf('3', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         (~ (r2_hidden @ X0 @ sk_A)
% 0.20/0.43          | (r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0))),
% 0.20/0.43      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.43  thf('4', plain,
% 0.20/0.43      (![X0 : $i]:
% 0.20/0.43         ((r1_tarski @ sk_A @ X0)
% 0.20/0.43          | (r2_hidden @ (sk_D @ (sk_C @ X0 @ sk_A) @ k1_xboole_0) @ 
% 0.20/0.43             k1_xboole_0))),
% 0.20/0.43      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.43  thf(d1_xboole_0, axiom,
% 0.20/0.43    (![A:$i]:
% 0.20/0.43     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.43  thf('5', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.43      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.43  thf('6', plain,
% 0.20/0.43      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.43      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.43  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.43  thf('7', plain, (![X9 : $i]: ((k1_subset_1 @ X9) = (k1_xboole_0))),
% 0.20/0.43      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.20/0.43  thf(fc13_subset_1, axiom, (![A:$i]: ( v1_xboole_0 @ ( k1_subset_1 @ A ) ))).
% 0.20/0.43  thf('8', plain, (![X10 : $i]: (v1_xboole_0 @ (k1_subset_1 @ X10))),
% 0.20/0.43      inference('cnf', [status(esa)], [fc13_subset_1])).
% 0.20/0.43  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.43      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.43  thf('10', plain, (![X0 : $i]: (r1_tarski @ sk_A @ X0)),
% 0.20/0.43      inference('demod', [status(thm)], ['6', '9'])).
% 0.20/0.43  thf(t135_zfmisc_1, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( ( r1_tarski @ A @ ( k2_zfmisc_1 @ A @ B ) ) | 
% 0.20/0.43         ( r1_tarski @ A @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.43       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.43  thf('11', plain,
% 0.20/0.43      (![X7 : $i, X8 : $i]:
% 0.20/0.43         (((X7) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ (k2_zfmisc_1 @ X7 @ X8)))),
% 0.20/0.43      inference('cnf', [status(esa)], [t135_zfmisc_1])).
% 0.20/0.43  thf('12', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.43      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.43  thf('13', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('14', plain, ($false),
% 0.20/0.43      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.20/0.43  
% 0.20/0.43  % SZS output end Refutation
% 0.20/0.43  
% 0.20/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
