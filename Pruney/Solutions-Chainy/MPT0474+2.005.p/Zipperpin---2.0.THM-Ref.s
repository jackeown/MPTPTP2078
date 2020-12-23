%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UY9srDh0VT

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:54 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   40 (  54 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  191 ( 252 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('1',plain,(
    ! [X6: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(d7_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( B
              = ( k4_relat_1 @ A ) )
          <=> ! [C: $i,D: $i] :
                ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X7 @ X8 ) @ ( sk_D @ X7 @ X8 ) ) @ X7 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X7 @ X8 ) @ ( sk_C @ X7 @ X8 ) ) @ X8 )
      | ( X7
        = ( k4_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ X2 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('6',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 ) @ ( sk_C @ k1_xboole_0 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','6'])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 ) @ ( sk_C @ k1_xboole_0 @ X0 ) ) @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('10',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('11',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('12',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 ) @ ( sk_C @ k1_xboole_0 @ X0 ) ) @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t66_relat_1,conjecture,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k4_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t66_relat_1])).

thf('17',plain,(
    ( k4_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['9','12'])).

thf('21',plain,(
    $false ),
    inference(demod,[status(thm)],['19','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UY9srDh0VT
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:57:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.62  % Solved by: fo/fo7.sh
% 0.36/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.62  % done 521 iterations in 0.165s
% 0.36/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.62  % SZS output start Refutation
% 0.36/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.62  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 0.36/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.36/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.62  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.36/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.62  thf(cc1_relat_1, axiom,
% 0.36/0.62    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.36/0.62  thf('0', plain, (![X6 : $i]: ((v1_relat_1 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.36/0.62      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.36/0.62  thf('1', plain, (![X6 : $i]: ((v1_relat_1 @ X6) | ~ (v1_xboole_0 @ X6))),
% 0.36/0.62      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.36/0.62  thf(d7_relat_1, axiom,
% 0.36/0.62    (![A:$i]:
% 0.36/0.62     ( ( v1_relat_1 @ A ) =>
% 0.36/0.62       ( ![B:$i]:
% 0.36/0.62         ( ( v1_relat_1 @ B ) =>
% 0.36/0.62           ( ( ( B ) = ( k4_relat_1 @ A ) ) <=>
% 0.36/0.62             ( ![C:$i,D:$i]:
% 0.36/0.62               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.36/0.62                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) ) ))).
% 0.36/0.62  thf('2', plain,
% 0.36/0.62      (![X7 : $i, X8 : $i]:
% 0.36/0.62         (~ (v1_relat_1 @ X7)
% 0.36/0.62          | (r2_hidden @ (k4_tarski @ (sk_C @ X7 @ X8) @ (sk_D @ X7 @ X8)) @ X7)
% 0.36/0.62          | (r2_hidden @ (k4_tarski @ (sk_D @ X7 @ X8) @ (sk_C @ X7 @ X8)) @ X8)
% 0.36/0.62          | ((X7) = (k4_relat_1 @ X8))
% 0.36/0.62          | ~ (v1_relat_1 @ X8))),
% 0.36/0.62      inference('cnf', [status(esa)], [d7_relat_1])).
% 0.36/0.62  thf(t113_zfmisc_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]:
% 0.36/0.62     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.62       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.62  thf('3', plain,
% 0.36/0.62      (![X2 : $i, X3 : $i]:
% 0.36/0.62         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 0.36/0.62      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.36/0.62  thf('4', plain,
% 0.36/0.62      (![X2 : $i]: ((k2_zfmisc_1 @ X2 @ k1_xboole_0) = (k1_xboole_0))),
% 0.36/0.62      inference('simplify', [status(thm)], ['3'])).
% 0.36/0.62  thf(t152_zfmisc_1, axiom,
% 0.36/0.62    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.36/0.62  thf('5', plain,
% 0.36/0.62      (![X4 : $i, X5 : $i]: ~ (r2_hidden @ X4 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.36/0.62      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.36/0.62  thf('6', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.36/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.62  thf('7', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (v1_relat_1 @ X0)
% 0.36/0.62          | ((k1_xboole_0) = (k4_relat_1 @ X0))
% 0.36/0.62          | (r2_hidden @ 
% 0.36/0.62             (k4_tarski @ (sk_D @ k1_xboole_0 @ X0) @ (sk_C @ k1_xboole_0 @ X0)) @ 
% 0.36/0.62             X0)
% 0.36/0.62          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['2', '6'])).
% 0.36/0.62  thf('8', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.62          | (r2_hidden @ 
% 0.36/0.62             (k4_tarski @ (sk_D @ k1_xboole_0 @ X0) @ (sk_C @ k1_xboole_0 @ X0)) @ 
% 0.36/0.62             X0)
% 0.36/0.62          | ((k1_xboole_0) = (k4_relat_1 @ X0))
% 0.36/0.62          | ~ (v1_relat_1 @ X0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['1', '7'])).
% 0.36/0.62  thf(dt_o_0_0_xboole_0, axiom, (v1_xboole_0 @ o_0_0_xboole_0)).
% 0.36/0.62  thf('9', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.36/0.62      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.36/0.62  thf('10', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 0.36/0.62      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 0.36/0.62  thf(l13_xboole_0, axiom,
% 0.36/0.62    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.36/0.62  thf('11', plain,
% 0.36/0.62      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.62      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.36/0.62  thf('12', plain, (((o_0_0_xboole_0) = (k1_xboole_0))),
% 0.36/0.62      inference('sup-', [status(thm)], ['10', '11'])).
% 0.36/0.62  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.62      inference('demod', [status(thm)], ['9', '12'])).
% 0.36/0.62  thf('14', plain,
% 0.36/0.62      (![X0 : $i]:
% 0.36/0.62         ((r2_hidden @ 
% 0.36/0.62           (k4_tarski @ (sk_D @ k1_xboole_0 @ X0) @ (sk_C @ k1_xboole_0 @ X0)) @ 
% 0.36/0.62           X0)
% 0.36/0.62          | ((k1_xboole_0) = (k4_relat_1 @ X0))
% 0.36/0.62          | ~ (v1_relat_1 @ X0))),
% 0.36/0.62      inference('demod', [status(thm)], ['8', '13'])).
% 0.36/0.62  thf('15', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.36/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.62  thf('16', plain,
% 0.36/0.62      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.36/0.62        | ((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0)))),
% 0.36/0.62      inference('sup-', [status(thm)], ['14', '15'])).
% 0.36/0.62  thf(t66_relat_1, conjecture,
% 0.36/0.62    (( k4_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.36/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.62    (( k4_relat_1 @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.36/0.62    inference('cnf.neg', [status(esa)], [t66_relat_1])).
% 0.36/0.62  thf('17', plain, (((k4_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.36/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.62  thf('18', plain, (~ (v1_relat_1 @ k1_xboole_0)),
% 0.36/0.62      inference('simplify_reflect-', [status(thm)], ['16', '17'])).
% 0.36/0.62  thf('19', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.62      inference('sup-', [status(thm)], ['0', '18'])).
% 0.36/0.62  thf('20', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.62      inference('demod', [status(thm)], ['9', '12'])).
% 0.36/0.62  thf('21', plain, ($false), inference('demod', [status(thm)], ['19', '20'])).
% 0.36/0.62  
% 0.36/0.62  % SZS output end Refutation
% 0.36/0.62  
% 0.46/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
