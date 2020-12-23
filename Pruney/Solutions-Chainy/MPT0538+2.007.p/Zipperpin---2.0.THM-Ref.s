%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dUS0Wtv7lh

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:50 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   36 (  43 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :   11
%              Number of atoms          :  207 ( 247 expanded)
%              Number of equality atoms :   18 (  24 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t138_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k8_relat_1 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k8_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t138_relat_1])).

thf('0',plain,(
    ( k8_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('2',plain,(
    ! [X5: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(d12_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( C
              = ( k8_relat_1 @ A @ B ) )
          <=> ! [D: $i,E: $i] :
                ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
              <=> ( ( r2_hidden @ E @ A )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X6 @ X8 @ X7 ) @ ( sk_E @ X6 @ X8 @ X7 ) ) @ X6 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X6 @ X8 @ X7 ) @ ( sk_E @ X6 @ X8 @ X7 ) ) @ X8 )
      | ( X6
        = ( k8_relat_1 @ X7 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('5',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k8_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X0 @ X1 ) ) @ X0 )
      | ( k1_xboole_0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('10',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ k1_xboole_0 @ X0 @ X1 ) @ ( sk_E @ k1_xboole_0 @ X0 @ X1 ) ) @ X0 )
      | ( k1_xboole_0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k8_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k8_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k8_relat_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','16'])).

thf('18',plain,(
    $false ),
    inference(simplify,[status(thm)],['17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dUS0Wtv7lh
% 0.17/0.37  % Computer   : n020.cluster.edu
% 0.17/0.37  % Model      : x86_64 x86_64
% 0.17/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.37  % Memory     : 8042.1875MB
% 0.17/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.37  % CPULimit   : 60
% 0.17/0.37  % DateTime   : Tue Dec  1 14:21:52 EST 2020
% 0.17/0.37  % CPUTime    : 
% 0.17/0.37  % Running portfolio for 600 s
% 0.17/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.37  % Number of cores: 8
% 0.17/0.38  % Python version: Python 3.6.8
% 0.17/0.38  % Running in FO mode
% 0.23/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.46  % Solved by: fo/fo7.sh
% 0.23/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.46  % done 26 iterations in 0.014s
% 0.23/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.46  % SZS output start Refutation
% 0.23/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.46  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.23/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.23/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.23/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.46  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.23/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.46  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.23/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.46  thf(t138_relat_1, conjecture,
% 0.23/0.46    (![A:$i]: ( ( k8_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.23/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.46    (~( ![A:$i]: ( ( k8_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.23/0.46    inference('cnf.neg', [status(esa)], [t138_relat_1])).
% 0.23/0.46  thf('0', plain, (((k8_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.23/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.46  thf(cc1_relat_1, axiom,
% 0.23/0.46    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.23/0.46  thf('1', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.23/0.46      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.23/0.46  thf('2', plain, (![X5 : $i]: ((v1_relat_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.23/0.46      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.23/0.46  thf(d12_relat_1, axiom,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ( v1_relat_1 @ B ) =>
% 0.23/0.46       ( ![C:$i]:
% 0.23/0.46         ( ( v1_relat_1 @ C ) =>
% 0.23/0.46           ( ( ( C ) = ( k8_relat_1 @ A @ B ) ) <=>
% 0.23/0.46             ( ![D:$i,E:$i]:
% 0.23/0.46               ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) <=>
% 0.23/0.46                 ( ( r2_hidden @ E @ A ) & 
% 0.23/0.46                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) ) ))).
% 0.23/0.46  thf('3', plain,
% 0.23/0.46      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.23/0.46         (~ (v1_relat_1 @ X6)
% 0.23/0.46          | (r2_hidden @ 
% 0.23/0.46             (k4_tarski @ (sk_D @ X6 @ X8 @ X7) @ (sk_E @ X6 @ X8 @ X7)) @ X6)
% 0.23/0.46          | (r2_hidden @ 
% 0.23/0.46             (k4_tarski @ (sk_D @ X6 @ X8 @ X7) @ (sk_E @ X6 @ X8 @ X7)) @ X8)
% 0.23/0.46          | ((X6) = (k8_relat_1 @ X7 @ X8))
% 0.23/0.46          | ~ (v1_relat_1 @ X8))),
% 0.23/0.46      inference('cnf', [status(esa)], [d12_relat_1])).
% 0.23/0.46  thf(t113_zfmisc_1, axiom,
% 0.23/0.46    (![A:$i,B:$i]:
% 0.23/0.46     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.23/0.46       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.23/0.46  thf('4', plain,
% 0.23/0.46      (![X1 : $i, X2 : $i]:
% 0.23/0.46         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.23/0.46      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.23/0.46  thf('5', plain,
% 0.23/0.46      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.23/0.46      inference('simplify', [status(thm)], ['4'])).
% 0.23/0.46  thf(t152_zfmisc_1, axiom,
% 0.23/0.46    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.23/0.46  thf('6', plain,
% 0.23/0.46      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.23/0.46      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.23/0.46  thf('7', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.23/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.46  thf('8', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         (~ (v1_relat_1 @ X1)
% 0.23/0.46          | ((k1_xboole_0) = (k8_relat_1 @ X0 @ X1))
% 0.23/0.46          | (r2_hidden @ 
% 0.23/0.46             (k4_tarski @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ 
% 0.23/0.46              (sk_E @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.23/0.46             X1)
% 0.23/0.46          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.23/0.46      inference('sup-', [status(thm)], ['3', '7'])).
% 0.23/0.46  thf('9', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.23/0.46          | (r2_hidden @ 
% 0.23/0.46             (k4_tarski @ (sk_D @ k1_xboole_0 @ X0 @ X1) @ 
% 0.23/0.46              (sk_E @ k1_xboole_0 @ X0 @ X1)) @ 
% 0.23/0.46             X0)
% 0.23/0.46          | ((k1_xboole_0) = (k8_relat_1 @ X1 @ X0))
% 0.23/0.46          | ~ (v1_relat_1 @ X0))),
% 0.23/0.46      inference('sup-', [status(thm)], ['2', '8'])).
% 0.23/0.46  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.23/0.46  thf('10', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.23/0.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.23/0.46  thf('11', plain,
% 0.23/0.46      (![X0 : $i, X1 : $i]:
% 0.23/0.46         ((r2_hidden @ 
% 0.23/0.46           (k4_tarski @ (sk_D @ k1_xboole_0 @ X0 @ X1) @ 
% 0.23/0.46            (sk_E @ k1_xboole_0 @ X0 @ X1)) @ 
% 0.23/0.46           X0)
% 0.23/0.46          | ((k1_xboole_0) = (k8_relat_1 @ X1 @ X0))
% 0.23/0.46          | ~ (v1_relat_1 @ X0))),
% 0.23/0.46      inference('demod', [status(thm)], ['9', '10'])).
% 0.23/0.46  thf('12', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.23/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.23/0.46  thf('13', plain,
% 0.23/0.46      (![X0 : $i]:
% 0.23/0.46         (~ (v1_relat_1 @ k1_xboole_0)
% 0.23/0.46          | ((k1_xboole_0) = (k8_relat_1 @ X0 @ k1_xboole_0)))),
% 0.23/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.23/0.46  thf('14', plain,
% 0.23/0.46      (![X0 : $i]:
% 0.23/0.46         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.23/0.46          | ((k1_xboole_0) = (k8_relat_1 @ X0 @ k1_xboole_0)))),
% 0.23/0.46      inference('sup-', [status(thm)], ['1', '13'])).
% 0.23/0.46  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.23/0.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.23/0.46  thf('16', plain,
% 0.23/0.46      (![X0 : $i]: ((k1_xboole_0) = (k8_relat_1 @ X0 @ k1_xboole_0))),
% 0.23/0.46      inference('demod', [status(thm)], ['14', '15'])).
% 0.23/0.46  thf('17', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.23/0.46      inference('demod', [status(thm)], ['0', '16'])).
% 0.23/0.46  thf('18', plain, ($false), inference('simplify', [status(thm)], ['17'])).
% 0.23/0.46  
% 0.23/0.46  % SZS output end Refutation
% 0.23/0.46  
% 0.23/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
