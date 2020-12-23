%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l41bZJz2lQ

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   32 (  37 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :  146 ( 180 expanded)
%              Number of equality atoms :   17 (  23 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t150_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k9_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t150_relat_1])).

thf('0',plain,(
    ( k9_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_D @ X5 @ X6 @ X7 ) @ X5 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X5 @ X6 @ X7 ) @ ( sk_D @ X5 @ X6 @ X7 ) ) @ X7 )
      | ( X5
        = ( k9_relat_1 @ X7 @ X6 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i] :
      ~ ( r2_hidden @ X3 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( X1
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('7',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X13: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('12',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','12'])).

thf('14',plain,(
    $false ),
    inference(simplify,[status(thm)],['13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.l41bZJz2lQ
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:11:03 EST 2020
% 0.12/0.35  % CPUTime    : 
% 0.12/0.35  % Running portfolio for 600 s
% 0.12/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.35  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 13 iterations in 0.013s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.47  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.47  thf(t150_relat_1, conjecture,
% 0.20/0.47    (![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i]: ( ( k9_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t150_relat_1])).
% 0.20/0.47  thf('0', plain, (((k9_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(d13_relat_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ A ) =>
% 0.20/0.47       ( ![B:$i,C:$i]:
% 0.20/0.47         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.20/0.47           ( ![D:$i]:
% 0.20/0.47             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.47               ( ?[E:$i]:
% 0.20/0.47                 ( ( r2_hidden @ E @ B ) & 
% 0.20/0.47                   ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.47         ((r2_hidden @ (sk_D @ X5 @ X6 @ X7) @ X5)
% 0.20/0.47          | (r2_hidden @ 
% 0.20/0.47             (k4_tarski @ (sk_E @ X5 @ X6 @ X7) @ (sk_D @ X5 @ X6 @ X7)) @ X7)
% 0.20/0.47          | ((X5) = (k9_relat_1 @ X7 @ X6))
% 0.20/0.47          | ~ (v1_relat_1 @ X7))),
% 0.20/0.47      inference('cnf', [status(esa)], [d13_relat_1])).
% 0.20/0.47  thf(t113_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.47       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      (![X1 : $i, X2 : $i]:
% 0.20/0.47         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.47  thf(t152_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.20/0.47      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.20/0.47  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (~ (v1_relat_1 @ k1_xboole_0)
% 0.20/0.47          | ((X1) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.47          | (r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1))),
% 0.20/0.47      inference('sup-', [status(thm)], ['1', '5'])).
% 0.20/0.47  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.47  thf('7', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.47  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.47  thf('8', plain, (![X13 : $i]: (v1_relat_1 @ (k6_relat_1 @ X13))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.47  thf('9', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.47      inference('sup+', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         (((X1) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.20/0.47          | (r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1))),
% 0.20/0.47      inference('demod', [status(thm)], ['6', '9'])).
% 0.20/0.47  thf('11', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('13', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.47      inference('demod', [status(thm)], ['0', '12'])).
% 0.20/0.47  thf('14', plain, ($false), inference('simplify', [status(thm)], ['13'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
