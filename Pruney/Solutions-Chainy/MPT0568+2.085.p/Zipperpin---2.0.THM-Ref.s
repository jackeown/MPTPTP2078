%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wMPCk3uENo

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:59 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   40 (  46 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  220 ( 259 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('0',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ( ( k4_xboole_0 @ X12 @ ( k1_tarski @ X11 ) )
       != X12 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X6: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ ( k10_relat_1 @ X19 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ X18 @ ( sk_D_1 @ X19 @ X17 @ X18 ) ) @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k10_relat_1 @ X1 @ X0 ) @ X2 @ k1_xboole_0 ) @ ( sk_D_1 @ X1 @ X0 @ ( sk_D @ ( k10_relat_1 @ X1 @ X0 ) @ X2 @ k1_xboole_0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('12',plain,(
    ! [X1: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k10_relat_1 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X9 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('14',plain,(
    ! [X10: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X10 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X1: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['12','16'])).

thf('18',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.wMPCk3uENo
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:01:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.72  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.72  % Solved by: fo/fo7.sh
% 0.49/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.72  % done 335 iterations in 0.275s
% 0.49/0.72  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.72  % SZS output start Refutation
% 0.49/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.72  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.49/0.72  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.49/0.72  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.49/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.72  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i > $i).
% 0.49/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.72  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.49/0.72  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.49/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.72  thf(t172_relat_1, conjecture,
% 0.49/0.72    (![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.49/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.72    (~( ![A:$i]: ( ( k10_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) )),
% 0.49/0.72    inference('cnf.neg', [status(esa)], [t172_relat_1])).
% 0.49/0.72  thf('0', plain, (((k10_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.72  thf(d5_xboole_0, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.49/0.72       ( ![D:$i]:
% 0.49/0.72         ( ( r2_hidden @ D @ C ) <=>
% 0.49/0.72           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.49/0.72  thf('1', plain,
% 0.49/0.72      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.49/0.72         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.49/0.72          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.49/0.72          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.49/0.72      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.49/0.72  thf(t4_boole, axiom,
% 0.49/0.72    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.49/0.72  thf('2', plain,
% 0.49/0.72      (![X6 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.49/0.72      inference('cnf', [status(esa)], [t4_boole])).
% 0.49/0.72  thf(t65_zfmisc_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.49/0.72       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.49/0.72  thf('3', plain,
% 0.49/0.72      (![X11 : $i, X12 : $i]:
% 0.49/0.72         (~ (r2_hidden @ X11 @ X12)
% 0.49/0.72          | ((k4_xboole_0 @ X12 @ (k1_tarski @ X11)) != (X12)))),
% 0.49/0.72      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.49/0.72  thf('4', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['2', '3'])).
% 0.49/0.72  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.49/0.72      inference('simplify', [status(thm)], ['4'])).
% 0.49/0.72  thf('6', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.49/0.72          | ((X1) = (k4_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['1', '5'])).
% 0.49/0.72  thf('7', plain,
% 0.49/0.72      (![X6 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.49/0.72      inference('cnf', [status(esa)], [t4_boole])).
% 0.49/0.72  thf('8', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]:
% 0.49/0.72         ((r2_hidden @ (sk_D @ X1 @ X0 @ k1_xboole_0) @ X1)
% 0.49/0.72          | ((X1) = (k1_xboole_0)))),
% 0.49/0.72      inference('demod', [status(thm)], ['6', '7'])).
% 0.49/0.72  thf(t166_relat_1, axiom,
% 0.49/0.72    (![A:$i,B:$i,C:$i]:
% 0.49/0.72     ( ( v1_relat_1 @ C ) =>
% 0.49/0.72       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.49/0.72         ( ?[D:$i]:
% 0.49/0.72           ( ( r2_hidden @ D @ B ) & 
% 0.49/0.72             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.49/0.72             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.49/0.72  thf('9', plain,
% 0.49/0.72      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.49/0.72         (~ (r2_hidden @ X18 @ (k10_relat_1 @ X19 @ X17))
% 0.49/0.72          | (r2_hidden @ (k4_tarski @ X18 @ (sk_D_1 @ X19 @ X17 @ X18)) @ X19)
% 0.49/0.72          | ~ (v1_relat_1 @ X19))),
% 0.49/0.72      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.49/0.72  thf('10', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         (((k10_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 0.49/0.72          | ~ (v1_relat_1 @ X1)
% 0.49/0.72          | (r2_hidden @ 
% 0.49/0.72             (k4_tarski @ 
% 0.49/0.72              (sk_D @ (k10_relat_1 @ X1 @ X0) @ X2 @ k1_xboole_0) @ 
% 0.49/0.72              (sk_D_1 @ X1 @ X0 @ 
% 0.49/0.72               (sk_D @ (k10_relat_1 @ X1 @ X0) @ X2 @ k1_xboole_0))) @ 
% 0.49/0.72             X1))),
% 0.49/0.72      inference('sup-', [status(thm)], ['8', '9'])).
% 0.49/0.72  thf('11', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.49/0.72      inference('simplify', [status(thm)], ['4'])).
% 0.49/0.72  thf('12', plain,
% 0.49/0.72      (![X1 : $i]:
% 0.49/0.72         (~ (v1_relat_1 @ k1_xboole_0)
% 0.49/0.72          | ((k10_relat_1 @ k1_xboole_0 @ X1) = (k1_xboole_0)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['10', '11'])).
% 0.49/0.72  thf(t113_zfmisc_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]:
% 0.49/0.72     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.49/0.72       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.49/0.72  thf('13', plain,
% 0.49/0.72      (![X9 : $i, X10 : $i]:
% 0.49/0.72         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X9) != (k1_xboole_0)))),
% 0.49/0.72      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.49/0.72  thf('14', plain,
% 0.49/0.72      (![X10 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X10) = (k1_xboole_0))),
% 0.49/0.72      inference('simplify', [status(thm)], ['13'])).
% 0.49/0.72  thf(fc6_relat_1, axiom,
% 0.49/0.72    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.49/0.72  thf('15', plain,
% 0.49/0.72      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X14 @ X15))),
% 0.49/0.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.49/0.72  thf('16', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.49/0.72      inference('sup+', [status(thm)], ['14', '15'])).
% 0.49/0.72  thf('17', plain,
% 0.49/0.72      (![X1 : $i]: ((k10_relat_1 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['12', '16'])).
% 0.49/0.72  thf('18', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['0', '17'])).
% 0.49/0.72  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.49/0.72  
% 0.49/0.72  % SZS output end Refutation
% 0.49/0.72  
% 0.58/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
