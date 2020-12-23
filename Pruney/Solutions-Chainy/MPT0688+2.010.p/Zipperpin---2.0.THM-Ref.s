%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OjuXxk38rJ

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 (  52 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :   11
%              Number of atoms          :  327 ( 435 expanded)
%              Number of equality atoms :   29 (  40 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t143_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) )
                = k1_xboole_0 ) )
       => ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) )
                  = k1_xboole_0 ) )
         => ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t143_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
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

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('2',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_zfmisc_1 @ X20 @ X21 )
        = k1_xboole_0 )
      | ( X21 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('3',plain,(
    ! [X20: $i] :
      ( ( k2_zfmisc_1 @ X20 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['2'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('4',plain,(
    ! [X22: $i,X23: $i] :
      ~ ( r2_hidden @ X22 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('5',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['1','5'])).

thf(t142_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) )
      <=> ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) )
         != k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k1_tarski @ X25 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X25 @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t142_funct_1])).

thf('8',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k4_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k10_relat_1 @ X0 @ ( k1_tarski @ ( sk_D @ X2 @ ( k2_relat_1 @ X0 ) @ X1 ) ) )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ X2 @ ( k2_relat_1 @ X0 ) @ X1 ) @ X2 )
      | ( X2
        = ( k4_xboole_0 @ X1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ sk_A )
      | ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ X26 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k2_relat_1 @ sk_B ) @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k2_relat_1 @ sk_B ) @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k2_relat_1 @ sk_B ) @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ ( k2_relat_1 @ sk_B ) @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X1 @ ( k2_relat_1 @ sk_B ) @ X0 ) @ sk_A )
      | ( r2_hidden @ ( sk_D @ X1 @ ( k2_relat_1 @ sk_B ) @ X0 ) @ X1 )
      | ( X1
        = ( k4_xboole_0 @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) )
    | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','14'])).

thf('16',plain,
    ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('18',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( ( k4_xboole_0 @ X6 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('20',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['0','21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.OjuXxk38rJ
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:45:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 61 iterations in 0.044s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.50  thf(t143_funct_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( ![C:$i]:
% 0.20/0.50           ( ~( ( r2_hidden @ C @ A ) & 
% 0.20/0.50                ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) ) = ( k1_xboole_0 ) ) ) ) ) =>
% 0.20/0.50         ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( v1_relat_1 @ B ) =>
% 0.20/0.50          ( ( ![C:$i]:
% 0.20/0.50              ( ~( ( r2_hidden @ C @ A ) & 
% 0.20/0.50                   ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) ) = ( k1_xboole_0 ) ) ) ) ) =>
% 0.20/0.50            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t143_funct_1])).
% 0.20/0.50  thf('0', plain, (~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d5_xboole_0, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.20/0.50       ( ![D:$i]:
% 0.20/0.50         ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.50           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.20/0.50         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.20/0.50          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.20/0.50          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.50  thf(t113_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X20 : $i, X21 : $i]:
% 0.20/0.50         (((k2_zfmisc_1 @ X20 @ X21) = (k1_xboole_0))
% 0.20/0.50          | ((X21) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X20 : $i]: ((k2_zfmisc_1 @ X20 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.50      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.50  thf(t152_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      (![X22 : $i, X23 : $i]: ~ (r2_hidden @ X22 @ (k2_zfmisc_1 @ X22 @ X23))),
% 0.20/0.50      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.20/0.50  thf('5', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         ((r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.20/0.50          | ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X1)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['1', '5'])).
% 0.20/0.50  thf(t142_funct_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ B ) =>
% 0.20/0.50       ( ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) <=>
% 0.20/0.50         ( ( k10_relat_1 @ B @ ( k1_tarski @ A ) ) != ( k1_xboole_0 ) ) ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X24 : $i, X25 : $i]:
% 0.20/0.50         (((k10_relat_1 @ X24 @ (k1_tarski @ X25)) = (k1_xboole_0))
% 0.20/0.50          | (r2_hidden @ X25 @ (k2_relat_1 @ X24))
% 0.20/0.50          | ~ (v1_relat_1 @ X24))),
% 0.20/0.50      inference('cnf', [status(esa)], [t142_funct_1])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.20/0.50         (((X5) = (k4_xboole_0 @ X1 @ X2))
% 0.20/0.50          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.20/0.50          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.20/0.50  thf('9', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X0)
% 0.20/0.50          | ((k10_relat_1 @ X0 @ 
% 0.20/0.50              (k1_tarski @ (sk_D @ X2 @ (k2_relat_1 @ X0) @ X1)))
% 0.20/0.50              = (k1_xboole_0))
% 0.20/0.50          | (r2_hidden @ (sk_D @ X2 @ (k2_relat_1 @ X0) @ X1) @ X2)
% 0.20/0.50          | ((X2) = (k4_xboole_0 @ X1 @ (k2_relat_1 @ X0))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      (![X26 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X26 @ sk_A)
% 0.20/0.50          | ((k10_relat_1 @ sk_B @ (k1_tarski @ X26)) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50          | ((X1) = (k4_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))
% 0.20/0.50          | (r2_hidden @ (sk_D @ X1 @ (k2_relat_1 @ sk_B) @ X0) @ X1)
% 0.20/0.50          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.50          | ~ (r2_hidden @ (sk_D @ X1 @ (k2_relat_1 @ sk_B) @ X0) @ sk_A))),
% 0.20/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.50  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50          | ((X1) = (k4_xboole_0 @ X0 @ (k2_relat_1 @ sk_B)))
% 0.20/0.50          | (r2_hidden @ (sk_D @ X1 @ (k2_relat_1 @ sk_B) @ X0) @ X1)
% 0.20/0.50          | ~ (r2_hidden @ (sk_D @ X1 @ (k2_relat_1 @ sk_B) @ X0) @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (~ (r2_hidden @ (sk_D @ X1 @ (k2_relat_1 @ sk_B) @ X0) @ sk_A)
% 0.20/0.50          | (r2_hidden @ (sk_D @ X1 @ (k2_relat_1 @ sk_B) @ X0) @ X1)
% 0.20/0.50          | ((X1) = (k4_xboole_0 @ X0 @ (k2_relat_1 @ sk_B))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['13'])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.20/0.50        | ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))
% 0.20/0.50        | (r2_hidden @ (sk_D @ k1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A) @ 
% 0.20/0.50           k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (((r2_hidden @ (sk_D @ k1_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A) @ 
% 0.20/0.50         k1_xboole_0)
% 0.20/0.50        | ((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.50  thf('17', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.50      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (((k1_xboole_0) = (k4_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.20/0.50      inference('clc', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf(l32_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i]:
% 0.20/0.50         ((r1_tarski @ X6 @ X7) | ((k4_xboole_0 @ X6 @ X7) != (k1_xboole_0)))),
% 0.20/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.50        | (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.20/0.50      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.50  thf('22', plain, ($false), inference('demod', [status(thm)], ['0', '21'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
