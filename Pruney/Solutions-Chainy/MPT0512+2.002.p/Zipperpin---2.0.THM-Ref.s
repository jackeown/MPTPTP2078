%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bShuLP2JD3

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:24 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   52 (  70 expanded)
%              Number of leaves         :   26 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  302 ( 432 expanded)
%              Number of equality atoms :   30 (  47 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_0,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X20: $i,X21: $i,X24: $i] :
      ( ( X24
        = ( k2_zfmisc_1 @ X21 @ X20 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X24 @ X20 @ X21 ) @ ( sk_E @ X24 @ X20 @ X21 ) @ ( sk_D @ X24 @ X20 @ X21 ) @ X20 @ X21 )
      | ( r2_hidden @ ( sk_D @ X24 @ X20 @ X21 ) @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('1',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X11 @ X15 )
      | ~ ( zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ ( k3_xboole_0 @ X0 @ X1 ) )
      = X0 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X2 @ X3 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t64_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) )
    <=> ( ( r2_hidden @ A @ B )
        & ( A != C ) ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( X27 != X29 )
      | ~ ( r2_hidden @ X27 @ ( k4_xboole_0 @ X28 @ ( k1_tarski @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[t64_zfmisc_1])).

thf('7',plain,(
    ! [X28: $i,X29: $i] :
      ~ ( r2_hidden @ X29 @ ( k4_xboole_0 @ X28 @ ( k1_tarski @ X29 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( k1_xboole_0
        = ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('11',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t96_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('12',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k7_relat_1 @ X31 @ X32 )
        = ( k3_xboole_0 @ X31 @ ( k2_zfmisc_1 @ X32 @ ( k2_relat_1 @ X31 ) ) ) )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t96_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(t50_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X4 @ ( k4_xboole_0 @ X5 @ X6 ) )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X4 @ X5 ) @ ( k3_xboole_0 @ X4 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t50_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf('18',plain,(
    ! [X1: $i] :
      ( ( k3_xboole_0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','18'])).

thf(t110_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_3,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k7_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t110_relat_1])).

thf('20',plain,(
    ( k7_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('23',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    $false ),
    inference(simplify,[status(thm)],['23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bShuLP2JD3
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:04:08 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.38/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.60  % Solved by: fo/fo7.sh
% 0.38/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.60  % done 194 iterations in 0.140s
% 0.38/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.60  % SZS output start Refutation
% 0.38/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.38/0.60  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.38/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.38/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.38/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.60  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.38/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.60  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.38/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.38/0.60  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.38/0.60  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.38/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.38/0.60  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.38/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.38/0.60  thf(d2_zfmisc_1, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.38/0.60       ( ![D:$i]:
% 0.38/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.60           ( ?[E:$i,F:$i]:
% 0.38/0.60             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.38/0.60               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.38/0.60  thf(zf_stmt_0, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.38/0.60  thf(zf_stmt_1, axiom,
% 0.38/0.60    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.38/0.60     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.38/0.60       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.38/0.60         ( r2_hidden @ E @ A ) ) ))).
% 0.38/0.60  thf(zf_stmt_2, axiom,
% 0.38/0.60    (![A:$i,B:$i,C:$i]:
% 0.38/0.60     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.38/0.60       ( ![D:$i]:
% 0.38/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.38/0.60           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.38/0.60  thf('0', plain,
% 0.38/0.60      (![X20 : $i, X21 : $i, X24 : $i]:
% 0.38/0.60         (((X24) = (k2_zfmisc_1 @ X21 @ X20))
% 0.38/0.60          | (zip_tseitin_0 @ (sk_F @ X24 @ X20 @ X21) @ 
% 0.38/0.61             (sk_E @ X24 @ X20 @ X21) @ (sk_D @ X24 @ X20 @ X21) @ X20 @ X21)
% 0.38/0.61          | (r2_hidden @ (sk_D @ X24 @ X20 @ X21) @ X24))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.38/0.61  thf('1', plain,
% 0.38/0.61      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.38/0.61         ((r2_hidden @ X11 @ X15)
% 0.38/0.61          | ~ (zip_tseitin_0 @ X12 @ X11 @ X13 @ X14 @ X15))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.38/0.61  thf('2', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.61         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.38/0.61          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.38/0.61          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.38/0.61  thf(t22_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.38/0.61  thf('3', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k2_xboole_0 @ X0 @ (k3_xboole_0 @ X0 @ X1)) = (X0))),
% 0.38/0.61      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.38/0.61  thf(t46_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 0.38/0.61  thf('4', plain,
% 0.38/0.61      (![X2 : $i, X3 : $i]:
% 0.38/0.61         ((k4_xboole_0 @ X2 @ (k2_xboole_0 @ X2 @ X3)) = (k1_xboole_0))),
% 0.38/0.61      inference('cnf', [status(esa)], [t46_xboole_1])).
% 0.38/0.61  thf('5', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['3', '4'])).
% 0.38/0.61  thf(t64_zfmisc_1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( r2_hidden @ A @ ( k4_xboole_0 @ B @ ( k1_tarski @ C ) ) ) <=>
% 0.38/0.61       ( ( r2_hidden @ A @ B ) & ( ( A ) != ( C ) ) ) ))).
% 0.38/0.61  thf('6', plain,
% 0.38/0.61      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.38/0.61         (((X27) != (X29))
% 0.38/0.61          | ~ (r2_hidden @ X27 @ (k4_xboole_0 @ X28 @ (k1_tarski @ X29))))),
% 0.38/0.61      inference('cnf', [status(esa)], [t64_zfmisc_1])).
% 0.38/0.61  thf('7', plain,
% 0.38/0.61      (![X28 : $i, X29 : $i]:
% 0.38/0.61         ~ (r2_hidden @ X29 @ (k4_xboole_0 @ X28 @ (k1_tarski @ X29)))),
% 0.38/0.61      inference('simplify', [status(thm)], ['6'])).
% 0.38/0.61  thf('8', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.61      inference('sup-', [status(thm)], ['5', '7'])).
% 0.38/0.61  thf('9', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X0)
% 0.38/0.61          | ((k1_xboole_0) = (k2_zfmisc_1 @ X0 @ X1)))),
% 0.38/0.61      inference('sup-', [status(thm)], ['2', '8'])).
% 0.38/0.61  thf('10', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.38/0.61      inference('sup-', [status(thm)], ['5', '7'])).
% 0.38/0.61  thf('11', plain,
% 0.38/0.61      (![X0 : $i]: ((k1_xboole_0) = (k2_zfmisc_1 @ k1_xboole_0 @ X0))),
% 0.38/0.61      inference('sup-', [status(thm)], ['9', '10'])).
% 0.38/0.61  thf(t96_relat_1, axiom,
% 0.38/0.61    (![A:$i,B:$i]:
% 0.38/0.61     ( ( v1_relat_1 @ B ) =>
% 0.38/0.61       ( ( k7_relat_1 @ B @ A ) =
% 0.38/0.61         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.38/0.61  thf('12', plain,
% 0.38/0.61      (![X31 : $i, X32 : $i]:
% 0.38/0.61         (((k7_relat_1 @ X31 @ X32)
% 0.38/0.61            = (k3_xboole_0 @ X31 @ (k2_zfmisc_1 @ X32 @ (k2_relat_1 @ X31))))
% 0.38/0.61          | ~ (v1_relat_1 @ X31))),
% 0.38/0.61      inference('cnf', [status(esa)], [t96_relat_1])).
% 0.38/0.61  thf('13', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((k7_relat_1 @ X0 @ k1_xboole_0) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 0.38/0.61          | ~ (v1_relat_1 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['11', '12'])).
% 0.38/0.61  thf('14', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['3', '4'])).
% 0.38/0.61  thf(t50_xboole_1, axiom,
% 0.38/0.61    (![A:$i,B:$i,C:$i]:
% 0.38/0.61     ( ( k3_xboole_0 @ A @ ( k4_xboole_0 @ B @ C ) ) =
% 0.38/0.61       ( k4_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) ))).
% 0.38/0.61  thf('15', plain,
% 0.38/0.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.38/0.61         ((k3_xboole_0 @ X4 @ (k4_xboole_0 @ X5 @ X6))
% 0.38/0.61           = (k4_xboole_0 @ (k3_xboole_0 @ X4 @ X5) @ (k3_xboole_0 @ X4 @ X6)))),
% 0.38/0.61      inference('cnf', [status(esa)], [t50_xboole_1])).
% 0.38/0.61  thf('16', plain,
% 0.38/0.61      (![X0 : $i, X1 : $i]:
% 0.38/0.61         ((k3_xboole_0 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['14', '15'])).
% 0.38/0.61  thf('17', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['3', '4'])).
% 0.38/0.61  thf('18', plain,
% 0.38/0.61      (![X1 : $i]: ((k3_xboole_0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.38/0.61      inference('demod', [status(thm)], ['16', '17'])).
% 0.38/0.61  thf('19', plain,
% 0.38/0.61      (![X0 : $i]:
% 0.38/0.61         (((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.38/0.61          | ~ (v1_relat_1 @ X0))),
% 0.38/0.61      inference('sup+', [status(thm)], ['13', '18'])).
% 0.38/0.61  thf(t110_relat_1, conjecture,
% 0.38/0.61    (![A:$i]:
% 0.38/0.61     ( ( v1_relat_1 @ A ) =>
% 0.38/0.61       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.38/0.61  thf(zf_stmt_3, negated_conjecture,
% 0.38/0.61    (~( ![A:$i]:
% 0.38/0.61        ( ( v1_relat_1 @ A ) =>
% 0.38/0.61          ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) )),
% 0.38/0.61    inference('cnf.neg', [status(esa)], [t110_relat_1])).
% 0.38/0.61  thf('20', plain, (((k7_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.61  thf('21', plain,
% 0.38/0.61      ((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_A))),
% 0.38/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.61  thf('22', plain, ((v1_relat_1 @ sk_A)),
% 0.38/0.61      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.38/0.61  thf('23', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.38/0.61      inference('demod', [status(thm)], ['21', '22'])).
% 0.38/0.61  thf('24', plain, ($false), inference('simplify', [status(thm)], ['23'])).
% 0.38/0.61  
% 0.38/0.61  % SZS output end Refutation
% 0.38/0.61  
% 0.38/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
