%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1Hf8q6t0TF

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:20 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :  195 ( 239 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_wellord1_type,type,(
    k1_wellord1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(d1_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k1_wellord1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ( ( D != B )
                & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_D @ X8 @ X9 @ X10 ) @ X8 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X8 @ X9 @ X10 ) @ X9 ) @ X10 )
      | ( X8
        = ( k1_wellord1 @ X10 @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d1_wellord1])).

thf(t30_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X5 @ X6 ) @ X7 )
      | ( r2_hidden @ X6 @ ( k3_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t30_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X2
        = ( k1_wellord1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k1_wellord1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

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
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k1_wellord1 @ X0 @ X1 ) )
      | ( r2_hidden @ X1 @ ( k3_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','7'])).

thf(t2_wellord1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) )
        | ( ( k1_wellord1 @ B @ A )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) )
          | ( ( k1_wellord1 @ B @ A )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t2_wellord1])).

thf('9',plain,(
    ~ ( r2_hidden @ sk_A @ ( k3_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k1_xboole_0
      = ( k1_wellord1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( k1_xboole_0
    = ( k1_wellord1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ( k1_wellord1 @ sk_B @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['12','13'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1Hf8q6t0TF
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:34:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.43  % Solved by: fo/fo7.sh
% 0.20/0.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.43  % done 15 iterations in 0.013s
% 0.20/0.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.43  % SZS output start Refutation
% 0.20/0.43  thf(k1_wellord1_type, type, k1_wellord1: $i > $i > $i).
% 0.20/0.43  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.43  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.43  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.43  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.43  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.43  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.43  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 0.20/0.43  thf(d1_wellord1, axiom,
% 0.20/0.43    (![A:$i]:
% 0.20/0.43     ( ( v1_relat_1 @ A ) =>
% 0.20/0.43       ( ![B:$i,C:$i]:
% 0.20/0.43         ( ( ( C ) = ( k1_wellord1 @ A @ B ) ) <=>
% 0.20/0.43           ( ![D:$i]:
% 0.20/0.43             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.43               ( ( ( D ) != ( B ) ) & ( r2_hidden @ ( k4_tarski @ D @ B ) @ A ) ) ) ) ) ) ))).
% 0.20/0.43  thf('0', plain,
% 0.20/0.43      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.43         ((r2_hidden @ (sk_D @ X8 @ X9 @ X10) @ X8)
% 0.20/0.43          | (r2_hidden @ (k4_tarski @ (sk_D @ X8 @ X9 @ X10) @ X9) @ X10)
% 0.20/0.43          | ((X8) = (k1_wellord1 @ X10 @ X9))
% 0.20/0.43          | ~ (v1_relat_1 @ X10))),
% 0.20/0.43      inference('cnf', [status(esa)], [d1_wellord1])).
% 0.20/0.43  thf(t30_relat_1, axiom,
% 0.20/0.43    (![A:$i,B:$i,C:$i]:
% 0.20/0.43     ( ( v1_relat_1 @ C ) =>
% 0.20/0.43       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.20/0.43         ( ( r2_hidden @ A @ ( k3_relat_1 @ C ) ) & 
% 0.20/0.43           ( r2_hidden @ B @ ( k3_relat_1 @ C ) ) ) ) ))).
% 0.20/0.43  thf('1', plain,
% 0.20/0.43      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.43         (~ (r2_hidden @ (k4_tarski @ X5 @ X6) @ X7)
% 0.20/0.43          | (r2_hidden @ X6 @ (k3_relat_1 @ X7))
% 0.20/0.43          | ~ (v1_relat_1 @ X7))),
% 0.20/0.43      inference('cnf', [status(esa)], [t30_relat_1])).
% 0.20/0.43  thf('2', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.43         (~ (v1_relat_1 @ X0)
% 0.20/0.43          | ((X2) = (k1_wellord1 @ X0 @ X1))
% 0.20/0.43          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.20/0.43          | ~ (v1_relat_1 @ X0)
% 0.20/0.43          | (r2_hidden @ X1 @ (k3_relat_1 @ X0)))),
% 0.20/0.43      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.43  thf('3', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.43         ((r2_hidden @ X1 @ (k3_relat_1 @ X0))
% 0.20/0.43          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.20/0.43          | ((X2) = (k1_wellord1 @ X0 @ X1))
% 0.20/0.43          | ~ (v1_relat_1 @ X0))),
% 0.20/0.43      inference('simplify', [status(thm)], ['2'])).
% 0.20/0.43  thf(t113_zfmisc_1, axiom,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.43       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.43  thf('4', plain,
% 0.20/0.43      (![X1 : $i, X2 : $i]:
% 0.20/0.43         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.20/0.43      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.20/0.43  thf('5', plain,
% 0.20/0.43      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.43      inference('simplify', [status(thm)], ['4'])).
% 0.20/0.43  thf(t152_zfmisc_1, axiom,
% 0.20/0.43    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.20/0.43  thf('6', plain,
% 0.20/0.43      (![X3 : $i, X4 : $i]: ~ (r2_hidden @ X3 @ (k2_zfmisc_1 @ X3 @ X4))),
% 0.20/0.43      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.20/0.43  thf('7', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.43      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.43  thf('8', plain,
% 0.20/0.43      (![X0 : $i, X1 : $i]:
% 0.20/0.43         (~ (v1_relat_1 @ X0)
% 0.20/0.43          | ((k1_xboole_0) = (k1_wellord1 @ X0 @ X1))
% 0.20/0.43          | (r2_hidden @ X1 @ (k3_relat_1 @ X0)))),
% 0.20/0.43      inference('sup-', [status(thm)], ['3', '7'])).
% 0.20/0.43  thf(t2_wellord1, conjecture,
% 0.20/0.43    (![A:$i,B:$i]:
% 0.20/0.43     ( ( v1_relat_1 @ B ) =>
% 0.20/0.43       ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) ) | 
% 0.20/0.43         ( ( k1_wellord1 @ B @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.20/0.43  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.43    (~( ![A:$i,B:$i]:
% 0.20/0.43        ( ( v1_relat_1 @ B ) =>
% 0.20/0.43          ( ( r2_hidden @ A @ ( k3_relat_1 @ B ) ) | 
% 0.20/0.43            ( ( k1_wellord1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) )),
% 0.20/0.43    inference('cnf.neg', [status(esa)], [t2_wellord1])).
% 0.20/0.43  thf('9', plain, (~ (r2_hidden @ sk_A @ (k3_relat_1 @ sk_B))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('10', plain,
% 0.20/0.43      ((((k1_xboole_0) = (k1_wellord1 @ sk_B @ sk_A)) | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.43      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.43  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('12', plain, (((k1_xboole_0) = (k1_wellord1 @ sk_B @ sk_A))),
% 0.20/0.43      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.43  thf('13', plain, (((k1_wellord1 @ sk_B @ sk_A) != (k1_xboole_0))),
% 0.20/0.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.43  thf('14', plain, ($false),
% 0.20/0.43      inference('simplify_reflect-', [status(thm)], ['12', '13'])).
% 0.20/0.43  
% 0.20/0.43  % SZS output end Refutation
% 0.20/0.43  
% 0.20/0.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
