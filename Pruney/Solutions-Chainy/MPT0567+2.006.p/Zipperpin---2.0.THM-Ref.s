%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3kRqEVoGcF

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:42 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   40 (  53 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :   12
%              Number of atoms          :  248 ( 363 expanded)
%              Number of equality atoms :   35 (  47 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(d14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ ( sk_D @ X14 @ X15 @ X16 ) @ X14 )
      | ( r2_hidden @ ( sk_E @ X14 @ X15 @ X16 ) @ X15 )
      | ( X14
        = ( k10_relat_1 @ X16 @ X15 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf(t17_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( A != B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X9 ) @ ( k1_tarski @ X10 ) )
      | ( X9 = X10 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( ( k3_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ ( k3_xboole_0 @ X3 @ X6 ) )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ k1_xboole_0 )
      | ( X1 = X0 )
      | ~ ( r1_xboole_0 @ ( k1_tarski @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X9 ) @ ( k1_tarski @ X10 ) )
      | ( X9 = X10 ) ) ),
    inference(cnf,[status(esa)],[t17_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X2 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k10_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X1 )
      | ( X2 = X3 ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X0 )
      | ~ ( r2_hidden @ X2 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['5','6'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( X3 = X4 )
      | ( k1_xboole_0
        = ( k10_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X1 = X2 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t171_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( k10_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t171_relat_1])).

thf('11',plain,(
    ( k10_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = X1 )
      | ~ ( v1_relat_1 @ sk_A )
      | ( X2 = X3 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( X0 = X1 )
      | ( X2 = X3 ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X2 = X3 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] : ( X0 = X1 ) ),
    inference(condensation,[status(thm)],['15'])).

thf(t20_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) )
        = ( k1_tarski @ A ) )
    <=> ( A != B ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( ( X12 != X11 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X12 ) @ ( k1_tarski @ X11 ) )
       != ( k1_tarski @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t20_zfmisc_1])).

thf('18',plain,(
    ! [X11: $i] :
      ( ( k4_xboole_0 @ ( k1_tarski @ X11 ) @ ( k1_tarski @ X11 ) )
     != ( k1_tarski @ X11 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
     != ( k1_tarski @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3kRqEVoGcF
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:07:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.71  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.71  % Solved by: fo/fo7.sh
% 0.44/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.71  % done 76 iterations in 0.252s
% 0.44/0.71  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.71  % SZS output start Refutation
% 0.44/0.71  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.44/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.71  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.44/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.71  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.44/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.71  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.44/0.71  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.44/0.71  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.44/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.71  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.44/0.71  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.44/0.71  thf(d14_relat_1, axiom,
% 0.44/0.71    (![A:$i]:
% 0.44/0.71     ( ( v1_relat_1 @ A ) =>
% 0.44/0.71       ( ![B:$i,C:$i]:
% 0.44/0.71         ( ( ( C ) = ( k10_relat_1 @ A @ B ) ) <=>
% 0.44/0.71           ( ![D:$i]:
% 0.44/0.71             ( ( r2_hidden @ D @ C ) <=>
% 0.44/0.71               ( ?[E:$i]:
% 0.44/0.71                 ( ( r2_hidden @ E @ B ) & 
% 0.44/0.71                   ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) ) ))).
% 0.44/0.71  thf('0', plain,
% 0.44/0.71      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.71         ((r2_hidden @ (sk_D @ X14 @ X15 @ X16) @ X14)
% 0.44/0.71          | (r2_hidden @ (sk_E @ X14 @ X15 @ X16) @ X15)
% 0.44/0.71          | ((X14) = (k10_relat_1 @ X16 @ X15))
% 0.44/0.71          | ~ (v1_relat_1 @ X16))),
% 0.44/0.71      inference('cnf', [status(esa)], [d14_relat_1])).
% 0.44/0.71  thf(t17_zfmisc_1, axiom,
% 0.44/0.71    (![A:$i,B:$i]:
% 0.44/0.71     ( ( ( A ) != ( B ) ) =>
% 0.44/0.71       ( r1_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.44/0.71  thf('1', plain,
% 0.44/0.71      (![X9 : $i, X10 : $i]:
% 0.44/0.71         ((r1_xboole_0 @ (k1_tarski @ X9) @ (k1_tarski @ X10)) | ((X9) = (X10)))),
% 0.44/0.71      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.44/0.71  thf(d7_xboole_0, axiom,
% 0.44/0.71    (![A:$i,B:$i]:
% 0.44/0.71     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.44/0.71       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.71  thf('2', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]:
% 0.44/0.71         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.44/0.71      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.44/0.71  thf('3', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i]:
% 0.44/0.71         (((X1) = (X0))
% 0.44/0.71          | ((k3_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0))
% 0.44/0.71              = (k1_xboole_0)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.71  thf(t4_xboole_0, axiom,
% 0.44/0.71    (![A:$i,B:$i]:
% 0.44/0.71     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.44/0.71            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.44/0.71       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.44/0.71            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.44/0.71  thf('4', plain,
% 0.44/0.71      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.44/0.71         (~ (r2_hidden @ X5 @ (k3_xboole_0 @ X3 @ X6))
% 0.44/0.71          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.44/0.71      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.44/0.71  thf('5', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.71         (~ (r2_hidden @ X2 @ k1_xboole_0)
% 0.44/0.71          | ((X1) = (X0))
% 0.44/0.71          | ~ (r1_xboole_0 @ (k1_tarski @ X1) @ (k1_tarski @ X0)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['3', '4'])).
% 0.44/0.71  thf('6', plain,
% 0.44/0.71      (![X9 : $i, X10 : $i]:
% 0.44/0.71         ((r1_xboole_0 @ (k1_tarski @ X9) @ (k1_tarski @ X10)) | ((X9) = (X10)))),
% 0.44/0.71      inference('cnf', [status(esa)], [t17_zfmisc_1])).
% 0.44/0.71  thf('7', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.71         (((X1) = (X0)) | ~ (r2_hidden @ X2 @ k1_xboole_0))),
% 0.44/0.71      inference('clc', [status(thm)], ['5', '6'])).
% 0.44/0.71  thf('8', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.71         (~ (v1_relat_1 @ X0)
% 0.44/0.71          | ((k1_xboole_0) = (k10_relat_1 @ X0 @ X1))
% 0.44/0.71          | (r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X1)
% 0.44/0.71          | ((X2) = (X3)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['0', '7'])).
% 0.44/0.71  thf('9', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.71         (((X1) = (X0)) | ~ (r2_hidden @ X2 @ k1_xboole_0))),
% 0.44/0.71      inference('clc', [status(thm)], ['5', '6'])).
% 0.44/0.71  thf('10', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.44/0.71         (((X3) = (X4))
% 0.44/0.71          | ((k1_xboole_0) = (k10_relat_1 @ X0 @ k1_xboole_0))
% 0.44/0.71          | ~ (v1_relat_1 @ X0)
% 0.44/0.71          | ((X1) = (X2)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.71  thf(t171_relat_1, conjecture,
% 0.44/0.71    (![A:$i]:
% 0.44/0.71     ( ( v1_relat_1 @ A ) =>
% 0.44/0.71       ( ( k10_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.71    (~( ![A:$i]:
% 0.44/0.71        ( ( v1_relat_1 @ A ) =>
% 0.44/0.71          ( ( k10_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) )),
% 0.44/0.71    inference('cnf.neg', [status(esa)], [t171_relat_1])).
% 0.44/0.71  thf('11', plain, (((k10_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('12', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.71         (((k1_xboole_0) != (k1_xboole_0))
% 0.44/0.71          | ((X0) = (X1))
% 0.44/0.71          | ~ (v1_relat_1 @ sk_A)
% 0.44/0.71          | ((X2) = (X3)))),
% 0.44/0.71      inference('sup-', [status(thm)], ['10', '11'])).
% 0.44/0.71  thf('13', plain, ((v1_relat_1 @ sk_A)),
% 0.44/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.71  thf('14', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.71         (((k1_xboole_0) != (k1_xboole_0)) | ((X0) = (X1)) | ((X2) = (X3)))),
% 0.44/0.71      inference('demod', [status(thm)], ['12', '13'])).
% 0.44/0.71  thf('15', plain,
% 0.44/0.71      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]: (((X2) = (X3)) | ((X0) = (X1)))),
% 0.44/0.71      inference('simplify', [status(thm)], ['14'])).
% 0.44/0.71  thf('16', plain, (![X0 : $i, X1 : $i]: ((X0) = (X1))),
% 0.44/0.71      inference('condensation', [status(thm)], ['15'])).
% 0.44/0.71  thf(t20_zfmisc_1, axiom,
% 0.44/0.71    (![A:$i,B:$i]:
% 0.44/0.71     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) =
% 0.44/0.71         ( k1_tarski @ A ) ) <=>
% 0.44/0.71       ( ( A ) != ( B ) ) ))).
% 0.44/0.71  thf('17', plain,
% 0.44/0.71      (![X11 : $i, X12 : $i]:
% 0.44/0.71         (((X12) != (X11))
% 0.44/0.71          | ((k4_xboole_0 @ (k1_tarski @ X12) @ (k1_tarski @ X11))
% 0.44/0.71              != (k1_tarski @ X12)))),
% 0.44/0.71      inference('cnf', [status(esa)], [t20_zfmisc_1])).
% 0.44/0.71  thf('18', plain,
% 0.44/0.71      (![X11 : $i]:
% 0.44/0.71         ((k4_xboole_0 @ (k1_tarski @ X11) @ (k1_tarski @ X11))
% 0.44/0.71           != (k1_tarski @ X11))),
% 0.44/0.71      inference('simplify', [status(thm)], ['17'])).
% 0.44/0.71  thf('19', plain, (![X0 : $i, X1 : $i]: ((X0) != (k1_tarski @ X1))),
% 0.44/0.71      inference('sup-', [status(thm)], ['16', '18'])).
% 0.44/0.71  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 0.44/0.71  
% 0.44/0.71  % SZS output end Refutation
% 0.44/0.71  
% 0.44/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
