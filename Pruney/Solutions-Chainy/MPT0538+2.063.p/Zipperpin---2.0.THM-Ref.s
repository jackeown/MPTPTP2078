%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.duiPKmgt6v

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:57 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :  133 ( 140 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf(t137_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( ( k8_relat_1 @ k1_xboole_0 @ X6 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t137_relat_1])).

thf('2',plain,(
    ! [X6: $i] :
      ( ( ( k8_relat_1 @ k1_xboole_0 @ X6 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t137_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('3',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t129_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf('4',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X5 )
      | ( ( k8_relat_1 @ X4 @ ( k8_relat_1 @ X3 @ X5 ) )
        = ( k8_relat_1 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t129_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ k1_xboole_0 @ X1 ) )
        = ( k8_relat_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X1 @ k1_xboole_0 )
        = ( k8_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k8_relat_1 @ X1 @ k1_xboole_0 )
        = ( k8_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k8_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf(t138_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k8_relat_1 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k8_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t138_relat_1])).

thf('10',plain,(
    ( k8_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ~ ( v1_relat_1 @ X0 ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.duiPKmgt6v
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:50:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.18/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.18/0.45  % Solved by: fo/fo7.sh
% 0.18/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.18/0.45  % done 12 iterations in 0.014s
% 0.18/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.18/0.45  % SZS output start Refutation
% 0.18/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.18/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.18/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.18/0.45  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.18/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.18/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.18/0.45  thf(fc6_relat_1, axiom,
% 0.18/0.45    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.18/0.45  thf('0', plain,
% 0.18/0.45      (![X1 : $i, X2 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X2))),
% 0.18/0.45      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.18/0.45  thf(t137_relat_1, axiom,
% 0.18/0.45    (![A:$i]:
% 0.18/0.45     ( ( v1_relat_1 @ A ) =>
% 0.18/0.45       ( ( k8_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.18/0.45  thf('1', plain,
% 0.18/0.45      (![X6 : $i]:
% 0.18/0.45         (((k8_relat_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))
% 0.18/0.45          | ~ (v1_relat_1 @ X6))),
% 0.18/0.45      inference('cnf', [status(esa)], [t137_relat_1])).
% 0.18/0.45  thf('2', plain,
% 0.18/0.45      (![X6 : $i]:
% 0.18/0.45         (((k8_relat_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))
% 0.18/0.45          | ~ (v1_relat_1 @ X6))),
% 0.18/0.45      inference('cnf', [status(esa)], [t137_relat_1])).
% 0.18/0.45  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.18/0.45  thf('3', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.18/0.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.18/0.45  thf(t129_relat_1, axiom,
% 0.18/0.45    (![A:$i,B:$i,C:$i]:
% 0.18/0.45     ( ( v1_relat_1 @ C ) =>
% 0.18/0.45       ( ( r1_tarski @ A @ B ) =>
% 0.18/0.45         ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.18/0.45  thf('4', plain,
% 0.18/0.45      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.18/0.45         (~ (r1_tarski @ X3 @ X4)
% 0.18/0.45          | ~ (v1_relat_1 @ X5)
% 0.18/0.45          | ((k8_relat_1 @ X4 @ (k8_relat_1 @ X3 @ X5))
% 0.18/0.45              = (k8_relat_1 @ X3 @ X5)))),
% 0.18/0.45      inference('cnf', [status(esa)], [t129_relat_1])).
% 0.18/0.45  thf('5', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i]:
% 0.18/0.45         (((k8_relat_1 @ X0 @ (k8_relat_1 @ k1_xboole_0 @ X1))
% 0.18/0.45            = (k8_relat_1 @ k1_xboole_0 @ X1))
% 0.18/0.45          | ~ (v1_relat_1 @ X1))),
% 0.18/0.45      inference('sup-', [status(thm)], ['3', '4'])).
% 0.18/0.45  thf('6', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i]:
% 0.18/0.45         (((k8_relat_1 @ X1 @ k1_xboole_0) = (k8_relat_1 @ k1_xboole_0 @ X0))
% 0.18/0.45          | ~ (v1_relat_1 @ X0)
% 0.18/0.45          | ~ (v1_relat_1 @ X0))),
% 0.18/0.45      inference('sup+', [status(thm)], ['2', '5'])).
% 0.18/0.45  thf('7', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i]:
% 0.18/0.45         (~ (v1_relat_1 @ X0)
% 0.18/0.45          | ((k8_relat_1 @ X1 @ k1_xboole_0) = (k8_relat_1 @ k1_xboole_0 @ X0)))),
% 0.18/0.45      inference('simplify', [status(thm)], ['6'])).
% 0.18/0.45  thf('8', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i]:
% 0.18/0.45         (((k8_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.18/0.45          | ~ (v1_relat_1 @ X1)
% 0.18/0.45          | ~ (v1_relat_1 @ X1))),
% 0.18/0.45      inference('sup+', [status(thm)], ['1', '7'])).
% 0.18/0.45  thf('9', plain,
% 0.18/0.45      (![X0 : $i, X1 : $i]:
% 0.18/0.45         (~ (v1_relat_1 @ X1)
% 0.18/0.45          | ((k8_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.18/0.45      inference('simplify', [status(thm)], ['8'])).
% 0.18/0.45  thf(t138_relat_1, conjecture,
% 0.18/0.45    (![A:$i]: ( ( k8_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.18/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.18/0.45    (~( ![A:$i]: ( ( k8_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.18/0.45    inference('cnf.neg', [status(esa)], [t138_relat_1])).
% 0.18/0.45  thf('10', plain, (((k8_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.18/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.18/0.45  thf('11', plain,
% 0.18/0.45      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ X0))),
% 0.18/0.45      inference('sup-', [status(thm)], ['9', '10'])).
% 0.18/0.45  thf('12', plain, (![X0 : $i]: ~ (v1_relat_1 @ X0)),
% 0.18/0.45      inference('simplify', [status(thm)], ['11'])).
% 0.18/0.45  thf('13', plain, ($false), inference('sup-', [status(thm)], ['0', '12'])).
% 0.18/0.45  
% 0.18/0.45  % SZS output end Refutation
% 0.18/0.45  
% 0.18/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
