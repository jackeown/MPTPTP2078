%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Szuq5dKUWu

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:57 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  53 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :  186 ( 256 expanded)
%              Number of equality atoms :   26 (  37 expanded)
%              Maximal formula depth    :   10 (   4 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

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

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X7 ) )
      = X7 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t126_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A )
        = A ) ) )).

thf('2',plain,(
    ! [X2: $i] :
      ( ( ( k8_relat_1 @ ( k2_relat_1 @ X2 ) @ X2 )
        = X2 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t126_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X1: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('6',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t129_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) )
          = ( k8_relat_1 @ A @ C ) ) ) ) )).

thf('7',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( v1_relat_1 @ X5 )
      | ( ( k8_relat_1 @ X4 @ ( k8_relat_1 @ X3 @ X5 ) )
        = ( k8_relat_1 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t129_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k8_relat_1 @ k1_xboole_0 @ X1 ) )
        = ( k8_relat_1 @ k1_xboole_0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ k1_xboole_0 ) )
        = ( k8_relat_1 @ k1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['5','8'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('10',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('11',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('12',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('14',plain,
    ( ( k8_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('16',plain,
    ( ( k8_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('18',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('19',plain,(
    ! [X1: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('20',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','10','11','16','17','20'])).

thf('22',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','21'])).

thf('23',plain,(
    $false ),
    inference(simplify,[status(thm)],['22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Szuq5dKUWu
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:35:34 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.45  % Solved by: fo/fo7.sh
% 0.20/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.45  % done 15 iterations in 0.007s
% 0.20/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.45  % SZS output start Refutation
% 0.20/0.45  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.45  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.20/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.45  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.45  thf(t138_relat_1, conjecture,
% 0.20/0.45    (![A:$i]: ( ( k8_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.45    (~( ![A:$i]: ( ( k8_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.20/0.45    inference('cnf.neg', [status(esa)], [t138_relat_1])).
% 0.20/0.45  thf('0', plain, (((k8_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.45  thf(t71_relat_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.20/0.45       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.20/0.45  thf('1', plain, (![X7 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X7)) = (X7))),
% 0.20/0.45      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.20/0.45  thf(t126_relat_1, axiom,
% 0.20/0.45    (![A:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ A ) =>
% 0.20/0.45       ( ( k8_relat_1 @ ( k2_relat_1 @ A ) @ A ) = ( A ) ) ))).
% 0.20/0.45  thf('2', plain,
% 0.20/0.45      (![X2 : $i]:
% 0.20/0.45         (((k8_relat_1 @ (k2_relat_1 @ X2) @ X2) = (X2)) | ~ (v1_relat_1 @ X2))),
% 0.20/0.45      inference('cnf', [status(esa)], [t126_relat_1])).
% 0.20/0.45  thf('3', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))
% 0.20/0.45          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.20/0.45      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.45  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 0.20/0.45  thf('4', plain, (![X1 : $i]: (v1_relat_1 @ (k6_relat_1 @ X1))),
% 0.20/0.45      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.45  thf('5', plain,
% 0.20/0.45      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.20/0.45      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.45  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.45  thf('6', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.45      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.45  thf(t129_relat_1, axiom,
% 0.20/0.45    (![A:$i,B:$i,C:$i]:
% 0.20/0.45     ( ( v1_relat_1 @ C ) =>
% 0.20/0.45       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.45         ( ( k8_relat_1 @ B @ ( k8_relat_1 @ A @ C ) ) = ( k8_relat_1 @ A @ C ) ) ) ))).
% 0.20/0.45  thf('7', plain,
% 0.20/0.45      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.45         (~ (r1_tarski @ X3 @ X4)
% 0.20/0.45          | ~ (v1_relat_1 @ X5)
% 0.20/0.45          | ((k8_relat_1 @ X4 @ (k8_relat_1 @ X3 @ X5))
% 0.20/0.45              = (k8_relat_1 @ X3 @ X5)))),
% 0.20/0.45      inference('cnf', [status(esa)], [t129_relat_1])).
% 0.20/0.45  thf('8', plain,
% 0.20/0.45      (![X0 : $i, X1 : $i]:
% 0.20/0.45         (((k8_relat_1 @ X0 @ (k8_relat_1 @ k1_xboole_0 @ X1))
% 0.20/0.45            = (k8_relat_1 @ k1_xboole_0 @ X1))
% 0.20/0.45          | ~ (v1_relat_1 @ X1))),
% 0.20/0.45      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.45  thf('9', plain,
% 0.20/0.45      (![X0 : $i]:
% 0.20/0.45         (((k8_relat_1 @ X0 @ (k6_relat_1 @ k1_xboole_0))
% 0.20/0.45            = (k8_relat_1 @ k1_xboole_0 @ (k6_relat_1 @ k1_xboole_0)))
% 0.20/0.45          | ~ (v1_relat_1 @ (k6_relat_1 @ k1_xboole_0)))),
% 0.20/0.45      inference('sup+', [status(thm)], ['5', '8'])).
% 0.20/0.45  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.20/0.45  thf('10', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.45      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.45  thf('11', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.45      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.45  thf('12', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.45      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.45  thf('13', plain,
% 0.20/0.45      (![X0 : $i]: ((k8_relat_1 @ X0 @ (k6_relat_1 @ X0)) = (k6_relat_1 @ X0))),
% 0.20/0.45      inference('demod', [status(thm)], ['3', '4'])).
% 0.20/0.45  thf('14', plain,
% 0.20/0.45      (((k8_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 0.20/0.45      inference('sup+', [status(thm)], ['12', '13'])).
% 0.20/0.45  thf('15', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.45      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.45  thf('16', plain,
% 0.20/0.45      (((k8_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.45      inference('demod', [status(thm)], ['14', '15'])).
% 0.20/0.45  thf('17', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.45      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.45  thf('18', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.45      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.20/0.45  thf('19', plain, (![X1 : $i]: (v1_relat_1 @ (k6_relat_1 @ X1))),
% 0.20/0.45      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 0.20/0.45  thf('20', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.20/0.45      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.45  thf('21', plain,
% 0.20/0.45      (![X0 : $i]: ((k8_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.45      inference('demod', [status(thm)], ['9', '10', '11', '16', '17', '20'])).
% 0.20/0.45  thf('22', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.20/0.45      inference('demod', [status(thm)], ['0', '21'])).
% 0.20/0.45  thf('23', plain, ($false), inference('simplify', [status(thm)], ['22'])).
% 0.20/0.45  
% 0.20/0.45  % SZS output end Refutation
% 0.20/0.45  
% 0.20/0.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
