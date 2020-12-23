%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.shzGEyzQ4y

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:49 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  43 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :   10
%              Number of atoms          :  186 ( 194 expanded)
%              Number of equality atoms :   25 (  26 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X35: $i] :
      ( ( v1_relat_1 @ X35 )
      | ~ ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ X1 @ X0 )
      = ( k5_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('3',plain,(
    ! [X5: $i] :
      ( ( k5_xboole_0 @ X5 @ k1_xboole_0 )
      = X5 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k4_xboole_0 @ X2 @ X3 )
      = ( k5_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X4: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('8',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k1_setfam_1 @ ( k2_tarski @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t124_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k8_relat_1 @ A @ B )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) )).

thf('11',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k8_relat_1 @ X37 @ X36 )
        = ( k3_xboole_0 @ X36 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X36 ) @ X37 ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t124_relat_1])).

thf('12',plain,(
    ! [X33: $i,X34: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X33 @ X34 ) )
      = ( k3_xboole_0 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('13',plain,(
    ! [X36: $i,X37: $i] :
      ( ( ( k8_relat_1 @ X37 @ X36 )
        = ( k1_setfam_1 @ ( k2_tarski @ X36 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X36 ) @ X37 ) ) ) )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( k8_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k8_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k8_relat_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','17'])).

thf('19',plain,(
    $false ),
    inference(simplify,[status(thm)],['18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.shzGEyzQ4y
% 0.13/0.36  % Computer   : n017.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 14:24:01 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 31 iterations in 0.015s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.45  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.45  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.45  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.45  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.45  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.45  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 0.21/0.45  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.45  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.45  thf(t138_relat_1, conjecture,
% 0.21/0.45    (![A:$i]: ( ( k8_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i]: ( ( k8_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t138_relat_1])).
% 0.21/0.45  thf('0', plain, (((k8_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(cc1_relat_1, axiom,
% 0.21/0.45    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.21/0.45  thf('1', plain, (![X35 : $i]: ((v1_relat_1 @ X35) | ~ (v1_xboole_0 @ X35))),
% 0.21/0.45      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.45  thf(commutativity_k5_xboole_0, axiom,
% 0.21/0.45    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 0.21/0.45  thf('2', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]: ((k5_xboole_0 @ X1 @ X0) = (k5_xboole_0 @ X0 @ X1))),
% 0.21/0.45      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 0.21/0.45  thf(t5_boole, axiom,
% 0.21/0.45    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.21/0.45  thf('3', plain, (![X5 : $i]: ((k5_xboole_0 @ X5 @ k1_xboole_0) = (X5))),
% 0.21/0.45      inference('cnf', [status(esa)], [t5_boole])).
% 0.21/0.45  thf('4', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.21/0.45      inference('sup+', [status(thm)], ['2', '3'])).
% 0.21/0.45  thf(t100_xboole_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 0.21/0.45  thf('5', plain,
% 0.21/0.45      (![X2 : $i, X3 : $i]:
% 0.21/0.45         ((k4_xboole_0 @ X2 @ X3)
% 0.21/0.45           = (k5_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)))),
% 0.21/0.45      inference('cnf', [status(esa)], [t100_xboole_1])).
% 0.21/0.45  thf('6', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.45      inference('sup+', [status(thm)], ['4', '5'])).
% 0.21/0.45  thf(t4_boole, axiom,
% 0.21/0.45    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.21/0.45  thf('7', plain,
% 0.21/0.45      (![X4 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 0.21/0.45      inference('cnf', [status(esa)], [t4_boole])).
% 0.21/0.45  thf('8', plain,
% 0.21/0.45      (![X0 : $i]: ((k1_xboole_0) = (k3_xboole_0 @ k1_xboole_0 @ X0))),
% 0.21/0.45      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.45  thf(t12_setfam_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.45  thf('9', plain,
% 0.21/0.45      (![X33 : $i, X34 : $i]:
% 0.21/0.45         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 0.21/0.45      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.45  thf('10', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         ((k1_xboole_0) = (k1_setfam_1 @ (k2_tarski @ k1_xboole_0 @ X0)))),
% 0.21/0.45      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.45  thf(t124_relat_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( v1_relat_1 @ B ) =>
% 0.21/0.45       ( ( k8_relat_1 @ A @ B ) =
% 0.21/0.45         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ))).
% 0.21/0.45  thf('11', plain,
% 0.21/0.45      (![X36 : $i, X37 : $i]:
% 0.21/0.45         (((k8_relat_1 @ X37 @ X36)
% 0.21/0.45            = (k3_xboole_0 @ X36 @ (k2_zfmisc_1 @ (k1_relat_1 @ X36) @ X37)))
% 0.21/0.45          | ~ (v1_relat_1 @ X36))),
% 0.21/0.45      inference('cnf', [status(esa)], [t124_relat_1])).
% 0.21/0.45  thf('12', plain,
% 0.21/0.45      (![X33 : $i, X34 : $i]:
% 0.21/0.45         ((k1_setfam_1 @ (k2_tarski @ X33 @ X34)) = (k3_xboole_0 @ X33 @ X34))),
% 0.21/0.45      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.45  thf('13', plain,
% 0.21/0.45      (![X36 : $i, X37 : $i]:
% 0.21/0.45         (((k8_relat_1 @ X37 @ X36)
% 0.21/0.45            = (k1_setfam_1 @ 
% 0.21/0.45               (k2_tarski @ X36 @ (k2_zfmisc_1 @ (k1_relat_1 @ X36) @ X37))))
% 0.21/0.45          | ~ (v1_relat_1 @ X36))),
% 0.21/0.45      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.45  thf('14', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (((k8_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.21/0.45          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.45      inference('sup+', [status(thm)], ['10', '13'])).
% 0.21/0.45  thf('15', plain,
% 0.21/0.45      (![X0 : $i]:
% 0.21/0.45         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.45          | ((k8_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['1', '14'])).
% 0.21/0.45  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.45  thf('16', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.45      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.45  thf('17', plain,
% 0.21/0.45      (![X0 : $i]: ((k8_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.45      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.45  thf('18', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.45      inference('demod', [status(thm)], ['0', '17'])).
% 0.21/0.45  thf('19', plain, ($false), inference('simplify', [status(thm)], ['18'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
