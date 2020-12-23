%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dR8RlW3aDG

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:34 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   38 (  41 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  198 ( 221 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_wellord1_type,type,(
    k2_wellord1: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(t33_wellord2,conjecture,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) ),
    inference('cnf.neg',[status(esa)],[t33_wellord2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_wellord2 @ sk_A ) @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t8_wellord2,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A )
        = ( k1_wellord2 @ A ) ) ) )).

thf('3',plain,(
    ! [X44: $i,X45: $i] :
      ( ( ( k2_wellord1 @ ( k1_wellord2 @ X45 ) @ X44 )
        = ( k1_wellord2 @ X44 ) )
      | ~ ( r1_tarski @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t8_wellord2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k2_wellord1 @ ( k1_wellord2 @ X0 ) @ X0 )
      = ( k1_wellord2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d6_wellord1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k2_wellord1 @ A @ B )
          = ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ B @ B ) ) ) ) )).

thf('5',plain,(
    ! [X41: $i,X42: $i] :
      ( ( ( k2_wellord1 @ X41 @ X42 )
        = ( k3_xboole_0 @ X41 @ ( k2_zfmisc_1 @ X42 @ X42 ) ) )
      | ~ ( v1_relat_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[d6_wellord1])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('6',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X39: $i,X40: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X39 @ X40 ) )
      = ( k3_xboole_0 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t18_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t18_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_wellord1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k1_wellord2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','15'])).

thf(dt_k1_wellord2,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ A ) ) )).

thf('17',plain,(
    ! [X43: $i] :
      ( v1_relat_1 @ ( k1_wellord2 @ X43 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_wellord2])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_wellord2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dR8RlW3aDG
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:25:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 75 iterations in 0.038s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(k2_wellord1_type, type, k2_wellord1: $i > $i > $i).
% 0.19/0.49  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.19/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.19/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.49  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.49  thf(t33_wellord2, conjecture,
% 0.19/0.49    (![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i]: ( r1_tarski @ ( k1_wellord2 @ A ) @ ( k2_zfmisc_1 @ A @ A ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t33_wellord2])).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      (~ (r1_tarski @ (k1_wellord2 @ sk_A) @ (k2_zfmisc_1 @ sk_A @ sk_A))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(d10_xboole_0, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.49  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.49      inference('simplify', [status(thm)], ['1'])).
% 0.19/0.49  thf(t8_wellord2, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( r1_tarski @ A @ B ) =>
% 0.19/0.49       ( ( k2_wellord1 @ ( k1_wellord2 @ B ) @ A ) = ( k1_wellord2 @ A ) ) ))).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      (![X44 : $i, X45 : $i]:
% 0.19/0.49         (((k2_wellord1 @ (k1_wellord2 @ X45) @ X44) = (k1_wellord2 @ X44))
% 0.19/0.49          | ~ (r1_tarski @ X44 @ X45))),
% 0.19/0.49      inference('cnf', [status(esa)], [t8_wellord2])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((k2_wellord1 @ (k1_wellord2 @ X0) @ X0) = (k1_wellord2 @ X0))),
% 0.19/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.49  thf(d6_wellord1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ A ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( k2_wellord1 @ A @ B ) =
% 0.19/0.49           ( k3_xboole_0 @ A @ ( k2_zfmisc_1 @ B @ B ) ) ) ) ))).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (![X41 : $i, X42 : $i]:
% 0.19/0.49         (((k2_wellord1 @ X41 @ X42)
% 0.19/0.49            = (k3_xboole_0 @ X41 @ (k2_zfmisc_1 @ X42 @ X42)))
% 0.19/0.49          | ~ (v1_relat_1 @ X41))),
% 0.19/0.49      inference('cnf', [status(esa)], [d6_wellord1])).
% 0.19/0.49  thf(commutativity_k2_tarski, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.19/0.49  thf('6', plain,
% 0.19/0.49      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 0.19/0.49      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.19/0.49  thf(t12_setfam_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (![X39 : $i, X40 : $i]:
% 0.19/0.49         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 0.19/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('sup+', [status(thm)], ['6', '7'])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (![X39 : $i, X40 : $i]:
% 0.19/0.49         ((k1_setfam_1 @ (k2_tarski @ X39 @ X40)) = (k3_xboole_0 @ X39 @ X40))),
% 0.19/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.19/0.49      inference('sup+', [status(thm)], ['8', '9'])).
% 0.19/0.49  thf('11', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.19/0.49      inference('simplify', [status(thm)], ['1'])).
% 0.19/0.49  thf(t18_xboole_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) => ( r1_tarski @ A @ B ) ))).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.49         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ X3 @ (k3_xboole_0 @ X4 @ X5)))),
% 0.19/0.49      inference('cnf', [status(esa)], [t18_xboole_1])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X1)),
% 0.19/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 0.19/0.49      inference('sup+', [status(thm)], ['10', '13'])).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((r1_tarski @ (k2_wellord1 @ X1 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))
% 0.19/0.49          | ~ (v1_relat_1 @ X1))),
% 0.19/0.49      inference('sup+', [status(thm)], ['5', '14'])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))
% 0.19/0.49          | ~ (v1_relat_1 @ (k1_wellord2 @ X0)))),
% 0.19/0.49      inference('sup+', [status(thm)], ['4', '15'])).
% 0.19/0.49  thf(dt_k1_wellord2, axiom, (![A:$i]: ( v1_relat_1 @ ( k1_wellord2 @ A ) ))).
% 0.19/0.49  thf('17', plain, (![X43 : $i]: (v1_relat_1 @ (k1_wellord2 @ X43))),
% 0.19/0.49      inference('cnf', [status(esa)], [dt_k1_wellord2])).
% 0.19/0.49  thf('18', plain,
% 0.19/0.49      (![X0 : $i]: (r1_tarski @ (k1_wellord2 @ X0) @ (k2_zfmisc_1 @ X0 @ X0))),
% 0.19/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.49  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
