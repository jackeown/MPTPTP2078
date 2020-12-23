%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wYCVjsaxp1

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:59 EST 2020

% Result     : Theorem 0.26s
% Output     : Refutation 0.26s
% Verified   : 
% Statistics : Number of formulae       :   37 (  47 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :  173 ( 241 expanded)
%              Number of equality atoms :   27 (  37 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t50_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
     != k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
       != k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t50_zfmisc_1])).

thf('0',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k3_xboole_0 @ X5 @ ( k2_xboole_0 @ X5 @ X6 ) )
      = X5 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('3',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ k1_xboole_0 )
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('5',plain,
    ( k1_xboole_0
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k2_xboole_0 @ k1_xboole_0 @ sk_C )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,
    ( k1_xboole_0
    = ( k2_tarski @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['3','4'])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('8',plain,(
    ! [X41: $i,X43: $i,X44: $i] :
      ( ( r1_tarski @ X43 @ ( k2_tarski @ X41 @ X44 ) )
      | ( X43
       != ( k1_tarski @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('9',plain,(
    ! [X41: $i,X44: $i] :
      ( r1_tarski @ ( k1_tarski @ X41 ) @ ( k2_tarski @ X41 @ X44 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    r1_tarski @ ( k1_tarski @ sk_A ) @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['7','9'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('12',plain,
    ( ( k4_xboole_0 @ ( k1_tarski @ sk_A ) @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('13',plain,(
    ! [X8: $i] :
      ( ( k4_xboole_0 @ X8 @ k1_xboole_0 )
      = X8 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('14',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['12','13'])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('15',plain,(
    ! [X47: $i,X48: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X47 ) @ X48 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','16'])).

thf('18',plain,(
    $false ),
    inference(simplify,[status(thm)],['17'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wYCVjsaxp1
% 0.17/0.39  % Computer   : n024.cluster.edu
% 0.17/0.39  % Model      : x86_64 x86_64
% 0.17/0.39  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.17/0.39  % Memory     : 8042.1875MB
% 0.17/0.39  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.17/0.39  % CPULimit   : 60
% 0.17/0.39  % DateTime   : Tue Dec  1 12:15:51 EST 2020
% 0.17/0.39  % CPUTime    : 
% 0.17/0.39  % Running portfolio for 600 s
% 0.17/0.39  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.17/0.39  % Number of cores: 8
% 0.17/0.39  % Python version: Python 3.6.8
% 0.17/0.39  % Running in FO mode
% 0.26/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.26/0.51  % Solved by: fo/fo7.sh
% 0.26/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.26/0.51  % done 24 iterations in 0.014s
% 0.26/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.26/0.51  % SZS output start Refutation
% 0.26/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.26/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.26/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.26/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.26/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.26/0.51  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.26/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.26/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.26/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.26/0.51  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.26/0.51  thf(t50_zfmisc_1, conjecture,
% 0.26/0.51    (![A:$i,B:$i,C:$i]:
% 0.26/0.51     ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ))).
% 0.26/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.26/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.26/0.51        ( ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) != ( k1_xboole_0 ) ) )),
% 0.26/0.51    inference('cnf.neg', [status(esa)], [t50_zfmisc_1])).
% 0.26/0.51  thf('0', plain,
% 0.26/0.51      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.26/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.51  thf('1', plain,
% 0.26/0.51      (((k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) = (k1_xboole_0))),
% 0.26/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.26/0.51  thf(t21_xboole_1, axiom,
% 0.26/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.26/0.51  thf('2', plain,
% 0.26/0.51      (![X5 : $i, X6 : $i]:
% 0.26/0.51         ((k3_xboole_0 @ X5 @ (k2_xboole_0 @ X5 @ X6)) = (X5))),
% 0.26/0.51      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.26/0.51  thf('3', plain,
% 0.26/0.51      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ k1_xboole_0)
% 0.26/0.51         = (k2_tarski @ sk_A @ sk_B))),
% 0.26/0.51      inference('sup+', [status(thm)], ['1', '2'])).
% 0.26/0.51  thf(t2_boole, axiom,
% 0.26/0.51    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.26/0.51  thf('4', plain,
% 0.26/0.51      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.26/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.26/0.51  thf('5', plain, (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))),
% 0.26/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.26/0.51  thf('6', plain, (((k2_xboole_0 @ k1_xboole_0 @ sk_C) = (k1_xboole_0))),
% 0.26/0.51      inference('demod', [status(thm)], ['0', '5'])).
% 0.26/0.51  thf('7', plain, (((k1_xboole_0) = (k2_tarski @ sk_A @ sk_B))),
% 0.26/0.51      inference('demod', [status(thm)], ['3', '4'])).
% 0.26/0.51  thf(l45_zfmisc_1, axiom,
% 0.26/0.51    (![A:$i,B:$i,C:$i]:
% 0.26/0.51     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.26/0.51       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.26/0.51            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.26/0.51  thf('8', plain,
% 0.26/0.51      (![X41 : $i, X43 : $i, X44 : $i]:
% 0.26/0.51         ((r1_tarski @ X43 @ (k2_tarski @ X41 @ X44))
% 0.26/0.51          | ((X43) != (k1_tarski @ X41)))),
% 0.26/0.51      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.26/0.51  thf('9', plain,
% 0.26/0.51      (![X41 : $i, X44 : $i]:
% 0.26/0.51         (r1_tarski @ (k1_tarski @ X41) @ (k2_tarski @ X41 @ X44))),
% 0.26/0.51      inference('simplify', [status(thm)], ['8'])).
% 0.26/0.51  thf('10', plain, ((r1_tarski @ (k1_tarski @ sk_A) @ k1_xboole_0)),
% 0.26/0.51      inference('sup+', [status(thm)], ['7', '9'])).
% 0.26/0.51  thf(l32_xboole_1, axiom,
% 0.26/0.51    (![A:$i,B:$i]:
% 0.26/0.51     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.26/0.51  thf('11', plain,
% 0.26/0.51      (![X0 : $i, X2 : $i]:
% 0.26/0.51         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 0.26/0.51      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.26/0.51  thf('12', plain,
% 0.26/0.51      (((k4_xboole_0 @ (k1_tarski @ sk_A) @ k1_xboole_0) = (k1_xboole_0))),
% 0.26/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.26/0.51  thf(t3_boole, axiom,
% 0.26/0.51    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.26/0.51  thf('13', plain, (![X8 : $i]: ((k4_xboole_0 @ X8 @ k1_xboole_0) = (X8))),
% 0.26/0.51      inference('cnf', [status(esa)], [t3_boole])).
% 0.26/0.51  thf('14', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 0.26/0.51      inference('demod', [status(thm)], ['12', '13'])).
% 0.26/0.51  thf(t49_zfmisc_1, axiom,
% 0.26/0.51    (![A:$i,B:$i]:
% 0.26/0.51     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.26/0.51  thf('15', plain,
% 0.26/0.51      (![X47 : $i, X48 : $i]:
% 0.26/0.51         ((k2_xboole_0 @ (k1_tarski @ X47) @ X48) != (k1_xboole_0))),
% 0.26/0.51      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.26/0.51  thf('16', plain,
% 0.26/0.51      (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) != (k1_xboole_0))),
% 0.26/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.26/0.51  thf('17', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.26/0.51      inference('sup-', [status(thm)], ['6', '16'])).
% 0.26/0.51  thf('18', plain, ($false), inference('simplify', [status(thm)], ['17'])).
% 0.26/0.51  
% 0.26/0.51  % SZS output end Refutation
% 0.26/0.51  
% 0.26/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
