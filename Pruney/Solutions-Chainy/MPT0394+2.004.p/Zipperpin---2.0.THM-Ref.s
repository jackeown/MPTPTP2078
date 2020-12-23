%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gfCPtcsK2m

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:45 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   52 (  73 expanded)
%              Number of leaves         :   20 (  30 expanded)
%              Depth                    :   12
%              Number of atoms          :  320 ( 450 expanded)
%              Number of equality atoms :   46 (  63 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t12_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
        = ( k3_xboole_0 @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t12_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k2_tarski @ sk_A @ sk_B ) )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t41_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X8 @ X9 )
      = ( k2_xboole_0 @ ( k1_tarski @ X8 ) @ ( k1_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t41_enumset1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_tarski @ X0 @ X1 )
      = ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t11_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf('5',plain,(
    ! [X27: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ X0 ) )
      = X0 ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(t10_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) )
         != ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) )).

thf('7',plain,(
    ! [X25: $i,X26: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ X25 @ X26 ) )
        = ( k3_xboole_0 @ ( k1_setfam_1 @ X25 ) @ ( k1_setfam_1 @ X26 ) ) )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t10_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) )
      | ( X1 = k1_xboole_0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X13: $i] :
      ( ( k2_tarski @ X13 @ X13 )
      = ( k1_tarski @ X13 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('11',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['10','11'])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r2_hidden @ X21 @ X22 )
      | ( ( k3_xboole_0 @ X22 @ ( k1_tarski @ X21 ) )
       != ( k1_tarski @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_tarski @ X0 ) )
      | ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X5: $i] :
      ( ( k3_xboole_0 @ X5 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('16',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X19 ) @ X20 )
      | ~ ( r2_hidden @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['14','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k2_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( ( k1_setfam_1 @ ( k2_xboole_0 @ ( k2_tarski @ X0 @ X0 ) @ X1 ) )
        = ( k3_xboole_0 @ X0 @ ( k1_setfam_1 @ X1 ) ) ) ) ),
    inference(clc,[status(thm)],['8','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['3','23'])).

thf('25',plain,(
    ! [X27: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t11_setfam_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
     != ( k1_tarski @ X0 ) ) ),
    inference(clc,[status(thm)],['14','20'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ( k3_xboole_0 @ sk_A @ sk_B )
 != ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['0','28'])).

thf('30',plain,(
    $false ),
    inference(simplify,[status(thm)],['29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gfCPtcsK2m
% 0.15/0.37  % Computer   : n004.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 14:19:39 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 406 iterations in 0.178s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.47/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.66  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.47/0.66  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.66  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.47/0.66  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.47/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.66  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(t12_setfam_1, conjecture,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i,B:$i]:
% 0.47/0.66        ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t12_setfam_1])).
% 0.47/0.66  thf('0', plain,
% 0.47/0.66      (((k1_setfam_1 @ (k2_tarski @ sk_A @ sk_B))
% 0.47/0.66         != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(t69_enumset1, axiom,
% 0.47/0.66    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.47/0.66  thf('1', plain, (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.47/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.66  thf(t41_enumset1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( k2_tarski @ A @ B ) =
% 0.47/0.66       ( k2_xboole_0 @ ( k1_tarski @ A ) @ ( k1_tarski @ B ) ) ))).
% 0.47/0.66  thf('2', plain,
% 0.47/0.66      (![X8 : $i, X9 : $i]:
% 0.47/0.66         ((k2_tarski @ X8 @ X9)
% 0.47/0.66           = (k2_xboole_0 @ (k1_tarski @ X8) @ (k1_tarski @ X9)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t41_enumset1])).
% 0.47/0.66  thf('3', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((k2_tarski @ X0 @ X1)
% 0.47/0.66           = (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ (k1_tarski @ X1)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['1', '2'])).
% 0.47/0.66  thf('4', plain, (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.47/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.66  thf(t11_setfam_1, axiom,
% 0.47/0.66    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.47/0.66  thf('5', plain, (![X27 : $i]: ((k1_setfam_1 @ (k1_tarski @ X27)) = (X27))),
% 0.47/0.66      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.47/0.66  thf('6', plain, (![X0 : $i]: ((k1_setfam_1 @ (k2_tarski @ X0 @ X0)) = (X0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['4', '5'])).
% 0.47/0.66  thf(t10_setfam_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.47/0.66          ( ( k1_setfam_1 @ ( k2_xboole_0 @ A @ B ) ) !=
% 0.47/0.66            ( k3_xboole_0 @ ( k1_setfam_1 @ A ) @ ( k1_setfam_1 @ B ) ) ) ) ))).
% 0.47/0.66  thf('7', plain,
% 0.47/0.66      (![X25 : $i, X26 : $i]:
% 0.47/0.66         (((X25) = (k1_xboole_0))
% 0.47/0.66          | ((k1_setfam_1 @ (k2_xboole_0 @ X25 @ X26))
% 0.47/0.66              = (k3_xboole_0 @ (k1_setfam_1 @ X25) @ (k1_setfam_1 @ X26)))
% 0.47/0.66          | ((X26) = (k1_xboole_0)))),
% 0.47/0.66      inference('cnf', [status(esa)], [t10_setfam_1])).
% 0.47/0.66  thf('8', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k1_setfam_1 @ (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1))
% 0.47/0.66            = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1)))
% 0.47/0.66          | ((X1) = (k1_xboole_0))
% 0.47/0.66          | ((k2_tarski @ X0 @ X0) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['6', '7'])).
% 0.47/0.66  thf('9', plain, (![X13 : $i]: ((k2_tarski @ X13 @ X13) = (k1_tarski @ X13))),
% 0.47/0.66      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.47/0.66  thf(commutativity_k3_xboole_0, axiom,
% 0.47/0.66    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.47/0.66  thf('10', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.47/0.66      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.47/0.66  thf(t2_boole, axiom,
% 0.47/0.66    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.47/0.66  thf('11', plain,
% 0.47/0.66      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [t2_boole])).
% 0.47/0.66  thf('12', plain,
% 0.47/0.66      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['10', '11'])).
% 0.47/0.66  thf(l29_zfmisc_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.47/0.66       ( r2_hidden @ B @ A ) ))).
% 0.47/0.66  thf('13', plain,
% 0.47/0.66      (![X21 : $i, X22 : $i]:
% 0.47/0.66         ((r2_hidden @ X21 @ X22)
% 0.47/0.66          | ((k3_xboole_0 @ X22 @ (k1_tarski @ X21)) != (k1_tarski @ X21)))),
% 0.47/0.66      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.47/0.66  thf('14', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((k1_xboole_0) != (k1_tarski @ X0)) | (r2_hidden @ X0 @ k1_xboole_0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['12', '13'])).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      (![X5 : $i]: ((k3_xboole_0 @ X5 @ k1_xboole_0) = (k1_xboole_0))),
% 0.47/0.66      inference('cnf', [status(esa)], [t2_boole])).
% 0.47/0.66  thf(d7_xboole_0, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.47/0.66       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.47/0.66  thf('16', plain,
% 0.47/0.66      (![X2 : $i, X4 : $i]:
% 0.47/0.66         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.47/0.66      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['15', '16'])).
% 0.47/0.66  thf('18', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.47/0.66      inference('simplify', [status(thm)], ['17'])).
% 0.47/0.66  thf(l24_zfmisc_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.47/0.66  thf('19', plain,
% 0.47/0.66      (![X19 : $i, X20 : $i]:
% 0.47/0.66         (~ (r1_xboole_0 @ (k1_tarski @ X19) @ X20) | ~ (r2_hidden @ X19 @ X20))),
% 0.47/0.66      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.47/0.66  thf('20', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.47/0.66      inference('sup-', [status(thm)], ['18', '19'])).
% 0.47/0.66  thf('21', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.47/0.66      inference('clc', [status(thm)], ['14', '20'])).
% 0.47/0.66  thf('22', plain, (![X0 : $i]: ((k1_xboole_0) != (k2_tarski @ X0 @ X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['9', '21'])).
% 0.47/0.66  thf('23', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((X1) = (k1_xboole_0))
% 0.47/0.66          | ((k1_setfam_1 @ (k2_xboole_0 @ (k2_tarski @ X0 @ X0) @ X1))
% 0.47/0.66              = (k3_xboole_0 @ X0 @ (k1_setfam_1 @ X1))))),
% 0.47/0.66      inference('clc', [status(thm)], ['8', '22'])).
% 0.47/0.66  thf('24', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0))
% 0.47/0.66            = (k3_xboole_0 @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0))))
% 0.47/0.66          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup+', [status(thm)], ['3', '23'])).
% 0.47/0.66  thf('25', plain, (![X27 : $i]: ((k1_setfam_1 @ (k1_tarski @ X27)) = (X27))),
% 0.47/0.66      inference('cnf', [status(esa)], [t11_setfam_1])).
% 0.47/0.66  thf('26', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))
% 0.47/0.66          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.47/0.66      inference('demod', [status(thm)], ['24', '25'])).
% 0.47/0.66  thf('27', plain, (![X0 : $i]: ((k1_xboole_0) != (k1_tarski @ X0))),
% 0.47/0.66      inference('clc', [status(thm)], ['14', '20'])).
% 0.47/0.66  thf('28', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X1 @ X0))),
% 0.47/0.66      inference('clc', [status(thm)], ['26', '27'])).
% 0.47/0.66  thf('29', plain,
% 0.47/0.66      (((k3_xboole_0 @ sk_A @ sk_B) != (k3_xboole_0 @ sk_A @ sk_B))),
% 0.47/0.66      inference('demod', [status(thm)], ['0', '28'])).
% 0.47/0.66  thf('30', plain, ($false), inference('simplify', [status(thm)], ['29'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
