%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fEj5GfAwUZ

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   44 (  48 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :   13
%              Number of atoms          :  229 ( 259 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t19_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) )
      = ( k1_tarski @ A ) ) )).

thf('0',plain,(
    ! [X48: $i,X49: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X48 ) @ ( k2_tarski @ X48 @ X49 ) )
      = ( k1_tarski @ X48 ) ) ),
    inference(cnf,[status(esa)],[t19_zfmisc_1])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t55_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
        & ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          & ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t55_zfmisc_1])).

thf('2',plain,(
    r1_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('4',plain,(
    r1_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('5',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k3_xboole_0 @ X2 @ X3 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('6',plain,
    ( ( k3_xboole_0 @ sk_C @ ( k2_tarski @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('7',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X9 @ X10 ) @ X11 )
      = ( k3_xboole_0 @ X9 @ ( k3_xboole_0 @ X10 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('10',plain,(
    ! [X14: $i] :
      ( ( X14 = k1_xboole_0 )
      | ~ ( r1_tarski @ X14 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_C @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X2: $i,X4: $i] :
      ( ( r1_xboole_0 @ X2 @ X4 )
      | ( ( k3_xboole_0 @ X2 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ sk_C @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ sk_C @ ( k3_xboole_0 @ X0 @ ( k2_tarski @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['1','15'])).

thf('17',plain,(
    r1_xboole_0 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['0','16'])).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('19',plain,(
    r1_xboole_0 @ ( k1_tarski @ sk_A ) @ sk_C ),
    inference('sup-',[status(thm)],['17','18'])).

thf(l24_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B )
        & ( r2_hidden @ A @ B ) ) )).

thf('20',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X46 ) @ X47 )
      | ~ ( r2_hidden @ X46 @ X47 ) ) ),
    inference(cnf,[status(esa)],[l24_zfmisc_1])).

thf('21',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['21','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.fEj5GfAwUZ
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:53:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 57 iterations in 0.029s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.47  thf(t19_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( k3_xboole_0 @ ( k1_tarski @ A ) @ ( k2_tarski @ A @ B ) ) =
% 0.20/0.47       ( k1_tarski @ A ) ))).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X48 : $i, X49 : $i]:
% 0.20/0.47         ((k3_xboole_0 @ (k1_tarski @ X48) @ (k2_tarski @ X48 @ X49))
% 0.20/0.47           = (k1_tarski @ X48))),
% 0.20/0.47      inference('cnf', [status(esa)], [t19_zfmisc_1])).
% 0.20/0.47  thf(commutativity_k3_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.47      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.20/0.47  thf(t55_zfmisc_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & ( r2_hidden @ A @ C ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.47        ( ~( ( r1_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) & 
% 0.20/0.47             ( r2_hidden @ A @ C ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t55_zfmisc_1])).
% 0.20/0.47  thf('2', plain, ((r1_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.47  thf('4', plain, ((r1_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf(d7_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.47       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X2 : $i, X3 : $i]:
% 0.20/0.47         (((k3_xboole_0 @ X2 @ X3) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X2 @ X3))),
% 0.20/0.47      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.47  thf('6', plain,
% 0.20/0.47      (((k3_xboole_0 @ sk_C @ (k2_tarski @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.47  thf(t16_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.20/0.47       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.47  thf('7', plain,
% 0.20/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.47         ((k3_xboole_0 @ (k3_xboole_0 @ X9 @ X10) @ X11)
% 0.20/0.47           = (k3_xboole_0 @ X9 @ (k3_xboole_0 @ X10 @ X11)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k3_xboole_0 @ k1_xboole_0 @ X0)
% 0.20/0.47           = (k3_xboole_0 @ sk_C @ 
% 0.20/0.47              (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['6', '7'])).
% 0.20/0.47  thf(t17_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X12 : $i, X13 : $i]: (r1_tarski @ (k3_xboole_0 @ X12 @ X13) @ X12)),
% 0.20/0.47      inference('cnf', [status(esa)], [t17_xboole_1])).
% 0.20/0.47  thf(t3_xboole_1, axiom,
% 0.20/0.47    (![A:$i]:
% 0.20/0.47     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (![X14 : $i]:
% 0.20/0.47         (((X14) = (k1_xboole_0)) | ~ (r1_tarski @ X14 @ k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         ((k1_xboole_0)
% 0.20/0.47           = (k3_xboole_0 @ sk_C @ 
% 0.20/0.47              (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['8', '11'])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      (![X2 : $i, X4 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ X2 @ X4) | ((k3_xboole_0 @ X2 @ X4) != (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.47  thf('14', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.47          | (r1_xboole_0 @ sk_C @ 
% 0.20/0.47             (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (r1_xboole_0 @ sk_C @ (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0))),
% 0.20/0.47      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.47  thf('16', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (r1_xboole_0 @ sk_C @ (k3_xboole_0 @ X0 @ (k2_tarski @ sk_A @ sk_B)))),
% 0.20/0.47      inference('sup+', [status(thm)], ['1', '15'])).
% 0.20/0.47  thf('17', plain, ((r1_xboole_0 @ sk_C @ (k1_tarski @ sk_A))),
% 0.20/0.47      inference('sup+', [status(thm)], ['0', '16'])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i]:
% 0.20/0.47         ((r1_xboole_0 @ X5 @ X6) | ~ (r1_xboole_0 @ X6 @ X5))),
% 0.20/0.47      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.47  thf('19', plain, ((r1_xboole_0 @ (k1_tarski @ sk_A) @ sk_C)),
% 0.20/0.47      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.47  thf(l24_zfmisc_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ~( ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) & ( r2_hidden @ A @ B ) ) ))).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X46 : $i, X47 : $i]:
% 0.20/0.47         (~ (r1_xboole_0 @ (k1_tarski @ X46) @ X47) | ~ (r2_hidden @ X46 @ X47))),
% 0.20/0.47      inference('cnf', [status(esa)], [l24_zfmisc_1])).
% 0.20/0.47  thf('21', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.20/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.47  thf('22', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('23', plain, ($false), inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.33/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
