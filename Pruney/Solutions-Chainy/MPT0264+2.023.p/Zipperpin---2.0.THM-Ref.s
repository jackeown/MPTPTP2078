%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SvgsPJEocl

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:33:41 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :   44 (  50 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :   11
%              Number of atoms          :  310 ( 384 expanded)
%              Number of equality atoms :   38 (  48 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t59_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
          = ( k1_tarski @ A ) )
        & ( r2_hidden @ B @ C )
        & ( A != B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ~ ( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C )
            = ( k1_tarski @ A ) )
          & ( r2_hidden @ B @ C )
          & ( A != B ) ) ),
    inference('cnf.neg',[status(esa)],[t59_zfmisc_1])).

thf('0',plain,
    ( ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C_1 )
    = ( k1_tarski @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('2',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t16_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C )
      = ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ X0 )
      = ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('6',plain,(
    r2_hidden @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('7',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k3_xboole_0 @ X25 @ ( k1_tarski @ X24 ) )
        = ( k1_tarski @ X24 ) )
      | ~ ( r2_hidden @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ ( k1_tarski @ sk_B ) )
    = ( k1_tarski @ sk_B ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X2 @ X3 ) @ X4 )
      = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X3 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t16_xboole_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      = ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ X0 )
      = ( k3_xboole_0 @ sk_C_1 @ ( k3_xboole_0 @ X0 @ ( k1_tarski @ sk_B ) ) ) ) ),
    inference('sup+',[status(thm)],['5','10'])).

thf('12',plain,
    ( ( k3_xboole_0 @ ( k1_tarski @ sk_B ) @ ( k2_tarski @ sk_A @ sk_B ) )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference('sup+',[status(thm)],['4','11'])).

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

thf('13',plain,(
    ! [X26: $i,X28: $i,X29: $i] :
      ( ( r1_tarski @ X28 @ ( k2_tarski @ X26 @ X29 ) )
      | ( X28
       != ( k1_tarski @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('14',plain,(
    ! [X26: $i,X29: $i] :
      ( r1_tarski @ ( k1_tarski @ X29 ) @ ( k2_tarski @ X26 @ X29 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('15',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k3_xboole_0 @ X5 @ X6 )
        = X5 )
      | ~ ( r1_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k1_tarski @ X0 ) @ ( k2_tarski @ X1 @ X0 ) )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( k1_tarski @ sk_B )
    = ( k3_xboole_0 @ ( k1_tarski @ sk_A ) @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','16'])).

thf(l29_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) )
        = ( k1_tarski @ B ) )
     => ( r2_hidden @ B @ A ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r2_hidden @ X22 @ X23 )
      | ( ( k3_xboole_0 @ X23 @ ( k1_tarski @ X22 ) )
       != ( k1_tarski @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[l29_zfmisc_1])).

thf('19',plain,
    ( ( ( k1_tarski @ sk_B )
     != ( k1_tarski @ sk_B ) )
    | ( r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['19'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ( X10 = X7 )
      | ( X9
       != ( k1_tarski @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('22',plain,(
    ! [X7: $i,X10: $i] :
      ( ( X10 = X7 )
      | ~ ( r2_hidden @ X10 @ ( k1_tarski @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    sk_B = sk_A ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    sk_A != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.SvgsPJEocl
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:49:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.36  % Running in FO mode
% 0.40/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.61  % Solved by: fo/fo7.sh
% 0.40/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.61  % done 209 iterations in 0.125s
% 0.40/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.61  % SZS output start Refutation
% 0.40/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.40/0.61  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.61  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.40/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.40/0.61  thf(t59_zfmisc_1, conjecture,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.40/0.61          ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ))).
% 0.40/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.40/0.61        ( ~( ( ( k3_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) = ( k1_tarski @ A ) ) & 
% 0.40/0.61             ( r2_hidden @ B @ C ) & ( ( A ) != ( B ) ) ) ) )),
% 0.40/0.61    inference('cnf.neg', [status(esa)], [t59_zfmisc_1])).
% 0.40/0.61  thf('0', plain,
% 0.40/0.61      (((k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C_1) = (k1_tarski @ sk_A))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(commutativity_k3_xboole_0, axiom,
% 0.40/0.61    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.40/0.61  thf('1', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.61  thf('2', plain,
% 0.40/0.61      (((k3_xboole_0 @ sk_C_1 @ (k2_tarski @ sk_A @ sk_B)) = (k1_tarski @ sk_A))),
% 0.40/0.61      inference('demod', [status(thm)], ['0', '1'])).
% 0.40/0.61  thf(t16_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( k3_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ C ) =
% 0.40/0.61       ( k3_xboole_0 @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 0.40/0.61  thf('3', plain,
% 0.40/0.61      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.61         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ X4)
% 0.40/0.61           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.40/0.61  thf('4', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((k3_xboole_0 @ (k1_tarski @ sk_A) @ X0)
% 0.40/0.61           = (k3_xboole_0 @ sk_C_1 @ 
% 0.40/0.61              (k3_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ X0)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['2', '3'])).
% 0.40/0.61  thf('5', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.40/0.61      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.40/0.61  thf('6', plain, ((r2_hidden @ sk_B @ sk_C_1)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(l31_zfmisc_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( r2_hidden @ A @ B ) =>
% 0.40/0.61       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.40/0.61  thf('7', plain,
% 0.40/0.61      (![X24 : $i, X25 : $i]:
% 0.40/0.61         (((k3_xboole_0 @ X25 @ (k1_tarski @ X24)) = (k1_tarski @ X24))
% 0.40/0.61          | ~ (r2_hidden @ X24 @ X25))),
% 0.40/0.61      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.40/0.61  thf('8', plain,
% 0.40/0.61      (((k3_xboole_0 @ sk_C_1 @ (k1_tarski @ sk_B)) = (k1_tarski @ sk_B))),
% 0.40/0.61      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.61  thf('9', plain,
% 0.40/0.61      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.40/0.61         ((k3_xboole_0 @ (k3_xboole_0 @ X2 @ X3) @ X4)
% 0.40/0.61           = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X3 @ X4)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t16_xboole_1])).
% 0.40/0.61  thf('10', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((k3_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 0.40/0.61           = (k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ (k1_tarski @ sk_B) @ X0)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['8', '9'])).
% 0.40/0.61  thf('11', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((k3_xboole_0 @ (k1_tarski @ sk_B) @ X0)
% 0.40/0.61           = (k3_xboole_0 @ sk_C_1 @ (k3_xboole_0 @ X0 @ (k1_tarski @ sk_B))))),
% 0.40/0.61      inference('sup+', [status(thm)], ['5', '10'])).
% 0.40/0.61  thf('12', plain,
% 0.40/0.61      (((k3_xboole_0 @ (k1_tarski @ sk_B) @ (k2_tarski @ sk_A @ sk_B))
% 0.40/0.61         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.40/0.61      inference('sup+', [status(thm)], ['4', '11'])).
% 0.40/0.61  thf(l45_zfmisc_1, axiom,
% 0.40/0.61    (![A:$i,B:$i,C:$i]:
% 0.40/0.61     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.40/0.61       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.40/0.61            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.40/0.61  thf('13', plain,
% 0.40/0.61      (![X26 : $i, X28 : $i, X29 : $i]:
% 0.40/0.61         ((r1_tarski @ X28 @ (k2_tarski @ X26 @ X29))
% 0.40/0.61          | ((X28) != (k1_tarski @ X29)))),
% 0.40/0.61      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.40/0.61  thf('14', plain,
% 0.40/0.61      (![X26 : $i, X29 : $i]:
% 0.40/0.61         (r1_tarski @ (k1_tarski @ X29) @ (k2_tarski @ X26 @ X29))),
% 0.40/0.61      inference('simplify', [status(thm)], ['13'])).
% 0.40/0.61  thf(t28_xboole_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.40/0.61  thf('15', plain,
% 0.40/0.61      (![X5 : $i, X6 : $i]:
% 0.40/0.61         (((k3_xboole_0 @ X5 @ X6) = (X5)) | ~ (r1_tarski @ X5 @ X6))),
% 0.40/0.61      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.40/0.61  thf('16', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((k3_xboole_0 @ (k1_tarski @ X0) @ (k2_tarski @ X1 @ X0))
% 0.40/0.61           = (k1_tarski @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.61  thf('17', plain,
% 0.40/0.61      (((k1_tarski @ sk_B)
% 0.40/0.61         = (k3_xboole_0 @ (k1_tarski @ sk_A) @ (k1_tarski @ sk_B)))),
% 0.40/0.61      inference('demod', [status(thm)], ['12', '16'])).
% 0.40/0.61  thf(l29_zfmisc_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ( k3_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( k1_tarski @ B ) ) =>
% 0.40/0.61       ( r2_hidden @ B @ A ) ))).
% 0.40/0.61  thf('18', plain,
% 0.40/0.61      (![X22 : $i, X23 : $i]:
% 0.40/0.61         ((r2_hidden @ X22 @ X23)
% 0.40/0.61          | ((k3_xboole_0 @ X23 @ (k1_tarski @ X22)) != (k1_tarski @ X22)))),
% 0.40/0.61      inference('cnf', [status(esa)], [l29_zfmisc_1])).
% 0.40/0.61  thf('19', plain,
% 0.40/0.61      ((((k1_tarski @ sk_B) != (k1_tarski @ sk_B))
% 0.40/0.61        | (r2_hidden @ sk_B @ (k1_tarski @ sk_A)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['17', '18'])).
% 0.40/0.61  thf('20', plain, ((r2_hidden @ sk_B @ (k1_tarski @ sk_A))),
% 0.40/0.61      inference('simplify', [status(thm)], ['19'])).
% 0.40/0.61  thf(d1_tarski, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.40/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.40/0.61  thf('21', plain,
% 0.40/0.61      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.40/0.61         (~ (r2_hidden @ X10 @ X9)
% 0.40/0.61          | ((X10) = (X7))
% 0.40/0.61          | ((X9) != (k1_tarski @ X7)))),
% 0.40/0.61      inference('cnf', [status(esa)], [d1_tarski])).
% 0.40/0.61  thf('22', plain,
% 0.40/0.61      (![X7 : $i, X10 : $i]:
% 0.40/0.61         (((X10) = (X7)) | ~ (r2_hidden @ X10 @ (k1_tarski @ X7)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['21'])).
% 0.40/0.61  thf('23', plain, (((sk_B) = (sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['20', '22'])).
% 0.40/0.61  thf('24', plain, (((sk_A) != (sk_B))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('25', plain, ($false),
% 0.40/0.61      inference('simplify_reflect-', [status(thm)], ['23', '24'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
