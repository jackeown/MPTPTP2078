%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3qzOr1hF7h

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:20 EST 2020

% Result     : Theorem 0.81s
% Output     : Refutation 0.81s
% Verified   : 
% Statistics : Number of formulae       :   35 (  45 expanded)
%              Number of leaves         :   14 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  232 ( 402 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t180_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ! [D: $i] :
          ( ( v1_relat_1 @ D )
         => ( ( ( r1_tarski @ C @ D )
              & ( r1_tarski @ A @ B ) )
           => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ D @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ! [D: $i] :
            ( ( v1_relat_1 @ D )
           => ( ( ( r1_tarski @ C @ D )
                & ( r1_tarski @ A @ B ) )
             => ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ D @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t180_relat_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('3',plain,
    ( ( k2_xboole_0 @ sk_A @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t175_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('4',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k10_relat_1 @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X15 @ X16 ) @ ( k10_relat_1 @ X15 @ X17 ) ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ ( k10_relat_1 @ X2 @ X0 ) @ ( k10_relat_1 @ X2 @ X1 ) )
        = ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t179_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( r1_tarski @ ( k10_relat_1 @ X19 @ X20 ) @ ( k10_relat_1 @ X18 @ X20 ) )
      | ~ ( r1_tarski @ X19 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t179_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k10_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(t10_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X5 @ ( k2_xboole_0 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t10_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k2_xboole_0 @ X1 @ ( k10_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ X1 ) @ ( k10_relat_1 @ sk_D @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup+',[status(thm)],['6','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X1 ) @ ( k10_relat_1 @ sk_D @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_D @ sk_B ) ),
    inference('sup+',[status(thm)],['3','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3qzOr1hF7h
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:47:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.81/1.02  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.81/1.02  % Solved by: fo/fo7.sh
% 0.81/1.02  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.81/1.02  % done 905 iterations in 0.564s
% 0.81/1.02  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.81/1.02  % SZS output start Refutation
% 0.81/1.02  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.81/1.02  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.81/1.02  thf(sk_B_type, type, sk_B: $i).
% 0.81/1.02  thf(sk_D_type, type, sk_D: $i).
% 0.81/1.02  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.81/1.02  thf(sk_C_type, type, sk_C: $i).
% 0.81/1.02  thf(sk_A_type, type, sk_A: $i).
% 0.81/1.02  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.81/1.02  thf(t180_relat_1, conjecture,
% 0.81/1.02    (![A:$i,B:$i,C:$i]:
% 0.81/1.02     ( ( v1_relat_1 @ C ) =>
% 0.81/1.02       ( ![D:$i]:
% 0.81/1.02         ( ( v1_relat_1 @ D ) =>
% 0.81/1.02           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.81/1.02             ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ D @ B ) ) ) ) ) ))).
% 0.81/1.02  thf(zf_stmt_0, negated_conjecture,
% 0.81/1.02    (~( ![A:$i,B:$i,C:$i]:
% 0.81/1.02        ( ( v1_relat_1 @ C ) =>
% 0.81/1.02          ( ![D:$i]:
% 0.81/1.02            ( ( v1_relat_1 @ D ) =>
% 0.81/1.02              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.81/1.02                ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ D @ B ) ) ) ) ) ) )),
% 0.81/1.02    inference('cnf.neg', [status(esa)], [t180_relat_1])).
% 0.81/1.02  thf('0', plain,
% 0.81/1.02      (~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_D @ sk_B))),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf(t12_xboole_1, axiom,
% 0.81/1.02    (![A:$i,B:$i]:
% 0.81/1.02     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.81/1.02  thf('2', plain,
% 0.81/1.02      (![X8 : $i, X9 : $i]:
% 0.81/1.02         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 0.81/1.02      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.81/1.02  thf('3', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.81/1.02      inference('sup-', [status(thm)], ['1', '2'])).
% 0.81/1.02  thf(t175_relat_1, axiom,
% 0.81/1.02    (![A:$i,B:$i,C:$i]:
% 0.81/1.02     ( ( v1_relat_1 @ C ) =>
% 0.81/1.02       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.81/1.02         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.81/1.02  thf('4', plain,
% 0.81/1.02      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.81/1.02         (((k10_relat_1 @ X15 @ (k2_xboole_0 @ X16 @ X17))
% 0.81/1.02            = (k2_xboole_0 @ (k10_relat_1 @ X15 @ X16) @ 
% 0.81/1.02               (k10_relat_1 @ X15 @ X17)))
% 0.81/1.02          | ~ (v1_relat_1 @ X15))),
% 0.81/1.02      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.81/1.02  thf(commutativity_k2_xboole_0, axiom,
% 0.81/1.02    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.81/1.02  thf('5', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.81/1.02      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.81/1.02  thf('6', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.81/1.02         (((k2_xboole_0 @ (k10_relat_1 @ X2 @ X0) @ (k10_relat_1 @ X2 @ X1))
% 0.81/1.02            = (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.81/1.02          | ~ (v1_relat_1 @ X2))),
% 0.81/1.02      inference('sup+', [status(thm)], ['4', '5'])).
% 0.81/1.02  thf('7', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf(t179_relat_1, axiom,
% 0.81/1.02    (![A:$i,B:$i]:
% 0.81/1.02     ( ( v1_relat_1 @ B ) =>
% 0.81/1.02       ( ![C:$i]:
% 0.81/1.02         ( ( v1_relat_1 @ C ) =>
% 0.81/1.02           ( ( r1_tarski @ B @ C ) =>
% 0.81/1.02             ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.81/1.02  thf('8', plain,
% 0.81/1.02      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.81/1.02         (~ (v1_relat_1 @ X18)
% 0.81/1.02          | (r1_tarski @ (k10_relat_1 @ X19 @ X20) @ (k10_relat_1 @ X18 @ X20))
% 0.81/1.02          | ~ (r1_tarski @ X19 @ X18)
% 0.81/1.02          | ~ (v1_relat_1 @ X19))),
% 0.81/1.02      inference('cnf', [status(esa)], [t179_relat_1])).
% 0.81/1.02  thf('9', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         (~ (v1_relat_1 @ sk_C)
% 0.81/1.02          | (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ (k10_relat_1 @ sk_D @ X0))
% 0.81/1.02          | ~ (v1_relat_1 @ sk_D))),
% 0.81/1.02      inference('sup-', [status(thm)], ['7', '8'])).
% 0.81/1.02  thf('10', plain, ((v1_relat_1 @ sk_C)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('11', plain, ((v1_relat_1 @ sk_D)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('12', plain,
% 0.81/1.02      (![X0 : $i]:
% 0.81/1.02         (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ (k10_relat_1 @ sk_D @ X0))),
% 0.81/1.02      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.81/1.02  thf(t10_xboole_1, axiom,
% 0.81/1.02    (![A:$i,B:$i,C:$i]:
% 0.81/1.02     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ A @ ( k2_xboole_0 @ C @ B ) ) ))).
% 0.81/1.02  thf('13', plain,
% 0.81/1.02      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.81/1.02         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ X5 @ (k2_xboole_0 @ X7 @ X6)))),
% 0.81/1.02      inference('cnf', [status(esa)], [t10_xboole_1])).
% 0.81/1.02  thf('14', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ 
% 0.81/1.02          (k2_xboole_0 @ X1 @ (k10_relat_1 @ sk_D @ X0)))),
% 0.81/1.02      inference('sup-', [status(thm)], ['12', '13'])).
% 0.81/1.02  thf('15', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         ((r1_tarski @ (k10_relat_1 @ sk_C @ X1) @ 
% 0.81/1.02           (k10_relat_1 @ sk_D @ (k2_xboole_0 @ X1 @ X0)))
% 0.81/1.02          | ~ (v1_relat_1 @ sk_D))),
% 0.81/1.02      inference('sup+', [status(thm)], ['6', '14'])).
% 0.81/1.02  thf('16', plain, ((v1_relat_1 @ sk_D)),
% 0.81/1.02      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.81/1.02  thf('17', plain,
% 0.81/1.02      (![X0 : $i, X1 : $i]:
% 0.81/1.02         (r1_tarski @ (k10_relat_1 @ sk_C @ X1) @ 
% 0.81/1.02          (k10_relat_1 @ sk_D @ (k2_xboole_0 @ X1 @ X0)))),
% 0.81/1.02      inference('demod', [status(thm)], ['15', '16'])).
% 0.81/1.02  thf('18', plain,
% 0.81/1.02      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_D @ sk_B))),
% 0.81/1.02      inference('sup+', [status(thm)], ['3', '17'])).
% 0.81/1.02  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.81/1.02  
% 0.81/1.02  % SZS output end Refutation
% 0.81/1.02  
% 0.88/1.03  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
