%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hQraNwClyt

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:43:21 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   35 (  45 expanded)
%              Number of leaves         :   14 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :  225 ( 395 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

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
    ! [X2: $i,X3: $i] :
      ( ( ( k2_xboole_0 @ X3 @ X2 )
        = X2 )
      | ~ ( r1_tarski @ X3 @ X2 ) ) ),
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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k10_relat_1 @ X14 @ ( k2_xboole_0 @ X15 @ X16 ) )
        = ( k2_xboole_0 @ ( k10_relat_1 @ X14 @ X15 ) @ ( k10_relat_1 @ X14 @ X16 ) ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t175_relat_1])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ X12 @ ( k2_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X0 @ sk_A ) @ ( k10_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['3','6'])).

thf('8',plain,(
    r1_tarski @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t179_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( r1_tarski @ B @ C )
           => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( r1_tarski @ ( k10_relat_1 @ X18 @ X19 ) @ ( k10_relat_1 @ X17 @ X19 ) )
      | ~ ( r1_tarski @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t179_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k10_relat_1 @ sk_D @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ ( k10_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_tarski @ X4 @ X5 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ sk_C @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k10_relat_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_D @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    $false ),
    inference(demod,[status(thm)],['0','18'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.hQraNwClyt
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.60  % Solved by: fo/fo7.sh
% 0.44/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.60  % done 310 iterations in 0.150s
% 0.44/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.60  % SZS output start Refutation
% 0.44/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.44/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.44/0.60  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.44/0.60  thf(t180_relat_1, conjecture,
% 0.44/0.60    (![A:$i,B:$i,C:$i]:
% 0.44/0.60     ( ( v1_relat_1 @ C ) =>
% 0.44/0.60       ( ![D:$i]:
% 0.44/0.60         ( ( v1_relat_1 @ D ) =>
% 0.44/0.60           ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.44/0.60             ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ D @ B ) ) ) ) ) ))).
% 0.44/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.60        ( ( v1_relat_1 @ C ) =>
% 0.44/0.60          ( ![D:$i]:
% 0.44/0.60            ( ( v1_relat_1 @ D ) =>
% 0.44/0.60              ( ( ( r1_tarski @ C @ D ) & ( r1_tarski @ A @ B ) ) =>
% 0.44/0.60                ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ D @ B ) ) ) ) ) ) )),
% 0.44/0.60    inference('cnf.neg', [status(esa)], [t180_relat_1])).
% 0.44/0.60  thf('0', plain,
% 0.44/0.60      (~ (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_D @ sk_B))),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf('1', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf(t12_xboole_1, axiom,
% 0.44/0.60    (![A:$i,B:$i]:
% 0.44/0.60     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.44/0.60  thf('2', plain,
% 0.44/0.60      (![X2 : $i, X3 : $i]:
% 0.44/0.60         (((k2_xboole_0 @ X3 @ X2) = (X2)) | ~ (r1_tarski @ X3 @ X2))),
% 0.44/0.60      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.44/0.60  thf('3', plain, (((k2_xboole_0 @ sk_A @ sk_B) = (sk_B))),
% 0.44/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.60  thf(t175_relat_1, axiom,
% 0.44/0.60    (![A:$i,B:$i,C:$i]:
% 0.44/0.60     ( ( v1_relat_1 @ C ) =>
% 0.44/0.60       ( ( k10_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.44/0.60         ( k2_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.44/0.60  thf('4', plain,
% 0.44/0.60      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.44/0.60         (((k10_relat_1 @ X14 @ (k2_xboole_0 @ X15 @ X16))
% 0.44/0.60            = (k2_xboole_0 @ (k10_relat_1 @ X14 @ X15) @ 
% 0.44/0.60               (k10_relat_1 @ X14 @ X16)))
% 0.44/0.60          | ~ (v1_relat_1 @ X14))),
% 0.44/0.60      inference('cnf', [status(esa)], [t175_relat_1])).
% 0.44/0.60  thf(t7_xboole_1, axiom,
% 0.44/0.60    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.44/0.60  thf('5', plain,
% 0.44/0.60      (![X12 : $i, X13 : $i]: (r1_tarski @ X12 @ (k2_xboole_0 @ X12 @ X13))),
% 0.44/0.60      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.44/0.60  thf('6', plain,
% 0.44/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.44/0.60         ((r1_tarski @ (k10_relat_1 @ X2 @ X1) @ 
% 0.44/0.60           (k10_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 0.44/0.60          | ~ (v1_relat_1 @ X2))),
% 0.44/0.60      inference('sup+', [status(thm)], ['4', '5'])).
% 0.44/0.60  thf('7', plain,
% 0.44/0.60      (![X0 : $i]:
% 0.44/0.60         ((r1_tarski @ (k10_relat_1 @ X0 @ sk_A) @ (k10_relat_1 @ X0 @ sk_B))
% 0.44/0.60          | ~ (v1_relat_1 @ X0))),
% 0.44/0.60      inference('sup+', [status(thm)], ['3', '6'])).
% 0.44/0.60  thf('8', plain, ((r1_tarski @ sk_C @ sk_D)),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf(t179_relat_1, axiom,
% 0.44/0.60    (![A:$i,B:$i]:
% 0.44/0.60     ( ( v1_relat_1 @ B ) =>
% 0.44/0.60       ( ![C:$i]:
% 0.44/0.60         ( ( v1_relat_1 @ C ) =>
% 0.44/0.60           ( ( r1_tarski @ B @ C ) =>
% 0.44/0.60             ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k10_relat_1 @ C @ A ) ) ) ) ) ))).
% 0.44/0.60  thf('9', plain,
% 0.44/0.60      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.44/0.60         (~ (v1_relat_1 @ X17)
% 0.44/0.60          | (r1_tarski @ (k10_relat_1 @ X18 @ X19) @ (k10_relat_1 @ X17 @ X19))
% 0.44/0.60          | ~ (r1_tarski @ X18 @ X17)
% 0.44/0.60          | ~ (v1_relat_1 @ X18))),
% 0.44/0.60      inference('cnf', [status(esa)], [t179_relat_1])).
% 0.44/0.60  thf('10', plain,
% 0.44/0.60      (![X0 : $i]:
% 0.44/0.60         (~ (v1_relat_1 @ sk_C)
% 0.44/0.60          | (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ (k10_relat_1 @ sk_D @ X0))
% 0.44/0.60          | ~ (v1_relat_1 @ sk_D))),
% 0.44/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.60  thf('11', plain, ((v1_relat_1 @ sk_C)),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf('12', plain, ((v1_relat_1 @ sk_D)),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf('13', plain,
% 0.44/0.60      (![X0 : $i]:
% 0.44/0.60         (r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ (k10_relat_1 @ sk_D @ X0))),
% 0.44/0.60      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.44/0.60  thf(t1_xboole_1, axiom,
% 0.44/0.60    (![A:$i,B:$i,C:$i]:
% 0.44/0.60     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.44/0.60       ( r1_tarski @ A @ C ) ))).
% 0.44/0.60  thf('14', plain,
% 0.44/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.44/0.60         (~ (r1_tarski @ X4 @ X5)
% 0.44/0.60          | ~ (r1_tarski @ X5 @ X6)
% 0.44/0.60          | (r1_tarski @ X4 @ X6))),
% 0.44/0.60      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.44/0.60  thf('15', plain,
% 0.44/0.60      (![X0 : $i, X1 : $i]:
% 0.44/0.60         ((r1_tarski @ (k10_relat_1 @ sk_C @ X0) @ X1)
% 0.44/0.60          | ~ (r1_tarski @ (k10_relat_1 @ sk_D @ X0) @ X1))),
% 0.44/0.60      inference('sup-', [status(thm)], ['13', '14'])).
% 0.44/0.60  thf('16', plain,
% 0.44/0.60      ((~ (v1_relat_1 @ sk_D)
% 0.44/0.60        | (r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.44/0.60           (k10_relat_1 @ sk_D @ sk_B)))),
% 0.44/0.60      inference('sup-', [status(thm)], ['7', '15'])).
% 0.44/0.60  thf('17', plain, ((v1_relat_1 @ sk_D)),
% 0.44/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.60  thf('18', plain,
% 0.44/0.60      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_D @ sk_B))),
% 0.44/0.60      inference('demod', [status(thm)], ['16', '17'])).
% 0.44/0.60  thf('19', plain, ($false), inference('demod', [status(thm)], ['0', '18'])).
% 0.44/0.60  
% 0.44/0.60  % SZS output end Refutation
% 0.44/0.60  
% 0.44/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
