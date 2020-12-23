%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IIfjvvZzzD

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   46 (  56 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  307 ( 434 expanded)
%              Number of equality atoms :   31 (  41 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(t100_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('0',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X34 @ X35 ) @ X36 )
        = ( k7_relat_1 @ X34 @ ( k3_xboole_0 @ X35 @ X36 ) ) )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t100_relat_1])).

thf(t103_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
          = ( k7_relat_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A )
            = ( k7_relat_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t103_relat_1])).

thf('1',plain,(
    ( k7_relat_1 @ ( k7_relat_1 @ sk_C @ sk_B ) @ sk_A )
 != ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k7_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) )
     != ( k7_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ( k7_relat_1 @ sk_C @ ( k3_xboole_0 @ sk_B @ sk_A ) )
 != ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('6',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t14_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ B )
        & ! [D: $i] :
            ( ( ( r1_tarski @ A @ D )
              & ( r1_tarski @ C @ D ) )
           => ( r1_tarski @ B @ D ) ) )
     => ( B
        = ( k2_xboole_0 @ A @ C ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X5 @ X4 )
      | ( r1_tarski @ X5 @ ( sk_D @ X5 @ X4 @ X3 ) )
      | ( X4
        = ( k2_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k2_xboole_0 @ sk_A @ X0 ) )
      | ( r1_tarski @ X0 @ ( sk_D @ X0 @ sk_B @ sk_A ) )
      | ~ ( r1_tarski @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( r1_tarski @ sk_B @ ( sk_D @ sk_B @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X5 @ X4 )
      | ~ ( r1_tarski @ X4 @ ( sk_D @ X5 @ X4 @ X3 ) )
      | ( X4
        = ( k2_xboole_0 @ X3 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t14_xboole_1])).

thf('12',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ~ ( r1_tarski @ sk_B @ sk_B )
    | ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['5'])).

thf('14',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( sk_B
      = ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ( sk_B
      = ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t21_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = A ) )).

thf('17',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k3_xboole_0 @ X6 @ ( k2_xboole_0 @ X6 @ X7 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[t21_xboole_1])).

thf('18',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['16','17'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k2_tarski @ X9 @ X8 )
      = ( k2_tarski @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('20',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    ( k7_relat_1 @ sk_C @ sk_A )
 != ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['4','24'])).

thf('26',plain,(
    $false ),
    inference(simplify,[status(thm)],['25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.IIfjvvZzzD
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:10:48 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 39 iterations in 0.023s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.47  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.47  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.47  thf(t100_relat_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ C ) =>
% 0.20/0.47       ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.20/0.47         ( k7_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) ) ))).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.47         (((k7_relat_1 @ (k7_relat_1 @ X34 @ X35) @ X36)
% 0.20/0.47            = (k7_relat_1 @ X34 @ (k3_xboole_0 @ X35 @ X36)))
% 0.20/0.47          | ~ (v1_relat_1 @ X34))),
% 0.20/0.47      inference('cnf', [status(esa)], [t100_relat_1])).
% 0.20/0.47  thf(t103_relat_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( v1_relat_1 @ C ) =>
% 0.20/0.47       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.47         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) = ( k7_relat_1 @ C @ A ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.47        ( ( v1_relat_1 @ C ) =>
% 0.20/0.47          ( ( r1_tarski @ A @ B ) =>
% 0.20/0.47            ( ( k7_relat_1 @ ( k7_relat_1 @ C @ B ) @ A ) =
% 0.20/0.47              ( k7_relat_1 @ C @ A ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t103_relat_1])).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (((k7_relat_1 @ (k7_relat_1 @ sk_C @ sk_B) @ sk_A)
% 0.20/0.47         != (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((((k7_relat_1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.20/0.47          != (k7_relat_1 @ sk_C @ sk_A))
% 0.20/0.47        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf('3', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (((k7_relat_1 @ sk_C @ (k3_xboole_0 @ sk_B @ sk_A))
% 0.20/0.47         != (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.47  thf(d10_xboole_0, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.20/0.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.47  thf('6', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.47  thf('7', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t14_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i]:
% 0.20/0.47     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ B ) & 
% 0.20/0.47         ( ![D:$i]:
% 0.20/0.47           ( ( ( r1_tarski @ A @ D ) & ( r1_tarski @ C @ D ) ) =>
% 0.20/0.47             ( r1_tarski @ B @ D ) ) ) ) =>
% 0.20/0.47       ( ( B ) = ( k2_xboole_0 @ A @ C ) ) ))).
% 0.20/0.47  thf('8', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         (~ (r1_tarski @ X3 @ X4)
% 0.20/0.47          | ~ (r1_tarski @ X5 @ X4)
% 0.20/0.47          | (r1_tarski @ X5 @ (sk_D @ X5 @ X4 @ X3))
% 0.20/0.47          | ((X4) = (k2_xboole_0 @ X3 @ X5)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.20/0.47  thf('9', plain,
% 0.20/0.47      (![X0 : $i]:
% 0.20/0.47         (((sk_B) = (k2_xboole_0 @ sk_A @ X0))
% 0.20/0.47          | (r1_tarski @ X0 @ (sk_D @ X0 @ sk_B @ sk_A))
% 0.20/0.47          | ~ (r1_tarski @ X0 @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (((r1_tarski @ sk_B @ (sk_D @ sk_B @ sk_B @ sk_A))
% 0.20/0.47        | ((sk_B) = (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['6', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.47         (~ (r1_tarski @ X3 @ X4)
% 0.20/0.47          | ~ (r1_tarski @ X5 @ X4)
% 0.20/0.47          | ~ (r1_tarski @ X4 @ (sk_D @ X5 @ X4 @ X3))
% 0.20/0.47          | ((X4) = (k2_xboole_0 @ X3 @ X5)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t14_xboole_1])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      ((((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))
% 0.20/0.47        | ((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))
% 0.20/0.47        | ~ (r1_tarski @ sk_B @ sk_B)
% 0.20/0.47        | ~ (r1_tarski @ sk_A @ sk_B))),
% 0.20/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.47  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.20/0.47      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.47  thf('14', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('15', plain,
% 0.20/0.47      ((((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))
% 0.20/0.47        | ((sk_B) = (k2_xboole_0 @ sk_A @ sk_B)))),
% 0.20/0.47      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.47  thf('16', plain, (((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 0.20/0.47      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.47  thf(t21_xboole_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.20/0.47  thf('17', plain,
% 0.20/0.47      (![X6 : $i, X7 : $i]:
% 0.20/0.47         ((k3_xboole_0 @ X6 @ (k2_xboole_0 @ X6 @ X7)) = (X6))),
% 0.20/0.47      inference('cnf', [status(esa)], [t21_xboole_1])).
% 0.20/0.47  thf('18', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (sk_A))),
% 0.20/0.47      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.47  thf(commutativity_k2_tarski, axiom,
% 0.20/0.47    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      (![X8 : $i, X9 : $i]: ((k2_tarski @ X9 @ X8) = (k2_tarski @ X8 @ X9))),
% 0.20/0.47      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.20/0.47  thf(t12_setfam_1, axiom,
% 0.20/0.47    (![A:$i,B:$i]:
% 0.20/0.47     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X32 : $i, X33 : $i]:
% 0.20/0.47         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 0.20/0.47      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]:
% 0.20/0.47         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['19', '20'])).
% 0.20/0.47  thf('22', plain,
% 0.20/0.47      (![X32 : $i, X33 : $i]:
% 0.20/0.47         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 0.20/0.47      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.47  thf('23', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.20/0.47      inference('sup+', [status(thm)], ['21', '22'])).
% 0.20/0.47  thf('24', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['18', '23'])).
% 0.20/0.47  thf('25', plain,
% 0.20/0.47      (((k7_relat_1 @ sk_C @ sk_A) != (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.47      inference('demod', [status(thm)], ['4', '24'])).
% 0.20/0.47  thf('26', plain, ($false), inference('simplify', [status(thm)], ['25'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
