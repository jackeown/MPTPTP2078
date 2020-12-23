%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7hphThInmE

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:41:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   44 (  85 expanded)
%              Number of leaves         :   16 (  34 expanded)
%              Depth                    :    9
%              Number of atoms          :  293 ( 663 expanded)
%              Number of equality atoms :   27 (  67 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t120_relat_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
       => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
          = A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
         => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
            = A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t120_relat_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t20_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C )
        & ! [D: $i] :
            ( ( ( r1_tarski @ D @ B )
              & ( r1_tarski @ D @ C ) )
           => ( r1_tarski @ D @ A ) ) )
     => ( A
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ( r1_tarski @ ( sk_D @ X5 @ X4 @ X3 ) @ X5 )
      | ( X3
        = ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ X0 ) )
      | ( r1_tarski @ ( sk_D @ X0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( r1_tarski @ ( sk_D @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_A ) @ sk_A )
    | ( sk_A
      = ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( k2_tarski @ X7 @ X6 )
      = ( k2_tarski @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X1 @ X0 ) )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X13 @ X14 ) )
      = ( k3_xboole_0 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( r1_tarski @ ( sk_D @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_A ) @ sk_A )
    | ( sk_A
      = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['5','10'])).

thf(t119_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k2_relat_1 @ ( k8_relat_1 @ X16 @ X15 ) )
        = ( k3_xboole_0 @ ( k2_relat_1 @ X15 ) @ X16 ) )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t119_relat_1])).

thf('13',plain,(
    ( k2_relat_1 @ ( k8_relat_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A )
     != sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('16',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    r1_tarski @ ( sk_D @ sk_A @ ( k2_relat_1 @ sk_B ) @ sk_A ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['11','17'])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X3 @ X5 )
      | ~ ( r1_tarski @ ( sk_D @ X5 @ X4 @ X3 ) @ X3 )
      | ( X3
        = ( k3_xboole_0 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[t20_xboole_1])).

thf('20',plain,
    ( ( sk_A
      = ( k3_xboole_0 @ ( k2_relat_1 @ sk_B ) @ sk_A ) )
    | ~ ( r1_tarski @ sk_A @ sk_A )
    | ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('22',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf('23',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( sk_A
    = ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    ( k3_xboole_0 @ sk_A @ ( k2_relat_1 @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7hphThInmE
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:42:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 22 iterations in 0.016s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k8_relat_1_type, type, k8_relat_1: $i > $i > $i).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.48  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(d10_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.48  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.48      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.48  thf(t120_relat_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.21/0.48         ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) = ( A ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i]:
% 0.21/0.48        ( ( v1_relat_1 @ B ) =>
% 0.21/0.48          ( ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) =>
% 0.21/0.48            ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) = ( A ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t120_relat_1])).
% 0.21/0.48  thf('2', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(t20_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) & 
% 0.21/0.48         ( ![D:$i]:
% 0.21/0.48           ( ( ( r1_tarski @ D @ B ) & ( r1_tarski @ D @ C ) ) =>
% 0.21/0.48             ( r1_tarski @ D @ A ) ) ) ) =>
% 0.21/0.48       ( ( A ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.48          | ~ (r1_tarski @ X3 @ X5)
% 0.21/0.48          | (r1_tarski @ (sk_D @ X5 @ X4 @ X3) @ X5)
% 0.21/0.48          | ((X3) = (k3_xboole_0 @ X4 @ X5)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         (((sk_A) = (k3_xboole_0 @ (k2_relat_1 @ sk_B) @ X0))
% 0.21/0.48          | (r1_tarski @ (sk_D @ X0 @ (k2_relat_1 @ sk_B) @ sk_A) @ X0)
% 0.21/0.48          | ~ (r1_tarski @ sk_A @ X0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (((r1_tarski @ (sk_D @ sk_A @ (k2_relat_1 @ sk_B) @ sk_A) @ sk_A)
% 0.21/0.48        | ((sk_A) = (k3_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.48  thf(commutativity_k2_tarski, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]: ((k2_tarski @ X7 @ X6) = (k2_tarski @ X6 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.21/0.48  thf(t12_setfam_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      (![X13 : $i, X14 : $i]:
% 0.21/0.48         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.48  thf('8', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k1_setfam_1 @ (k2_tarski @ X1 @ X0)) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X13 : $i, X14 : $i]:
% 0.21/0.48         ((k1_setfam_1 @ (k2_tarski @ X13 @ X14)) = (k3_xboole_0 @ X13 @ X14))),
% 0.21/0.48      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (((r1_tarski @ (sk_D @ sk_A @ (k2_relat_1 @ sk_B) @ sk_A) @ sk_A)
% 0.21/0.48        | ((sk_A) = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B))))),
% 0.21/0.48      inference('demod', [status(thm)], ['5', '10'])).
% 0.21/0.48  thf(t119_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( k2_relat_1 @ ( k8_relat_1 @ A @ B ) ) =
% 0.21/0.48         ( k3_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X15 : $i, X16 : $i]:
% 0.21/0.48         (((k2_relat_1 @ (k8_relat_1 @ X16 @ X15))
% 0.21/0.48            = (k3_xboole_0 @ (k2_relat_1 @ X15) @ X16))
% 0.21/0.48          | ~ (v1_relat_1 @ X15))),
% 0.21/0.48      inference('cnf', [status(esa)], [t119_relat_1])).
% 0.21/0.48  thf('13', plain, (((k2_relat_1 @ (k8_relat_1 @ sk_A @ sk_B)) != (sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      ((((k3_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A) != (sk_A))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('16', plain, ((v1_relat_1 @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('17', plain, (((k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)) != (sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      ((r1_tarski @ (sk_D @ sk_A @ (k2_relat_1 @ sk_B) @ sk_A) @ sk_A)),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['11', '17'])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.48         (~ (r1_tarski @ X3 @ X4)
% 0.21/0.48          | ~ (r1_tarski @ X3 @ X5)
% 0.21/0.48          | ~ (r1_tarski @ (sk_D @ X5 @ X4 @ X3) @ X3)
% 0.21/0.48          | ((X3) = (k3_xboole_0 @ X4 @ X5)))),
% 0.21/0.48      inference('cnf', [status(esa)], [t20_xboole_1])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      ((((sk_A) = (k3_xboole_0 @ (k2_relat_1 @ sk_B) @ sk_A))
% 0.21/0.48        | ~ (r1_tarski @ sk_A @ sk_A)
% 0.21/0.48        | ~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('22', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.48      inference('simplify', [status(thm)], ['0'])).
% 0.21/0.48  thf('23', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('24', plain, (((sk_A) = (k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 0.21/0.48  thf('25', plain, (((k3_xboole_0 @ sk_A @ (k2_relat_1 @ sk_B)) != (sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.21/0.48  thf('26', plain, ($false),
% 0.21/0.48      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
