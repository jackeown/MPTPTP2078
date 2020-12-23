%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KmnvGm7scf

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:38:40 EST 2020

% Result     : Theorem 0.57s
% Output     : Refutation 0.57s
% Verified   : 
% Statistics : Number of formulae       :   44 (  57 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :   11
%              Number of atoms          :  268 ( 355 expanded)
%              Number of equality atoms :   36 (  46 expanded)
%              Maximal formula depth    :    9 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t11_setfam_1,conjecture,(
    ! [A: $i] :
      ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k1_setfam_1 @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t11_setfam_1])).

thf('0',plain,(
    ( k1_setfam_1 @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r1_tarski @ B @ C ) )
     => ( ( A = k1_xboole_0 )
        | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X67: $i,X68: $i] :
      ( ( X67 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_3 @ X68 @ X67 ) @ X67 )
      | ( r1_tarski @ X68 @ ( k1_setfam_1 @ X67 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X30: $i,X31: $i] :
      ( ~ ( r2_hidden @ X31 @ X30 )
      | ( X31 = X28 )
      | ( X30
       != ( k1_tarski @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('3',plain,(
    ! [X28: $i,X31: $i] :
      ( ( X31 = X28 )
      | ~ ( r2_hidden @ X31 @ ( k1_tarski @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C_3 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf(idempotence_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ A )
      = A ) )).

thf('5',plain,(
    ! [X10: $i] :
      ( ( k2_xboole_0 @ X10 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[idempotence_k2_xboole_0])).

thf(t49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B )
     != k1_xboole_0 ) )).

thf('6',plain,(
    ! [X51: $i,X52: $i] :
      ( ( k2_xboole_0 @ ( k1_tarski @ X51 ) @ X52 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t49_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X1 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( sk_C_3 @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['4','7'])).

thf(t31_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_tarski @ A ) )
      = A ) )).

thf('9',plain,(
    ! [X47: $i] :
      ( ( k3_tarski @ ( k1_tarski @ X47 ) )
      = X47 ) ),
    inference(cnf,[status(esa)],[t31_zfmisc_1])).

thf(t3_setfam_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ) )).

thf('10',plain,(
    ! [X65: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ X65 ) @ ( k3_tarski @ X65 ) ) ),
    inference(cnf,[status(esa)],[t3_setfam_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) @ X0 ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_3 @ X0 @ ( k1_tarski @ X0 ) )
        = X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X67: $i,X68: $i] :
      ( ( X67 = k1_xboole_0 )
      | ~ ( r1_tarski @ X68 @ ( sk_C_3 @ X68 @ X67 ) )
      | ( r1_tarski @ X68 @ ( k1_setfam_1 @ X67 ) ) ) ),
    inference(cnf,[status(esa)],[t6_setfam_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ X0 )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( X12 != X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( ( k1_tarski @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_tarski @ X0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) )
      | ( X0
        = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('23',plain,(
    ! [X0: $i] :
      ( X0
      = ( k1_setfam_1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(clc,[status(thm)],['21','22'])).

thf('24',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['0','23'])).

thf('25',plain,(
    $false ),
    inference(simplify,[status(thm)],['24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KmnvGm7scf
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:02:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.57/0.82  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.57/0.82  % Solved by: fo/fo7.sh
% 0.57/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.57/0.82  % done 953 iterations in 0.372s
% 0.57/0.82  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.57/0.82  % SZS output start Refutation
% 0.57/0.82  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.57/0.82  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.57/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.57/0.82  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.57/0.82  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.57/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.57/0.82  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 0.57/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.57/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.57/0.82  thf(t11_setfam_1, conjecture,
% 0.57/0.82    (![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.57/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.57/0.82    (~( ![A:$i]: ( ( k1_setfam_1 @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.57/0.82    inference('cnf.neg', [status(esa)], [t11_setfam_1])).
% 0.57/0.82  thf('0', plain, (((k1_setfam_1 @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.57/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.57/0.82  thf(t6_setfam_1, axiom,
% 0.57/0.82    (![A:$i,B:$i]:
% 0.57/0.82     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r1_tarski @ B @ C ) ) ) =>
% 0.57/0.82       ( ( ( A ) = ( k1_xboole_0 ) ) | ( r1_tarski @ B @ ( k1_setfam_1 @ A ) ) ) ))).
% 0.57/0.82  thf('1', plain,
% 0.57/0.82      (![X67 : $i, X68 : $i]:
% 0.57/0.82         (((X67) = (k1_xboole_0))
% 0.57/0.82          | (r2_hidden @ (sk_C_3 @ X68 @ X67) @ X67)
% 0.57/0.82          | (r1_tarski @ X68 @ (k1_setfam_1 @ X67)))),
% 0.57/0.82      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.57/0.82  thf(d1_tarski, axiom,
% 0.57/0.82    (![A:$i,B:$i]:
% 0.57/0.82     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.57/0.82       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.57/0.82  thf('2', plain,
% 0.57/0.82      (![X28 : $i, X30 : $i, X31 : $i]:
% 0.57/0.82         (~ (r2_hidden @ X31 @ X30)
% 0.57/0.82          | ((X31) = (X28))
% 0.57/0.82          | ((X30) != (k1_tarski @ X28)))),
% 0.57/0.82      inference('cnf', [status(esa)], [d1_tarski])).
% 0.57/0.82  thf('3', plain,
% 0.57/0.82      (![X28 : $i, X31 : $i]:
% 0.57/0.82         (((X31) = (X28)) | ~ (r2_hidden @ X31 @ (k1_tarski @ X28)))),
% 0.57/0.82      inference('simplify', [status(thm)], ['2'])).
% 0.57/0.82  thf('4', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]:
% 0.57/0.82         ((r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.57/0.82          | ((k1_tarski @ X0) = (k1_xboole_0))
% 0.57/0.82          | ((sk_C_3 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.57/0.82      inference('sup-', [status(thm)], ['1', '3'])).
% 0.57/0.82  thf(idempotence_k2_xboole_0, axiom,
% 0.57/0.82    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ A ) = ( A ) ))).
% 0.57/0.82  thf('5', plain, (![X10 : $i]: ((k2_xboole_0 @ X10 @ X10) = (X10))),
% 0.57/0.82      inference('cnf', [status(esa)], [idempotence_k2_xboole_0])).
% 0.57/0.82  thf(t49_zfmisc_1, axiom,
% 0.57/0.82    (![A:$i,B:$i]:
% 0.57/0.82     ( ( k2_xboole_0 @ ( k1_tarski @ A ) @ B ) != ( k1_xboole_0 ) ))).
% 0.57/0.82  thf('6', plain,
% 0.57/0.82      (![X51 : $i, X52 : $i]:
% 0.57/0.82         ((k2_xboole_0 @ (k1_tarski @ X51) @ X52) != (k1_xboole_0))),
% 0.57/0.82      inference('cnf', [status(esa)], [t49_zfmisc_1])).
% 0.57/0.82  thf('7', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.57/0.82      inference('sup-', [status(thm)], ['5', '6'])).
% 0.57/0.82  thf('8', plain,
% 0.57/0.82      (![X0 : $i, X1 : $i]:
% 0.57/0.82         ((r1_tarski @ X1 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.57/0.82          | ((sk_C_3 @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.57/0.82      inference('simplify_reflect-', [status(thm)], ['4', '7'])).
% 0.57/0.82  thf(t31_zfmisc_1, axiom,
% 0.57/0.82    (![A:$i]: ( ( k3_tarski @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.57/0.82  thf('9', plain, (![X47 : $i]: ((k3_tarski @ (k1_tarski @ X47)) = (X47))),
% 0.57/0.82      inference('cnf', [status(esa)], [t31_zfmisc_1])).
% 0.57/0.82  thf(t3_setfam_1, axiom,
% 0.57/0.82    (![A:$i]: ( r1_tarski @ ( k1_setfam_1 @ A ) @ ( k3_tarski @ A ) ))).
% 0.57/0.82  thf('10', plain,
% 0.57/0.82      (![X65 : $i]: (r1_tarski @ (k1_setfam_1 @ X65) @ (k3_tarski @ X65))),
% 0.57/0.82      inference('cnf', [status(esa)], [t3_setfam_1])).
% 0.57/0.82  thf('11', plain,
% 0.57/0.82      (![X0 : $i]: (r1_tarski @ (k1_setfam_1 @ (k1_tarski @ X0)) @ X0)),
% 0.57/0.82      inference('sup+', [status(thm)], ['9', '10'])).
% 0.57/0.82  thf(d10_xboole_0, axiom,
% 0.57/0.82    (![A:$i,B:$i]:
% 0.57/0.82     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.57/0.82  thf('12', plain,
% 0.57/0.82      (![X12 : $i, X14 : $i]:
% 0.57/0.82         (((X12) = (X14))
% 0.57/0.82          | ~ (r1_tarski @ X14 @ X12)
% 0.57/0.82          | ~ (r1_tarski @ X12 @ X14))),
% 0.57/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.57/0.82  thf('13', plain,
% 0.57/0.82      (![X0 : $i]:
% 0.57/0.82         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.57/0.82          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.57/0.82      inference('sup-', [status(thm)], ['11', '12'])).
% 0.57/0.82  thf('14', plain,
% 0.57/0.82      (![X0 : $i]:
% 0.57/0.82         (((sk_C_3 @ X0 @ (k1_tarski @ X0)) = (X0))
% 0.57/0.82          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.57/0.82      inference('sup-', [status(thm)], ['8', '13'])).
% 0.57/0.82  thf('15', plain,
% 0.57/0.82      (![X67 : $i, X68 : $i]:
% 0.57/0.82         (((X67) = (k1_xboole_0))
% 0.57/0.82          | ~ (r1_tarski @ X68 @ (sk_C_3 @ X68 @ X67))
% 0.57/0.82          | (r1_tarski @ X68 @ (k1_setfam_1 @ X67)))),
% 0.57/0.82      inference('cnf', [status(esa)], [t6_setfam_1])).
% 0.57/0.82  thf('16', plain,
% 0.57/0.82      (![X0 : $i]:
% 0.57/0.82         (~ (r1_tarski @ X0 @ X0)
% 0.57/0.82          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.57/0.82          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.57/0.82          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.57/0.82      inference('sup-', [status(thm)], ['14', '15'])).
% 0.57/0.82  thf('17', plain,
% 0.57/0.82      (![X12 : $i, X13 : $i]: ((r1_tarski @ X12 @ X13) | ((X12) != (X13)))),
% 0.57/0.82      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.57/0.82  thf('18', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 0.57/0.82      inference('simplify', [status(thm)], ['17'])).
% 0.57/0.82  thf('19', plain,
% 0.57/0.82      (![X0 : $i]:
% 0.57/0.82         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.57/0.82          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.57/0.82          | ((k1_tarski @ X0) = (k1_xboole_0)))),
% 0.57/0.82      inference('demod', [status(thm)], ['16', '18'])).
% 0.57/0.82  thf('20', plain, (![X0 : $i]: ((k1_tarski @ X0) != (k1_xboole_0))),
% 0.57/0.82      inference('sup-', [status(thm)], ['5', '6'])).
% 0.57/0.82  thf('21', plain,
% 0.57/0.82      (![X0 : $i]:
% 0.57/0.82         (((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.57/0.82          | (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.57/0.82      inference('simplify_reflect-', [status(thm)], ['19', '20'])).
% 0.57/0.82  thf('22', plain,
% 0.57/0.82      (![X0 : $i]:
% 0.57/0.82         (~ (r1_tarski @ X0 @ (k1_setfam_1 @ (k1_tarski @ X0)))
% 0.57/0.82          | ((X0) = (k1_setfam_1 @ (k1_tarski @ X0))))),
% 0.57/0.82      inference('sup-', [status(thm)], ['11', '12'])).
% 0.57/0.82  thf('23', plain, (![X0 : $i]: ((X0) = (k1_setfam_1 @ (k1_tarski @ X0)))),
% 0.57/0.82      inference('clc', [status(thm)], ['21', '22'])).
% 0.57/0.82  thf('24', plain, (((sk_A) != (sk_A))),
% 0.57/0.82      inference('demod', [status(thm)], ['0', '23'])).
% 0.57/0.82  thf('25', plain, ($false), inference('simplify', [status(thm)], ['24'])).
% 0.57/0.82  
% 0.57/0.82  % SZS output end Refutation
% 0.57/0.82  
% 0.57/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
