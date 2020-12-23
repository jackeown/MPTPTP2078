%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LQ68c5DAwN

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:18 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   38 (  41 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :  209 ( 230 expanded)
%              Number of equality atoms :   28 (  31 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_ordinal1_type,type,(
    k1_ordinal1: $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k4_xboole_0 @ X60 @ ( k1_tarski @ X61 ) )
        = X60 )
      | ( r2_hidden @ X61 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('1',plain,(
    ! [X62: $i,X63: $i] :
      ( ( k6_subset_1 @ X62 @ X63 )
      = ( k4_xboole_0 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('2',plain,(
    ! [X60: $i,X61: $i] :
      ( ( ( k6_subset_1 @ X60 @ ( k1_tarski @ X61 ) )
        = X60 )
      | ( r2_hidden @ X61 @ X60 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t52_ordinal1,conjecture,(
    ! [A: $i] :
      ( ( k6_subset_1 @ ( k1_ordinal1 @ A ) @ ( k1_tarski @ A ) )
      = A ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k6_subset_1 @ ( k1_ordinal1 @ A ) @ ( k1_tarski @ A ) )
        = A ) ),
    inference('cnf.neg',[status(esa)],[t52_ordinal1])).

thf('3',plain,(
    ( k6_subset_1 @ ( k1_ordinal1 @ sk_A ) @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_ordinal1,axiom,(
    ! [A: $i] :
      ( ( k1_ordinal1 @ A )
      = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ) )).

thf('4',plain,(
    ! [X66: $i] :
      ( ( k1_ordinal1 @ X66 )
      = ( k2_xboole_0 @ X66 @ ( k1_tarski @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf(t40_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X4 @ X5 ) @ X5 )
      = ( k4_xboole_0 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t40_xboole_1])).

thf('6',plain,(
    ! [X62: $i,X63: $i] :
      ( ( k6_subset_1 @ X62 @ X63 )
      = ( k4_xboole_0 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X62: $i,X63: $i] :
      ( ( k6_subset_1 @ X62 @ X63 )
      = ( k4_xboole_0 @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( ( k6_subset_1 @ ( k2_xboole_0 @ X4 @ X5 ) @ X5 )
      = ( k6_subset_1 @ X4 @ X5 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ ( k1_ordinal1 @ X0 ) @ ( k1_tarski @ X0 ) )
      = ( k6_subset_1 @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    ( k6_subset_1 @ sk_A @ ( k1_tarski @ sk_A ) )
 != sk_A ),
    inference(demod,[status(thm)],['3','9'])).

thf('11',plain,
    ( ( sk_A != sk_A )
    | ( r2_hidden @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['2','10'])).

thf('12',plain,(
    r2_hidden @ sk_A @ sk_A ),
    inference(simplify,[status(thm)],['11'])).

thf(l31_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) )
        = ( k1_tarski @ A ) ) ) )).

thf('13',plain,(
    ! [X55: $i,X56: $i] :
      ( ( ( k3_xboole_0 @ X56 @ ( k1_tarski @ X55 ) )
        = ( k1_tarski @ X55 ) )
      | ~ ( r2_hidden @ X55 @ X56 ) ) ),
    inference(cnf,[status(esa)],[l31_zfmisc_1])).

thf('14',plain,
    ( ( k3_xboole_0 @ sk_A @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t22_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) )
      = A ) )).

thf('15',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k2_xboole_0 @ X2 @ ( k3_xboole_0 @ X2 @ X3 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t22_xboole_1])).

thf('16',plain,
    ( ( k2_xboole_0 @ sk_A @ ( k1_tarski @ sk_A ) )
    = sk_A ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X66: $i] :
      ( ( k1_ordinal1 @ X66 )
      = ( k2_xboole_0 @ X66 @ ( k1_tarski @ X66 ) ) ) ),
    inference(cnf,[status(esa)],[d1_ordinal1])).

thf('18',plain,
    ( ( k1_ordinal1 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['16','17'])).

thf(t14_ordinal1,axiom,(
    ! [A: $i] :
      ( A
     != ( k1_ordinal1 @ A ) ) )).

thf('19',plain,(
    ! [X67: $i] :
      ( X67
     != ( k1_ordinal1 @ X67 ) ) ),
    inference(cnf,[status(esa)],[t14_ordinal1])).

thf('20',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LQ68c5DAwN
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:41:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.36/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.54  % Solved by: fo/fo7.sh
% 0.36/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.54  % done 117 iterations in 0.081s
% 0.36/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.54  % SZS output start Refutation
% 0.36/0.54  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.36/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.54  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(k1_ordinal1_type, type, k1_ordinal1: $i > $i).
% 0.36/0.54  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.36/0.54  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.36/0.54  thf(t65_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.36/0.54       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.36/0.54  thf('0', plain,
% 0.36/0.54      (![X60 : $i, X61 : $i]:
% 0.36/0.54         (((k4_xboole_0 @ X60 @ (k1_tarski @ X61)) = (X60))
% 0.36/0.54          | (r2_hidden @ X61 @ X60))),
% 0.36/0.54      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.36/0.54  thf(redefinition_k6_subset_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.36/0.54  thf('1', plain,
% 0.36/0.54      (![X62 : $i, X63 : $i]:
% 0.36/0.54         ((k6_subset_1 @ X62 @ X63) = (k4_xboole_0 @ X62 @ X63))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.36/0.54  thf('2', plain,
% 0.36/0.54      (![X60 : $i, X61 : $i]:
% 0.36/0.54         (((k6_subset_1 @ X60 @ (k1_tarski @ X61)) = (X60))
% 0.36/0.54          | (r2_hidden @ X61 @ X60))),
% 0.36/0.54      inference('demod', [status(thm)], ['0', '1'])).
% 0.36/0.54  thf(t52_ordinal1, conjecture,
% 0.36/0.54    (![A:$i]:
% 0.36/0.54     ( ( k6_subset_1 @ ( k1_ordinal1 @ A ) @ ( k1_tarski @ A ) ) = ( A ) ))).
% 0.36/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.54    (~( ![A:$i]:
% 0.36/0.54        ( ( k6_subset_1 @ ( k1_ordinal1 @ A ) @ ( k1_tarski @ A ) ) = ( A ) ) )),
% 0.36/0.54    inference('cnf.neg', [status(esa)], [t52_ordinal1])).
% 0.36/0.54  thf('3', plain,
% 0.36/0.54      (((k6_subset_1 @ (k1_ordinal1 @ sk_A) @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.36/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.54  thf(d1_ordinal1, axiom,
% 0.36/0.54    (![A:$i]: ( ( k1_ordinal1 @ A ) = ( k2_xboole_0 @ A @ ( k1_tarski @ A ) ) ))).
% 0.36/0.54  thf('4', plain,
% 0.36/0.54      (![X66 : $i]:
% 0.36/0.54         ((k1_ordinal1 @ X66) = (k2_xboole_0 @ X66 @ (k1_tarski @ X66)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.36/0.54  thf(t40_xboole_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.36/0.54  thf('5', plain,
% 0.36/0.54      (![X4 : $i, X5 : $i]:
% 0.36/0.54         ((k4_xboole_0 @ (k2_xboole_0 @ X4 @ X5) @ X5)
% 0.36/0.54           = (k4_xboole_0 @ X4 @ X5))),
% 0.36/0.54      inference('cnf', [status(esa)], [t40_xboole_1])).
% 0.36/0.54  thf('6', plain,
% 0.36/0.54      (![X62 : $i, X63 : $i]:
% 0.36/0.54         ((k6_subset_1 @ X62 @ X63) = (k4_xboole_0 @ X62 @ X63))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.36/0.54  thf('7', plain,
% 0.36/0.54      (![X62 : $i, X63 : $i]:
% 0.36/0.54         ((k6_subset_1 @ X62 @ X63) = (k4_xboole_0 @ X62 @ X63))),
% 0.36/0.54      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.36/0.54  thf('8', plain,
% 0.36/0.54      (![X4 : $i, X5 : $i]:
% 0.36/0.54         ((k6_subset_1 @ (k2_xboole_0 @ X4 @ X5) @ X5)
% 0.36/0.54           = (k6_subset_1 @ X4 @ X5))),
% 0.36/0.54      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.36/0.54  thf('9', plain,
% 0.36/0.54      (![X0 : $i]:
% 0.36/0.54         ((k6_subset_1 @ (k1_ordinal1 @ X0) @ (k1_tarski @ X0))
% 0.36/0.54           = (k6_subset_1 @ X0 @ (k1_tarski @ X0)))),
% 0.36/0.54      inference('sup+', [status(thm)], ['4', '8'])).
% 0.36/0.54  thf('10', plain, (((k6_subset_1 @ sk_A @ (k1_tarski @ sk_A)) != (sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['3', '9'])).
% 0.36/0.54  thf('11', plain, ((((sk_A) != (sk_A)) | (r2_hidden @ sk_A @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['2', '10'])).
% 0.36/0.54  thf('12', plain, ((r2_hidden @ sk_A @ sk_A)),
% 0.36/0.54      inference('simplify', [status(thm)], ['11'])).
% 0.36/0.54  thf(l31_zfmisc_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]:
% 0.36/0.54     ( ( r2_hidden @ A @ B ) =>
% 0.36/0.54       ( ( k3_xboole_0 @ B @ ( k1_tarski @ A ) ) = ( k1_tarski @ A ) ) ))).
% 0.36/0.54  thf('13', plain,
% 0.36/0.54      (![X55 : $i, X56 : $i]:
% 0.36/0.54         (((k3_xboole_0 @ X56 @ (k1_tarski @ X55)) = (k1_tarski @ X55))
% 0.36/0.54          | ~ (r2_hidden @ X55 @ X56))),
% 0.36/0.54      inference('cnf', [status(esa)], [l31_zfmisc_1])).
% 0.36/0.54  thf('14', plain,
% 0.36/0.54      (((k3_xboole_0 @ sk_A @ (k1_tarski @ sk_A)) = (k1_tarski @ sk_A))),
% 0.36/0.54      inference('sup-', [status(thm)], ['12', '13'])).
% 0.36/0.54  thf(t22_xboole_1, axiom,
% 0.36/0.54    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) = ( A ) ))).
% 0.36/0.54  thf('15', plain,
% 0.36/0.54      (![X2 : $i, X3 : $i]:
% 0.36/0.54         ((k2_xboole_0 @ X2 @ (k3_xboole_0 @ X2 @ X3)) = (X2))),
% 0.36/0.54      inference('cnf', [status(esa)], [t22_xboole_1])).
% 0.36/0.54  thf('16', plain, (((k2_xboole_0 @ sk_A @ (k1_tarski @ sk_A)) = (sk_A))),
% 0.36/0.54      inference('sup+', [status(thm)], ['14', '15'])).
% 0.36/0.54  thf('17', plain,
% 0.36/0.54      (![X66 : $i]:
% 0.36/0.54         ((k1_ordinal1 @ X66) = (k2_xboole_0 @ X66 @ (k1_tarski @ X66)))),
% 0.36/0.54      inference('cnf', [status(esa)], [d1_ordinal1])).
% 0.36/0.54  thf('18', plain, (((k1_ordinal1 @ sk_A) = (sk_A))),
% 0.36/0.54      inference('demod', [status(thm)], ['16', '17'])).
% 0.36/0.54  thf(t14_ordinal1, axiom, (![A:$i]: ( ( A ) != ( k1_ordinal1 @ A ) ))).
% 0.36/0.54  thf('19', plain, (![X67 : $i]: ((X67) != (k1_ordinal1 @ X67))),
% 0.36/0.54      inference('cnf', [status(esa)], [t14_ordinal1])).
% 0.36/0.54  thf('20', plain, ($false),
% 0.36/0.54      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.36/0.54  
% 0.36/0.54  % SZS output end Refutation
% 0.36/0.54  
% 0.36/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
