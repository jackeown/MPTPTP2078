%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GBPvKjbWCs

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:32:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  47 expanded)
%              Number of leaves         :   13 (  20 expanded)
%              Depth                    :    9
%              Number of atoms          :  202 ( 283 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t47_zfmisc_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
     => ( r2_hidden @ A @ C ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C )
       => ( r2_hidden @ A @ C ) ) ),
    inference('cnf.neg',[status(esa)],[t47_zfmisc_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('3',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) )
    | ( sk_C
      = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('5',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( r2_hidden @ X68 @ X67 )
      | ~ ( r1_tarski @ ( k2_tarski @ X66 @ X68 ) @ X67 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('8',plain,(
    ! [X62: $i,X63: $i] :
      ( ( r1_tarski @ X62 @ ( k3_tarski @ X63 ) )
      | ~ ( r2_hidden @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('10',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X64 @ X65 ) )
      = ( k2_xboole_0 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( sk_C
    = ( k2_xboole_0 @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ) ),
    inference(demod,[status(thm)],['3','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('14',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( r2_hidden @ X66 @ X67 )
      | ~ ( r1_tarski @ ( k2_tarski @ X66 @ X68 ) @ X67 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X62: $i,X63: $i] :
      ( ( r1_tarski @ X62 @ ( k3_tarski @ X63 ) )
      | ~ ( r2_hidden @ X62 @ X63 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X64: $i,X65: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X64 @ X65 ) )
      = ( k2_xboole_0 @ X64 @ X65 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ ( k2_tarski @ sk_A @ sk_B ) @ sk_C ),
    inference('sup+',[status(thm)],['12','19'])).

thf('21',plain,(
    ! [X66: $i,X67: $i,X68: $i] :
      ( ( r2_hidden @ X66 @ X67 )
      | ~ ( r1_tarski @ ( k2_tarski @ X66 @ X68 ) @ X67 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('22',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GBPvKjbWCs
% 0.14/0.33  % Computer   : n006.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:21:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.21/0.45  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.45  % Solved by: fo/fo7.sh
% 0.21/0.45  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.45  % done 41 iterations in 0.025s
% 0.21/0.45  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.45  % SZS output start Refutation
% 0.21/0.45  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.45  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.45  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.45  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.45  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.21/0.45  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.45  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.45  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.45  thf(t47_zfmisc_1, conjecture,
% 0.21/0.45    (![A:$i,B:$i,C:$i]:
% 0.21/0.45     ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.21/0.45       ( r2_hidden @ A @ C ) ))).
% 0.21/0.45  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.45    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.45        ( ( r1_tarski @ ( k2_xboole_0 @ ( k2_tarski @ A @ B ) @ C ) @ C ) =>
% 0.21/0.45          ( r2_hidden @ A @ C ) ) )),
% 0.21/0.45    inference('cnf.neg', [status(esa)], [t47_zfmisc_1])).
% 0.21/0.45  thf('0', plain, (~ (r2_hidden @ sk_A @ sk_C)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf('1', plain,
% 0.21/0.45      ((r1_tarski @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C) @ sk_C)),
% 0.21/0.45      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.45  thf(d10_xboole_0, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.45  thf('2', plain,
% 0.21/0.45      (![X0 : $i, X2 : $i]:
% 0.21/0.45         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.45  thf('3', plain,
% 0.21/0.45      ((~ (r1_tarski @ sk_C @ (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))
% 0.21/0.45        | ((sk_C) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.45  thf('4', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.21/0.45      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.45  thf('5', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.45      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.45  thf(t38_zfmisc_1, axiom,
% 0.21/0.45    (![A:$i,B:$i,C:$i]:
% 0.21/0.45     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 0.21/0.45       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 0.21/0.45  thf('6', plain,
% 0.21/0.45      (![X66 : $i, X67 : $i, X68 : $i]:
% 0.21/0.45         ((r2_hidden @ X68 @ X67)
% 0.21/0.45          | ~ (r1_tarski @ (k2_tarski @ X66 @ X68) @ X67))),
% 0.21/0.45      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.45  thf('7', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X1 @ X0))),
% 0.21/0.45      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.45  thf(l49_zfmisc_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.21/0.45  thf('8', plain,
% 0.21/0.45      (![X62 : $i, X63 : $i]:
% 0.21/0.45         ((r1_tarski @ X62 @ (k3_tarski @ X63)) | ~ (r2_hidden @ X62 @ X63))),
% 0.21/0.45      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.21/0.45  thf('9', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         (r1_tarski @ X0 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.45  thf(l51_zfmisc_1, axiom,
% 0.21/0.45    (![A:$i,B:$i]:
% 0.21/0.45     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.21/0.45  thf('10', plain,
% 0.21/0.45      (![X64 : $i, X65 : $i]:
% 0.21/0.45         ((k3_tarski @ (k2_tarski @ X64 @ X65)) = (k2_xboole_0 @ X64 @ X65))),
% 0.21/0.45      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.45  thf('11', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.45      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.45  thf('12', plain,
% 0.21/0.45      (((sk_C) = (k2_xboole_0 @ (k2_tarski @ sk_A @ sk_B) @ sk_C))),
% 0.21/0.45      inference('demod', [status(thm)], ['3', '11'])).
% 0.21/0.45  thf('13', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.21/0.45      inference('simplify', [status(thm)], ['4'])).
% 0.21/0.45  thf('14', plain,
% 0.21/0.45      (![X66 : $i, X67 : $i, X68 : $i]:
% 0.21/0.45         ((r2_hidden @ X66 @ X67)
% 0.21/0.45          | ~ (r1_tarski @ (k2_tarski @ X66 @ X68) @ X67))),
% 0.21/0.45      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.45  thf('15', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 0.21/0.45      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.45  thf('16', plain,
% 0.21/0.45      (![X62 : $i, X63 : $i]:
% 0.21/0.45         ((r1_tarski @ X62 @ (k3_tarski @ X63)) | ~ (r2_hidden @ X62 @ X63))),
% 0.21/0.45      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.21/0.45  thf('17', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]:
% 0.21/0.45         (r1_tarski @ X1 @ (k3_tarski @ (k2_tarski @ X1 @ X0)))),
% 0.21/0.45      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.45  thf('18', plain,
% 0.21/0.45      (![X64 : $i, X65 : $i]:
% 0.21/0.45         ((k3_tarski @ (k2_tarski @ X64 @ X65)) = (k2_xboole_0 @ X64 @ X65))),
% 0.21/0.45      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.21/0.45  thf('19', plain,
% 0.21/0.45      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X1 @ X0))),
% 0.21/0.45      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.45  thf('20', plain, ((r1_tarski @ (k2_tarski @ sk_A @ sk_B) @ sk_C)),
% 0.21/0.45      inference('sup+', [status(thm)], ['12', '19'])).
% 0.21/0.45  thf('21', plain,
% 0.21/0.45      (![X66 : $i, X67 : $i, X68 : $i]:
% 0.21/0.45         ((r2_hidden @ X66 @ X67)
% 0.21/0.45          | ~ (r1_tarski @ (k2_tarski @ X66 @ X68) @ X67))),
% 0.21/0.45      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 0.21/0.45  thf('22', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.21/0.45      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.45  thf('23', plain, ($false), inference('demod', [status(thm)], ['0', '22'])).
% 0.21/0.45  
% 0.21/0.45  % SZS output end Refutation
% 0.21/0.45  
% 0.21/0.46  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
