%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tb6v1FMIRC

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:14 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   46 (  48 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :  195 ( 205 expanded)
%              Number of equality atoms :   14 (  15 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(t18_yellow_1,conjecture,(
    ! [A: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t18_yellow_1])).

thf('0',plain,(
    ( k3_yellow_0 @ ( k3_yellow_1 @ sk_A ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X13: $i] :
      ( ( k9_setfam_1 @ X13 )
      = ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('6',plain,(
    ! [X10: $i,X12: $i] :
      ( ( m1_subset_1 @ X10 @ ( k9_setfam_1 @ X12 ) )
      | ~ ( r1_tarski @ X10 @ X12 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('8',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( r2_hidden @ X1 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('10',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('11',plain,(
    ! [X13: $i] :
      ( ( k9_setfam_1 @ X13 )
      = ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('12',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k9_setfam_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k9_setfam_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(clc,[status(thm)],['9','12'])).

thf(t13_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
          = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X14: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X14 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X14 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('16',plain,(
    ! [X14: $i] :
      ( ( ( k3_yellow_0 @ ( k2_yellow_1 @ X14 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X14 ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('19',plain,(
    ! [X15: $i] :
      ( ( k3_yellow_1 @ X15 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','20'])).

thf('22',plain,(
    $false ),
    inference(simplify,[status(thm)],['21'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.tb6v1FMIRC
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:22:03 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 26 iterations in 0.014s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.19/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.46  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.46  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.19/0.46  thf(t18_yellow_1, conjecture,
% 0.19/0.46    (![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t18_yellow_1])).
% 0.19/0.46  thf('0', plain, (((k3_yellow_0 @ (k3_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(d3_tarski, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( r1_tarski @ A @ B ) <=>
% 0.19/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X4 : $i, X6 : $i]:
% 0.19/0.46         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.19/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.19/0.46  thf(d1_xboole_0, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.46      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.46  thf('3', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.46  thf(t3_subset, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.46  thf('4', plain,
% 0.19/0.46      (![X10 : $i, X12 : $i]:
% 0.19/0.46         ((m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.19/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.46  thf(redefinition_k9_setfam_1, axiom,
% 0.19/0.46    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.19/0.46  thf('5', plain, (![X13 : $i]: ((k9_setfam_1 @ X13) = (k1_zfmisc_1 @ X13))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X10 : $i, X12 : $i]:
% 0.19/0.46         ((m1_subset_1 @ X10 @ (k9_setfam_1 @ X12)) | ~ (r1_tarski @ X10 @ X12))),
% 0.19/0.46      inference('demod', [status(thm)], ['4', '5'])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k9_setfam_1 @ X0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['3', '6'])).
% 0.19/0.46  thf(t2_subset, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ A @ B ) =>
% 0.19/0.46       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      (![X8 : $i, X9 : $i]:
% 0.19/0.46         ((r2_hidden @ X8 @ X9)
% 0.19/0.46          | (v1_xboole_0 @ X9)
% 0.19/0.46          | ~ (m1_subset_1 @ X8 @ X9))),
% 0.19/0.46      inference('cnf', [status(esa)], [t2_subset])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (v1_xboole_0 @ X1)
% 0.19/0.46          | (v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.19/0.46          | (r2_hidden @ X1 @ (k9_setfam_1 @ X0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.46  thf(fc1_subset_1, axiom,
% 0.19/0.46    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.46  thf('10', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.19/0.46      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.19/0.46  thf('11', plain, (![X13 : $i]: ((k9_setfam_1 @ X13) = (k1_zfmisc_1 @ X13))),
% 0.19/0.46      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.19/0.46  thf('12', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k9_setfam_1 @ X7))),
% 0.19/0.46      inference('demod', [status(thm)], ['10', '11'])).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         ((r2_hidden @ X1 @ (k9_setfam_1 @ X0)) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.46      inference('clc', [status(thm)], ['9', '12'])).
% 0.19/0.46  thf(t13_yellow_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.46       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.19/0.46         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (![X14 : $i]:
% 0.19/0.46         (~ (r2_hidden @ k1_xboole_0 @ X14)
% 0.19/0.46          | ((k3_yellow_0 @ (k2_yellow_1 @ X14)) = (k1_xboole_0))
% 0.19/0.46          | (v1_xboole_0 @ X14))),
% 0.19/0.46      inference('cnf', [status(esa)], [t13_yellow_1])).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.19/0.46      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.19/0.46  thf('16', plain,
% 0.19/0.46      (![X14 : $i]:
% 0.19/0.46         (((k3_yellow_0 @ (k2_yellow_1 @ X14)) = (k1_xboole_0))
% 0.19/0.46          | ~ (r2_hidden @ k1_xboole_0 @ X14))),
% 0.19/0.46      inference('clc', [status(thm)], ['14', '15'])).
% 0.19/0.46  thf('17', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.19/0.46          | ((k3_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0))) = (k1_xboole_0)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['13', '16'])).
% 0.19/0.46  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.46  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.46      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.46  thf(t4_yellow_1, axiom,
% 0.19/0.46    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.19/0.46  thf('19', plain,
% 0.19/0.46      (![X15 : $i]: ((k3_yellow_1 @ X15) = (k2_yellow_1 @ (k9_setfam_1 @ X15)))),
% 0.19/0.46      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.19/0.46  thf('20', plain,
% 0.19/0.46      (![X0 : $i]: ((k3_yellow_0 @ (k3_yellow_1 @ X0)) = (k1_xboole_0))),
% 0.19/0.46      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.19/0.46  thf('21', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.19/0.46      inference('demod', [status(thm)], ['0', '20'])).
% 0.19/0.46  thf('22', plain, ($false), inference('simplify', [status(thm)], ['21'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
