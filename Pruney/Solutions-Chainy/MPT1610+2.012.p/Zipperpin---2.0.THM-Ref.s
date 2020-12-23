%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vbJ1VJIOwO

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:14 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  44 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  163 ( 174 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :    8 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_yellow_1_type,type,(
    k3_yellow_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_yellow_1_type,type,(
    k2_yellow_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_yellow_0_type,type,(
    k3_yellow_0: $i > $i )).

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

thf(rc2_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ( v1_xboole_0 @ B )
      & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ ( sk_B_1 @ X5 ) @ ( k1_zfmisc_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf('2',plain,(
    ! [X5: $i] :
      ( v1_xboole_0 @ ( sk_B_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[rc2_subset_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('3',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( sk_B_1 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('5',plain,(
    ! [X8: $i] :
      ( ( k9_setfam_1 @ X8 )
      = ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('6',plain,(
    ! [X5: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k9_setfam_1 @ X5 ) ) ),
    inference(demod,[status(thm)],['1','4','5'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ X6 @ X7 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k9_setfam_1 @ X0 ) )
      | ( r2_hidden @ k1_xboole_0 @ ( k9_setfam_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('9',plain,(
    ! [X4: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('10',plain,(
    ! [X8: $i] :
      ( ( k9_setfam_1 @ X8 )
      = ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('11',plain,(
    ! [X4: $i] :
      ~ ( v1_xboole_0 @ ( k9_setfam_1 @ X4 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r2_hidden @ k1_xboole_0 @ ( k9_setfam_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['8','11'])).

thf(t13_yellow_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( r2_hidden @ k1_xboole_0 @ A )
       => ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) )
          = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X9: $i] :
      ( ~ ( r2_hidden @ k1_xboole_0 @ X9 )
      | ( ( k3_yellow_0 @ ( k2_yellow_1 @ X9 ) )
        = k1_xboole_0 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t13_yellow_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('15',plain,(
    ! [X9: $i] :
      ( ( ( k3_yellow_0 @ ( k2_yellow_1 @ X9 ) )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ k1_xboole_0 @ X9 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_yellow_0 @ ( k2_yellow_1 @ ( k9_setfam_1 @ X0 ) ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(t4_yellow_1,axiom,(
    ! [A: $i] :
      ( ( k3_yellow_1 @ A )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ) )).

thf('17',plain,(
    ! [X10: $i] :
      ( ( k3_yellow_1 @ X10 )
      = ( k2_yellow_1 @ ( k9_setfam_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t4_yellow_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k3_yellow_0 @ ( k3_yellow_1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','18'])).

thf('20',plain,(
    $false ),
    inference(simplify,[status(thm)],['19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.vbJ1VJIOwO
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 16 iterations in 0.011s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(k3_yellow_1_type, type, k3_yellow_1: $i > $i).
% 0.21/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.46  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(k2_yellow_1_type, type, k2_yellow_1: $i > $i).
% 0.21/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.46  thf(k3_yellow_0_type, type, k3_yellow_0: $i > $i).
% 0.21/0.46  thf(t18_yellow_1, conjecture,
% 0.21/0.46    (![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i]: ( ( k3_yellow_0 @ ( k3_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t18_yellow_1])).
% 0.21/0.46  thf('0', plain, (((k3_yellow_0 @ (k3_yellow_1 @ sk_A)) != (k1_xboole_0))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(rc2_subset_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ?[B:$i]:
% 0.21/0.46       ( ( v1_xboole_0 @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X5 : $i]: (m1_subset_1 @ (sk_B_1 @ X5) @ (k1_zfmisc_1 @ X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.21/0.46  thf('2', plain, (![X5 : $i]: (v1_xboole_0 @ (sk_B_1 @ X5))),
% 0.21/0.46      inference('cnf', [status(esa)], [rc2_subset_1])).
% 0.21/0.46  thf(l13_xboole_0, axiom,
% 0.21/0.46    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.46  thf('3', plain,
% 0.21/0.46      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.21/0.46      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.46  thf('4', plain, (![X0 : $i]: ((sk_B_1 @ X0) = (k1_xboole_0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.46  thf(redefinition_k9_setfam_1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.46  thf('5', plain, (![X8 : $i]: ((k9_setfam_1 @ X8) = (k1_zfmisc_1 @ X8))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X5 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k9_setfam_1 @ X5))),
% 0.21/0.46      inference('demod', [status(thm)], ['1', '4', '5'])).
% 0.21/0.46  thf(t2_subset, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.46       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.46  thf('7', plain,
% 0.21/0.46      (![X6 : $i, X7 : $i]:
% 0.21/0.46         ((r2_hidden @ X6 @ X7)
% 0.21/0.46          | (v1_xboole_0 @ X7)
% 0.21/0.46          | ~ (m1_subset_1 @ X6 @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.46  thf('8', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((v1_xboole_0 @ (k9_setfam_1 @ X0))
% 0.21/0.46          | (r2_hidden @ k1_xboole_0 @ (k9_setfam_1 @ X0)))),
% 0.21/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.46  thf(fc1_subset_1, axiom,
% 0.21/0.46    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.46  thf('9', plain, (![X4 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 0.21/0.46      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.46  thf('10', plain, (![X8 : $i]: ((k9_setfam_1 @ X8) = (k1_zfmisc_1 @ X8))),
% 0.21/0.46      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.21/0.46  thf('11', plain, (![X4 : $i]: ~ (v1_xboole_0 @ (k9_setfam_1 @ X4))),
% 0.21/0.46      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.46  thf('12', plain,
% 0.21/0.46      (![X0 : $i]: (r2_hidden @ k1_xboole_0 @ (k9_setfam_1 @ X0))),
% 0.21/0.46      inference('clc', [status(thm)], ['8', '11'])).
% 0.21/0.46  thf(t13_yellow_1, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.46       ( ( r2_hidden @ k1_xboole_0 @ A ) =>
% 0.21/0.46         ( ( k3_yellow_0 @ ( k2_yellow_1 @ A ) ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      (![X9 : $i]:
% 0.21/0.46         (~ (r2_hidden @ k1_xboole_0 @ X9)
% 0.21/0.46          | ((k3_yellow_0 @ (k2_yellow_1 @ X9)) = (k1_xboole_0))
% 0.21/0.46          | (v1_xboole_0 @ X9))),
% 0.21/0.46      inference('cnf', [status(esa)], [t13_yellow_1])).
% 0.21/0.46  thf(d1_xboole_0, axiom,
% 0.21/0.46    (![A:$i]:
% 0.21/0.46     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.46      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.46  thf('15', plain,
% 0.21/0.46      (![X9 : $i]:
% 0.21/0.46         (((k3_yellow_0 @ (k2_yellow_1 @ X9)) = (k1_xboole_0))
% 0.21/0.46          | ~ (r2_hidden @ k1_xboole_0 @ X9))),
% 0.21/0.46      inference('clc', [status(thm)], ['13', '14'])).
% 0.21/0.46  thf('16', plain,
% 0.21/0.46      (![X0 : $i]:
% 0.21/0.46         ((k3_yellow_0 @ (k2_yellow_1 @ (k9_setfam_1 @ X0))) = (k1_xboole_0))),
% 0.21/0.46      inference('sup-', [status(thm)], ['12', '15'])).
% 0.21/0.46  thf(t4_yellow_1, axiom,
% 0.21/0.46    (![A:$i]: ( ( k3_yellow_1 @ A ) = ( k2_yellow_1 @ ( k9_setfam_1 @ A ) ) ))).
% 0.21/0.46  thf('17', plain,
% 0.21/0.46      (![X10 : $i]: ((k3_yellow_1 @ X10) = (k2_yellow_1 @ (k9_setfam_1 @ X10)))),
% 0.21/0.46      inference('cnf', [status(esa)], [t4_yellow_1])).
% 0.21/0.46  thf('18', plain,
% 0.21/0.46      (![X0 : $i]: ((k3_yellow_0 @ (k3_yellow_1 @ X0)) = (k1_xboole_0))),
% 0.21/0.46      inference('demod', [status(thm)], ['16', '17'])).
% 0.21/0.46  thf('19', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.46      inference('demod', [status(thm)], ['0', '18'])).
% 0.21/0.46  thf('20', plain, ($false), inference('simplify', [status(thm)], ['19'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
