%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GNqeptfLHi

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 133 expanded)
%              Number of leaves         :   12 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :  220 (1571 expanded)
%              Number of equality atoms :   12 (  39 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t12_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( r2_hidden @ B @ ( k1_funct_2 @ A @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( r2_hidden @ B @ ( k1_funct_2 @ A @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_funct_2 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t11_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ( r2_hidden @ X1 @ ( k1_funct_2 @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t11_funct_2])).

thf('3',plain,
    ( ( r2_hidden @ sk_B @ ( k1_funct_2 @ sk_A @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( r2_hidden @ sk_B @ ( k1_funct_2 @ sk_A @ sk_A ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_funct_2 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['6','7'])).

thf('9',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['6','7'])).

thf('10',plain,(
    ~ ( r2_hidden @ sk_B @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['0','8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['6','7'])).

thf('13',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['6','7'])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ( r2_hidden @ X1 @ ( k1_funct_2 @ X0 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t11_funct_2])).

thf('16',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ ( k1_funct_2 @ k1_xboole_0 @ X2 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X1 @ k1_xboole_0 @ X2 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ k1_xboole_0 @ k1_xboole_0 )
    | ( r2_hidden @ sk_B @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['6','7'])).

thf('21',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['6','7'])).

thf('22',plain,(
    v1_funct_2 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    r2_hidden @ sk_B @ ( k1_funct_2 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['17','18','22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['10','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.GNqeptfLHi
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:37 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 10 iterations in 0.010s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.20/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(t12_funct_2, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.46       ( r2_hidden @ B @ ( k1_funct_2 @ A @ A ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.46            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.46          ( r2_hidden @ B @ ( k1_funct_2 @ A @ A ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t12_funct_2])).
% 0.20/0.46  thf('0', plain, (~ (r2_hidden @ sk_B @ (k1_funct_2 @ sk_A @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(t11_funct_2, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.46       ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.46         ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (((X2) = (k1_xboole_0))
% 0.20/0.46          | ~ (v1_funct_1 @ X1)
% 0.20/0.46          | ~ (v1_funct_2 @ X1 @ X0 @ X2)
% 0.20/0.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.20/0.46          | (r2_hidden @ X1 @ (k1_funct_2 @ X0 @ X2)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t11_funct_2])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (((r2_hidden @ sk_B @ (k1_funct_2 @ sk_A @ sk_A))
% 0.20/0.46        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.20/0.46        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.46        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf('4', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('5', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (((r2_hidden @ sk_B @ (k1_funct_2 @ sk_A @ sk_A))
% 0.20/0.46        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.46      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.46  thf('7', plain, (~ (r2_hidden @ sk_B @ (k1_funct_2 @ sk_A @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('8', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.46      inference('clc', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.46      inference('clc', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (~ (r2_hidden @ sk_B @ (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '8', '9'])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('12', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.46      inference('clc', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('13', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.46      inference('clc', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ 
% 0.20/0.46        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.20/0.46      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (((X0) != (k1_xboole_0))
% 0.20/0.46          | ~ (v1_funct_1 @ X1)
% 0.20/0.46          | ~ (v1_funct_2 @ X1 @ X0 @ X2)
% 0.20/0.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.20/0.46          | (r2_hidden @ X1 @ (k1_funct_2 @ X0 @ X2)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t11_funct_2])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i]:
% 0.20/0.46         ((r2_hidden @ X1 @ (k1_funct_2 @ k1_xboole_0 @ X2))
% 0.20/0.46          | ~ (m1_subset_1 @ X1 @ 
% 0.20/0.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X2)))
% 0.20/0.46          | ~ (v1_funct_2 @ X1 @ k1_xboole_0 @ X2)
% 0.20/0.46          | ~ (v1_funct_1 @ X1))),
% 0.20/0.46      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      ((~ (v1_funct_1 @ sk_B)
% 0.20/0.46        | ~ (v1_funct_2 @ sk_B @ k1_xboole_0 @ k1_xboole_0)
% 0.20/0.46        | (r2_hidden @ sk_B @ (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['14', '16'])).
% 0.20/0.46  thf('18', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('19', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('20', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.46      inference('clc', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('21', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.46      inference('clc', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('22', plain, ((v1_funct_2 @ sk_B @ k1_xboole_0 @ k1_xboole_0)),
% 0.20/0.46      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      ((r2_hidden @ sk_B @ (k1_funct_2 @ k1_xboole_0 @ k1_xboole_0))),
% 0.20/0.46      inference('demod', [status(thm)], ['17', '18', '22'])).
% 0.20/0.46  thf('24', plain, ($false), inference('demod', [status(thm)], ['10', '23'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
