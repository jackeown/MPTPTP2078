%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kXM63wGyTL

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:36 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   32 (  41 expanded)
%              Number of leaves         :   13 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :  171 ( 334 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v3_setfam_1_type,type,(
    v3_setfam_1: $i > $i > $o )).

thf(t62_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( ( v3_setfam_1 @ B @ A )
              & ( r1_tarski @ C @ B ) )
           => ( v3_setfam_1 @ C @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
           => ( ( ( v3_setfam_1 @ B @ A )
                & ( r1_tarski @ C @ B ) )
             => ( v3_setfam_1 @ C @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_setfam_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d13_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( v3_setfam_1 @ B @ A )
      <=> ~ ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v3_setfam_1 @ X9 @ X8 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('2',plain,
    ( ~ ( r2_hidden @ sk_A @ sk_B )
    | ~ ( v3_setfam_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v3_setfam_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( r2_hidden @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('7',plain,
    ( ( k2_xboole_0 @ sk_C @ sk_B )
    = sk_B ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v3_setfam_1 @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('10',plain,
    ( ( v3_setfam_1 @ sk_C @ sk_A )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ~ ( v3_setfam_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(clc,[status(thm)],['10','11'])).

thf(d3_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            | ( r2_hidden @ D @ B ) ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X0 @ X3 )
      | ( r2_hidden @ X0 @ X2 )
      | ( X2
       != ( k2_xboole_0 @ X3 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[d3_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ ( k2_xboole_0 @ X3 @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X3 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_A @ ( k2_xboole_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup+',[status(thm)],['7','15'])).

thf('17',plain,(
    $false ),
    inference(demod,[status(thm)],['4','16'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.kXM63wGyTL
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:00:36 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 17 iterations in 0.013s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.19/0.46  thf(v3_setfam_1_type, type, v3_setfam_1: $i > $i > $o).
% 0.19/0.46  thf(t62_setfam_1, conjecture,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.46       ( ![C:$i]:
% 0.19/0.46         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.46           ( ( ( v3_setfam_1 @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.19/0.46             ( v3_setfam_1 @ C @ A ) ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i,B:$i]:
% 0.19/0.46        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.46          ( ![C:$i]:
% 0.19/0.46            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.46              ( ( ( v3_setfam_1 @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.19/0.46                ( v3_setfam_1 @ C @ A ) ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t62_setfam_1])).
% 0.19/0.46  thf('0', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(d13_setfam_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.19/0.46       ( ( v3_setfam_1 @ B @ A ) <=> ( ~( r2_hidden @ A @ B ) ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X8 : $i, X9 : $i]:
% 0.19/0.46         (~ (v3_setfam_1 @ X9 @ X8)
% 0.19/0.46          | ~ (r2_hidden @ X8 @ X9)
% 0.19/0.46          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8))))),
% 0.19/0.46      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      ((~ (r2_hidden @ sk_A @ sk_B) | ~ (v3_setfam_1 @ sk_B @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.46  thf('3', plain, ((v3_setfam_1 @ sk_B @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('4', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.19/0.46      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.46  thf('5', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(t12_xboole_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X6 : $i, X7 : $i]:
% 0.19/0.46         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.19/0.46      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.19/0.46  thf('7', plain, (((k2_xboole_0 @ sk_C @ sk_B) = (sk_B))),
% 0.19/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.46  thf('8', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('9', plain,
% 0.19/0.46      (![X8 : $i, X9 : $i]:
% 0.19/0.46         ((r2_hidden @ X8 @ X9)
% 0.19/0.46          | (v3_setfam_1 @ X9 @ X8)
% 0.19/0.46          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X8))))),
% 0.19/0.46      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.19/0.46  thf('10', plain, (((v3_setfam_1 @ sk_C @ sk_A) | (r2_hidden @ sk_A @ sk_C))),
% 0.19/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.46  thf('11', plain, (~ (v3_setfam_1 @ sk_C @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('12', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.19/0.46      inference('clc', [status(thm)], ['10', '11'])).
% 0.19/0.46  thf(d3_xboole_0, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( ( C ) = ( k2_xboole_0 @ A @ B ) ) <=>
% 0.19/0.46       ( ![D:$i]:
% 0.19/0.46         ( ( r2_hidden @ D @ C ) <=>
% 0.19/0.46           ( ( r2_hidden @ D @ A ) | ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.46         (~ (r2_hidden @ X0 @ X3)
% 0.19/0.46          | (r2_hidden @ X0 @ X2)
% 0.19/0.46          | ((X2) != (k2_xboole_0 @ X3 @ X1)))),
% 0.19/0.46      inference('cnf', [status(esa)], [d3_xboole_0])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i, X3 : $i]:
% 0.19/0.46         ((r2_hidden @ X0 @ (k2_xboole_0 @ X3 @ X1)) | ~ (r2_hidden @ X0 @ X3))),
% 0.19/0.46      inference('simplify', [status(thm)], ['13'])).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      (![X0 : $i]: (r2_hidden @ sk_A @ (k2_xboole_0 @ sk_C @ X0))),
% 0.19/0.46      inference('sup-', [status(thm)], ['12', '14'])).
% 0.19/0.46  thf('16', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.19/0.46      inference('sup+', [status(thm)], ['7', '15'])).
% 0.19/0.46  thf('17', plain, ($false), inference('demod', [status(thm)], ['4', '16'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.46  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
