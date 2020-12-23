%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CqEoaPcaP2

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  39 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :  156 ( 319 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v3_setfam_1_type,type,(
    v3_setfam_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X3: $i,X4: $i] :
      ( ~ ( v3_setfam_1 @ X4 @ X3 )
      | ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v3_setfam_1 @ X4 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[d13_setfam_1])).

thf('7',plain,
    ( ( v3_setfam_1 @ sk_C @ sk_A )
    | ( r2_hidden @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( v3_setfam_1 @ sk_C @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    r2_hidden @ sk_A @ sk_C ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    $false ),
    inference(demod,[status(thm)],['4','15'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CqEoaPcaP2
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:17:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.46  % Solved by: fo/fo7.sh
% 0.21/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.46  % done 23 iterations in 0.013s
% 0.21/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.46  % SZS output start Refutation
% 0.21/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.46  thf(v3_setfam_1_type, type, v3_setfam_1: $i > $i > $o).
% 0.21/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.46  thf(t62_setfam_1, conjecture,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.46       ( ![C:$i]:
% 0.21/0.46         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.46           ( ( ( v3_setfam_1 @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.21/0.46             ( v3_setfam_1 @ C @ A ) ) ) ) ))).
% 0.21/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.46    (~( ![A:$i,B:$i]:
% 0.21/0.46        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.46          ( ![C:$i]:
% 0.21/0.46            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.46              ( ( ( v3_setfam_1 @ B @ A ) & ( r1_tarski @ C @ B ) ) =>
% 0.21/0.46                ( v3_setfam_1 @ C @ A ) ) ) ) ) )),
% 0.21/0.46    inference('cnf.neg', [status(esa)], [t62_setfam_1])).
% 0.21/0.46  thf('0', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(d13_setfam_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.21/0.46       ( ( v3_setfam_1 @ B @ A ) <=> ( ~( r2_hidden @ A @ B ) ) ) ))).
% 0.21/0.46  thf('1', plain,
% 0.21/0.46      (![X3 : $i, X4 : $i]:
% 0.21/0.46         (~ (v3_setfam_1 @ X4 @ X3)
% 0.21/0.46          | ~ (r2_hidden @ X3 @ X4)
% 0.21/0.46          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.21/0.46      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.21/0.46  thf('2', plain,
% 0.21/0.46      ((~ (r2_hidden @ sk_A @ sk_B) | ~ (v3_setfam_1 @ sk_B @ sk_A))),
% 0.21/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.46  thf('3', plain, ((v3_setfam_1 @ sk_B @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('4', plain, (~ (r2_hidden @ sk_A @ sk_B)),
% 0.21/0.46      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.46  thf('5', plain,
% 0.21/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('6', plain,
% 0.21/0.46      (![X3 : $i, X4 : $i]:
% 0.21/0.46         ((r2_hidden @ X3 @ X4)
% 0.21/0.46          | (v3_setfam_1 @ X4 @ X3)
% 0.21/0.46          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.21/0.46      inference('cnf', [status(esa)], [d13_setfam_1])).
% 0.21/0.46  thf('7', plain, (((v3_setfam_1 @ sk_C @ sk_A) | (r2_hidden @ sk_A @ sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.21/0.46  thf('8', plain, (~ (v3_setfam_1 @ sk_C @ sk_A)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf('9', plain, ((r2_hidden @ sk_A @ sk_C)),
% 0.21/0.46      inference('clc', [status(thm)], ['7', '8'])).
% 0.21/0.46  thf('10', plain, ((r1_tarski @ sk_C @ sk_B)),
% 0.21/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.46  thf(t3_subset, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.46  thf('11', plain,
% 0.21/0.46      (![X5 : $i, X7 : $i]:
% 0.21/0.46         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 0.21/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.46  thf('12', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_B))),
% 0.21/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.46  thf(l3_subset_1, axiom,
% 0.21/0.46    (![A:$i,B:$i]:
% 0.21/0.46     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.21/0.46  thf('13', plain,
% 0.21/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.46         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.46          | (r2_hidden @ X0 @ X2)
% 0.21/0.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.21/0.46      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.21/0.46  thf('14', plain,
% 0.21/0.46      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.21/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.46  thf('15', plain, ((r2_hidden @ sk_A @ sk_B)),
% 0.21/0.46      inference('sup-', [status(thm)], ['9', '14'])).
% 0.21/0.46  thf('16', plain, ($false), inference('demod', [status(thm)], ['4', '15'])).
% 0.21/0.46  
% 0.21/0.46  % SZS output end Refutation
% 0.21/0.46  
% 0.21/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
