%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jj1FLiZlzX

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  51 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    9
%              Number of atoms          :  180 ( 324 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t6_tex_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
              & ( v1_zfmisc_1 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ A )
           => ~ ( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A )
                & ( v1_zfmisc_1 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tex_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('2',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r2_hidden @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['2','3'])).

thf(t63_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k1_tarski @ X4 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t63_subset_1])).

thf('6',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(cc2_tex_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( ~ ( v1_xboole_0 @ B )
           => ~ ( v1_subset_1 @ B @ A ) ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( v1_subset_1 @ X12 @ X13 )
      | ( v1_xboole_0 @ X12 )
      | ~ ( v1_zfmisc_1 @ X13 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_tex_2])).

thf('8',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_zfmisc_1 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) )
    | ~ ( v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ X10 )
      | ( ( k6_domain_1 @ X10 @ X11 )
        = ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('13',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['10','15'])).

thf('17',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ ( k1_tarski @ sk_B ) ) ),
    inference(demod,[status(thm)],['8','9','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_xboole_0 @ ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['17','18'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X3: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('21',plain,(
    $false ),
    inference('sup-',[status(thm)],['19','20'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jj1FLiZlzX
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:59:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 19 iterations in 0.013s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.51  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(t6_tex_2, conjecture,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.51           ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.21/0.51                ( v1_zfmisc_1 @ A ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i]:
% 0.21/0.51        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.51          ( ![B:$i]:
% 0.21/0.51            ( ( m1_subset_1 @ B @ A ) =>
% 0.21/0.51              ( ~( ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) & 
% 0.21/0.51                   ( v1_zfmisc_1 @ A ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t6_tex_2])).
% 0.21/0.51  thf('0', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(t2_subset, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.51       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i]:
% 0.21/0.51         ((r2_hidden @ X8 @ X9)
% 0.21/0.51          | (v1_xboole_0 @ X9)
% 0.21/0.51          | ~ (m1_subset_1 @ X8 @ X9))),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.51  thf('2', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_B @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.51  thf('3', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('4', plain, ((r2_hidden @ sk_B @ sk_A)),
% 0.21/0.51      inference('clc', [status(thm)], ['2', '3'])).
% 0.21/0.51  thf(t63_subset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r2_hidden @ A @ B ) =>
% 0.21/0.51       ( m1_subset_1 @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         ((m1_subset_1 @ (k1_tarski @ X4) @ (k1_zfmisc_1 @ X5))
% 0.21/0.51          | ~ (r2_hidden @ X4 @ X5))),
% 0.21/0.51      inference('cnf', [status(esa)], [t63_subset_1])).
% 0.21/0.51  thf('6', plain, ((m1_subset_1 @ (k1_tarski @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.51  thf(cc2_tex_2, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_zfmisc_1 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.21/0.51           ( ( ~( v1_xboole_0 @ B ) ) => ( ~( v1_subset_1 @ B @ A ) ) ) ) ) ))).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i]:
% 0.21/0.51         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.21/0.51          | ~ (v1_subset_1 @ X12 @ X13)
% 0.21/0.51          | (v1_xboole_0 @ X12)
% 0.21/0.51          | ~ (v1_zfmisc_1 @ X13)
% 0.21/0.51          | (v1_xboole_0 @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc2_tex_2])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_A)
% 0.21/0.51        | ~ (v1_zfmisc_1 @ sk_A)
% 0.21/0.51        | (v1_xboole_0 @ (k1_tarski @ sk_B))
% 0.21/0.51        | ~ (v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('9', plain, ((v1_zfmisc_1 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('10', plain, ((v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('11', plain, ((m1_subset_1 @ sk_B @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k6_domain_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.21/0.51       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      (![X10 : $i, X11 : $i]:
% 0.21/0.51         ((v1_xboole_0 @ X10)
% 0.21/0.51          | ~ (m1_subset_1 @ X11 @ X10)
% 0.21/0.51          | ((k6_domain_1 @ X10 @ X11) = (k1_tarski @ X11)))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      ((((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))
% 0.21/0.51        | (v1_xboole_0 @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('15', plain, (((k6_domain_1 @ sk_A @ sk_B) = (k1_tarski @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf('16', plain, ((v1_subset_1 @ (k1_tarski @ sk_B) @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['10', '15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ (k1_tarski @ sk_B)))),
% 0.21/0.51      inference('demod', [status(thm)], ['8', '9', '16'])).
% 0.21/0.51  thf('18', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('19', plain, ((v1_xboole_0 @ (k1_tarski @ sk_B))),
% 0.21/0.51      inference('clc', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 0.21/0.51  thf('20', plain, (![X3 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 0.21/0.51  thf('21', plain, ($false), inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
