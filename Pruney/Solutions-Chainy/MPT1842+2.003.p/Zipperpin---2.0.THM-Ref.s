%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.k9JlKUyyEX

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   56 (  80 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  312 ( 572 expanded)
%              Number of equality atoms :   20 (  23 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t7_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v1_xboole_0 @ A )
          & ~ ( v1_zfmisc_1 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ A )
           => ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_tex_2])).

thf('0',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X16 @ X15 )
      | ( ( k6_domain_1 @ X15 @ X16 )
        = ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B_1 )
      = ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_1 )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ X10 )
      | ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('9',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    r2_hidden @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['9','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( X7 = X4 )
      | ( X6
       != ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('14',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7 = X4 )
      | ~ ( r2_hidden @ X7 @ ( k1_tarski @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    r1_tarski @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['11','18'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('20',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('21',plain,(
    m1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i] :
      ( ( X20 = X19 )
      | ( v1_subset_1 @ X20 @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('23',plain,
    ( ( v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A )
    | ( ( k1_tarski @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B_1 )
    = ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(d1_tex_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ( ( v1_zfmisc_1 @ A )
      <=> ? [B: $i] :
            ( ( A
              = ( k6_domain_1 @ A @ B ) )
            & ( m1_subset_1 @ B @ A ) ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17
       != ( k6_domain_1 @ X17 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ X17 )
      | ( v1_zfmisc_1 @ X17 )
      | ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d1_tex_2])).

thf('26',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_zfmisc_1 @ sk_A )
    | ~ ( m1_subset_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_A
     != ( k1_tarski @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_zfmisc_1 @ sk_A )
    | ( sk_A
     != ( k1_tarski @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ~ ( v1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_A
 != ( k1_tarski @ sk_B_1 ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    v1_subset_1 @ ( k1_tarski @ sk_B_1 ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['23','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['6','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.k9JlKUyyEX
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:33:08 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 59 iterations in 0.027s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.48  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.48  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.22/0.48  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(t7_tex_2, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.48           ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.48          ( ![B:$i]:
% 0.22/0.48            ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.48              ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t7_tex_2])).
% 0.22/0.48  thf('0', plain, (~ (v1_subset_1 @ (k6_domain_1 @ sk_A @ sk_B_1) @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain, ((m1_subset_1 @ sk_B_1 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(redefinition_k6_domain_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.22/0.48       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X15 : $i, X16 : $i]:
% 0.22/0.48         ((v1_xboole_0 @ X15)
% 0.22/0.48          | ~ (m1_subset_1 @ X16 @ X15)
% 0.22/0.48          | ((k6_domain_1 @ X15 @ X16) = (k1_tarski @ X16)))),
% 0.22/0.48      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      ((((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))
% 0.22/0.48        | (v1_xboole_0 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.48  thf('4', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('5', plain, (((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))),
% 0.22/0.48      inference('clc', [status(thm)], ['3', '4'])).
% 0.22/0.48  thf('6', plain, (~ (v1_subset_1 @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.22/0.48      inference('demod', [status(thm)], ['0', '5'])).
% 0.22/0.48  thf('7', plain, ((m1_subset_1 @ sk_B_1 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(d2_subset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( v1_xboole_0 @ A ) =>
% 0.22/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.22/0.48       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X9 : $i, X10 : $i]:
% 0.22/0.48         (~ (m1_subset_1 @ X9 @ X10)
% 0.22/0.48          | (r2_hidden @ X9 @ X10)
% 0.22/0.48          | (v1_xboole_0 @ X10))),
% 0.22/0.48      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.22/0.48  thf('9', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_B_1 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.48  thf('10', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('11', plain, ((r2_hidden @ sk_B_1 @ sk_A)),
% 0.22/0.48      inference('clc', [status(thm)], ['9', '10'])).
% 0.22/0.48  thf(d3_tarski, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.48  thf('12', plain,
% 0.22/0.48      (![X1 : $i, X3 : $i]:
% 0.22/0.48         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.22/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.48  thf(d1_tarski, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.22/0.48       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X7 @ X6) | ((X7) = (X4)) | ((X6) != (k1_tarski @ X4)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d1_tarski])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      (![X4 : $i, X7 : $i]:
% 0.22/0.48         (((X7) = (X4)) | ~ (r2_hidden @ X7 @ (k1_tarski @ X4)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['13'])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.22/0.48          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['12', '14'])).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X1 : $i, X3 : $i]:
% 0.22/0.48         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.22/0.48      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.48  thf('17', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.48          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.22/0.48          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.22/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.22/0.48      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.48  thf('19', plain, ((r1_tarski @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.22/0.48      inference('sup-', [status(thm)], ['11', '18'])).
% 0.22/0.48  thf(t3_subset, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.48  thf('20', plain,
% 0.22/0.48      (![X12 : $i, X14 : $i]:
% 0.22/0.48         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.22/0.48      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      ((m1_subset_1 @ (k1_tarski @ sk_B_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.48  thf(d7_subset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.48       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.22/0.48  thf('22', plain,
% 0.22/0.48      (![X19 : $i, X20 : $i]:
% 0.22/0.48         (((X20) = (X19))
% 0.22/0.48          | (v1_subset_1 @ X20 @ X19)
% 0.22/0.48          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X19)))),
% 0.22/0.48      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.22/0.48  thf('23', plain,
% 0.22/0.48      (((v1_subset_1 @ (k1_tarski @ sk_B_1) @ sk_A)
% 0.22/0.48        | ((k1_tarski @ sk_B_1) = (sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.48  thf('24', plain, (((k6_domain_1 @ sk_A @ sk_B_1) = (k1_tarski @ sk_B_1))),
% 0.22/0.48      inference('clc', [status(thm)], ['3', '4'])).
% 0.22/0.48  thf(d1_tex_2, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.48       ( ( v1_zfmisc_1 @ A ) <=>
% 0.22/0.48         ( ?[B:$i]:
% 0.22/0.48           ( ( ( A ) = ( k6_domain_1 @ A @ B ) ) & ( m1_subset_1 @ B @ A ) ) ) ) ))).
% 0.22/0.48  thf('25', plain,
% 0.22/0.48      (![X17 : $i, X18 : $i]:
% 0.22/0.48         (((X17) != (k6_domain_1 @ X17 @ X18))
% 0.22/0.48          | ~ (m1_subset_1 @ X18 @ X17)
% 0.22/0.48          | (v1_zfmisc_1 @ X17)
% 0.22/0.48          | (v1_xboole_0 @ X17))),
% 0.22/0.48      inference('cnf', [status(esa)], [d1_tex_2])).
% 0.22/0.48  thf('26', plain,
% 0.22/0.48      ((((sk_A) != (k1_tarski @ sk_B_1))
% 0.22/0.48        | (v1_xboole_0 @ sk_A)
% 0.22/0.48        | (v1_zfmisc_1 @ sk_A)
% 0.22/0.48        | ~ (m1_subset_1 @ sk_B_1 @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.48  thf('27', plain, ((m1_subset_1 @ sk_B_1 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('28', plain,
% 0.22/0.48      ((((sk_A) != (k1_tarski @ sk_B_1))
% 0.22/0.48        | (v1_xboole_0 @ sk_A)
% 0.22/0.48        | (v1_zfmisc_1 @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.48  thf('29', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('30', plain, (((v1_zfmisc_1 @ sk_A) | ((sk_A) != (k1_tarski @ sk_B_1)))),
% 0.22/0.48      inference('clc', [status(thm)], ['28', '29'])).
% 0.22/0.48  thf('31', plain, (~ (v1_zfmisc_1 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('32', plain, (((sk_A) != (k1_tarski @ sk_B_1))),
% 0.22/0.48      inference('clc', [status(thm)], ['30', '31'])).
% 0.22/0.48  thf('33', plain, ((v1_subset_1 @ (k1_tarski @ sk_B_1) @ sk_A)),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['23', '32'])).
% 0.22/0.48  thf('34', plain, ($false), inference('demod', [status(thm)], ['6', '33'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
