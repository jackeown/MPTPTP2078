%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dXWgqhb4kz

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:11:52 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   46 (  58 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :   13
%              Number of atoms          :  253 ( 457 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v7_struct_0_type,type,(
    v7_struct_0: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t9_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ~ ( v7_struct_0 @ A )
          & ( l1_struct_0 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_tex_2])).

thf('0',plain,(
    ~ ( v7_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ X5 )
      | ( ( k6_domain_1 @ X5 @ X6 )
        = ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X4 @ X3 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X3 @ X4 ) @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('6',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('7',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X8 = X7 )
      | ( v1_subset_1 @ X8 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) )
    | ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B ) @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k6_domain_1 @ ( u1_struct_0 @ sk_A ) @ sk_B )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['3','10'])).

thf('12',plain,
    ( ( v1_xboole_0 @ ( u1_struct_0 @ sk_A ) )
    | ( ( k1_tarski @ sk_B )
      = ( u1_struct_0 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(fc2_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) )).

thf('13',plain,(
    ! [X1: $i] :
      ( ~ ( v1_xboole_0 @ ( u1_struct_0 @ X1 ) )
      | ~ ( l1_struct_0 @ X1 )
      | ( v2_struct_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[fc2_struct_0])).

thf('14',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( u1_struct_0 @ sk_A ) )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k1_tarski @ sk_B )
    = ( u1_struct_0 @ sk_A ) ),
    inference(clc,[status(thm)],['16','17'])).

thf(fc6_struct_0,axiom,(
    ! [A: $i] :
      ( ( ~ ( v7_struct_0 @ A )
        & ( l1_struct_0 @ A ) )
     => ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )).

thf('19',plain,(
    ! [X2: $i] :
      ( ~ ( v1_zfmisc_1 @ ( u1_struct_0 @ X2 ) )
      | ~ ( l1_struct_0 @ X2 )
      | ( v7_struct_0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc6_struct_0])).

thf('20',plain,
    ( ~ ( v1_zfmisc_1 @ ( k1_tarski @ sk_B ) )
    | ( v7_struct_0 @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc2_zfmisc_1,axiom,(
    ! [A: $i] :
      ( v1_zfmisc_1 @ ( k1_tarski @ A ) ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( v1_zfmisc_1 @ ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[fc2_zfmisc_1])).

thf('22',plain,(
    l1_struct_0 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v7_struct_0 @ sk_A ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    $false ),
    inference(demod,[status(thm)],['0','23'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dXWgqhb4kz
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:45:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 20 iterations in 0.016s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.47  thf(v7_struct_0_type, type, v7_struct_0: $i > $o).
% 0.19/0.47  thf(v1_zfmisc_1_type, type, v1_zfmisc_1: $i > $o).
% 0.19/0.47  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.19/0.47  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.19/0.47  thf(v1_subset_1_type, type, v1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.47  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(t9_tex_2, conjecture,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( ~( v7_struct_0 @ A ) ) & 
% 0.19/0.47         ( l1_struct_0 @ A ) ) =>
% 0.19/0.47       ( ![B:$i]:
% 0.19/0.47         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.47           ( v1_subset_1 @
% 0.19/0.47             ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i]:
% 0.19/0.47        ( ( ( ~( v2_struct_0 @ A ) ) & ( ~( v7_struct_0 @ A ) ) & 
% 0.19/0.47            ( l1_struct_0 @ A ) ) =>
% 0.19/0.47          ( ![B:$i]:
% 0.19/0.47            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.19/0.47              ( v1_subset_1 @
% 0.19/0.47                ( k6_domain_1 @ ( u1_struct_0 @ A ) @ B ) @ ( u1_struct_0 @ A ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t9_tex_2])).
% 0.19/0.47  thf('0', plain, (~ (v7_struct_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(redefinition_k6_domain_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.19/0.47       ( ( k6_domain_1 @ A @ B ) = ( k1_tarski @ B ) ) ))).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      (![X5 : $i, X6 : $i]:
% 0.19/0.47         ((v1_xboole_0 @ X5)
% 0.19/0.47          | ~ (m1_subset_1 @ X6 @ X5)
% 0.19/0.47          | ((k6_domain_1 @ X5 @ X6) = (k1_tarski @ X6)))),
% 0.19/0.47      inference('cnf', [status(esa)], [redefinition_k6_domain_1])).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (k1_tarski @ sk_B))
% 0.19/0.47        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.47  thf('4', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(dt_k6_domain_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( ( ~( v1_xboole_0 @ A ) ) & ( m1_subset_1 @ B @ A ) ) =>
% 0.19/0.47       ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.47  thf('5', plain,
% 0.19/0.47      (![X3 : $i, X4 : $i]:
% 0.19/0.47         ((v1_xboole_0 @ X3)
% 0.19/0.47          | ~ (m1_subset_1 @ X4 @ X3)
% 0.19/0.47          | (m1_subset_1 @ (k6_domain_1 @ X3 @ X4) @ (k1_zfmisc_1 @ X3)))),
% 0.19/0.47      inference('cnf', [status(esa)], [dt_k6_domain_1])).
% 0.19/0.47  thf('6', plain,
% 0.19/0.47      (((m1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.47         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.19/0.47        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.47  thf(d7_subset_1, axiom,
% 0.19/0.47    (![A:$i,B:$i]:
% 0.19/0.47     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.47       ( ( v1_subset_1 @ B @ A ) <=> ( ( B ) != ( A ) ) ) ))).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (![X7 : $i, X8 : $i]:
% 0.19/0.47         (((X8) = (X7))
% 0.19/0.47          | (v1_subset_1 @ X8 @ X7)
% 0.19/0.47          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.19/0.47      inference('cnf', [status(esa)], [d7_subset_1])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.47        | (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.47           (u1_struct_0 @ sk_A))
% 0.19/0.47        | ((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      (~ (v1_subset_1 @ (k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) @ 
% 0.19/0.47          (u1_struct_0 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('10', plain,
% 0.19/0.47      ((((k6_domain_1 @ (u1_struct_0 @ sk_A) @ sk_B) = (u1_struct_0 @ sk_A))
% 0.19/0.47        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('clc', [status(thm)], ['8', '9'])).
% 0.19/0.47  thf('11', plain,
% 0.19/0.47      ((((k1_tarski @ sk_B) = (u1_struct_0 @ sk_A))
% 0.19/0.47        | (v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.47        | (v1_xboole_0 @ (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('sup+', [status(thm)], ['3', '10'])).
% 0.19/0.47  thf('12', plain,
% 0.19/0.47      (((v1_xboole_0 @ (u1_struct_0 @ sk_A))
% 0.19/0.47        | ((k1_tarski @ sk_B) = (u1_struct_0 @ sk_A)))),
% 0.19/0.47      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.47  thf(fc2_struct_0, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( ~( v2_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.47       ( ~( v1_xboole_0 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.47  thf('13', plain,
% 0.19/0.47      (![X1 : $i]:
% 0.19/0.47         (~ (v1_xboole_0 @ (u1_struct_0 @ X1))
% 0.19/0.47          | ~ (l1_struct_0 @ X1)
% 0.19/0.47          | (v2_struct_0 @ X1))),
% 0.19/0.47      inference('cnf', [status(esa)], [fc2_struct_0])).
% 0.19/0.47  thf('14', plain,
% 0.19/0.47      ((((k1_tarski @ sk_B) = (u1_struct_0 @ sk_A))
% 0.19/0.47        | (v2_struct_0 @ sk_A)
% 0.19/0.47        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.47  thf('15', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('16', plain,
% 0.19/0.47      ((((k1_tarski @ sk_B) = (u1_struct_0 @ sk_A)) | (v2_struct_0 @ sk_A))),
% 0.19/0.47      inference('demod', [status(thm)], ['14', '15'])).
% 0.19/0.47  thf('17', plain, (~ (v2_struct_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('18', plain, (((k1_tarski @ sk_B) = (u1_struct_0 @ sk_A))),
% 0.19/0.47      inference('clc', [status(thm)], ['16', '17'])).
% 0.19/0.47  thf(fc6_struct_0, axiom,
% 0.19/0.47    (![A:$i]:
% 0.19/0.47     ( ( ( ~( v7_struct_0 @ A ) ) & ( l1_struct_0 @ A ) ) =>
% 0.19/0.47       ( ~( v1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.19/0.47  thf('19', plain,
% 0.19/0.47      (![X2 : $i]:
% 0.19/0.47         (~ (v1_zfmisc_1 @ (u1_struct_0 @ X2))
% 0.19/0.47          | ~ (l1_struct_0 @ X2)
% 0.19/0.47          | (v7_struct_0 @ X2))),
% 0.19/0.47      inference('cnf', [status(esa)], [fc6_struct_0])).
% 0.19/0.47  thf('20', plain,
% 0.19/0.47      ((~ (v1_zfmisc_1 @ (k1_tarski @ sk_B))
% 0.19/0.47        | (v7_struct_0 @ sk_A)
% 0.19/0.47        | ~ (l1_struct_0 @ sk_A))),
% 0.19/0.47      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.47  thf(fc2_zfmisc_1, axiom, (![A:$i]: ( v1_zfmisc_1 @ ( k1_tarski @ A ) ))).
% 0.19/0.47  thf('21', plain, (![X0 : $i]: (v1_zfmisc_1 @ (k1_tarski @ X0))),
% 0.19/0.47      inference('cnf', [status(esa)], [fc2_zfmisc_1])).
% 0.19/0.47  thf('22', plain, ((l1_struct_0 @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('23', plain, ((v7_struct_0 @ sk_A)),
% 0.19/0.47      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.19/0.47  thf('24', plain, ($false), inference('demod', [status(thm)], ['0', '23'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
