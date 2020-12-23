%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qByOwhl5fS

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:01:59 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  75 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :  349 ( 655 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_orders_2_type,type,(
    v5_orders_2: $i > $o )).

thf(v3_orders_2_type,type,(
    v3_orders_2: $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v2_struct_0_type,type,(
    v2_struct_0: $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(l1_orders_2_type,type,(
    l1_orders_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_orders_2_type,type,(
    k3_orders_2: $i > $i > $i > $i )).

thf(k1_setfam_1_type,type,(
    k1_setfam_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_orders_2_type,type,(
    k2_orders_2: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_orders_2_type,type,(
    v4_orders_2: $i > $o )).

thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t60_orders_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
         => ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v2_struct_0 @ A )
          & ( v3_orders_2 @ A )
          & ( v4_orders_2 @ A )
          & ( v5_orders_2 @ A )
          & ( l1_orders_2 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) )
           => ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t60_orders_2])).

thf('0',plain,(
    ~ ( v2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( u1_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d14_orders_2,axiom,(
    ! [A: $i] :
      ( ( ~ ( v2_struct_0 @ A )
        & ( v3_orders_2 @ A )
        & ( v4_orders_2 @ A )
        & ( v5_orders_2 @ A )
        & ( l1_orders_2 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) )
             => ( ( k3_orders_2 @ A @ B @ C )
                = ( k9_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_orders_2 @ A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( ( k3_orders_2 @ X39 @ X38 @ X40 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X39 ) @ ( k2_orders_2 @ X39 @ ( k6_domain_1 @ ( u1_struct_0 @ X39 ) @ X40 ) ) @ X38 ) )
      | ~ ( m1_subset_1 @ X40 @ ( u1_struct_0 @ X39 ) )
      | ~ ( l1_orders_2 @ X39 )
      | ~ ( v5_orders_2 @ X39 )
      | ~ ( v4_orders_2 @ X39 )
      | ~ ( v3_orders_2 @ X39 )
      | ( v2_struct_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d14_orders_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_orders_2 @ X0 @ k1_xboole_0 @ X1 )
        = ( k9_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_orders_2 @ X0 @ ( k6_domain_1 @ ( u1_struct_0 @ X0 ) @ X1 ) ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k9_subset_1 @ X30 @ X28 @ X29 )
        = ( k3_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf(t12_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('7',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('8',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k9_subset_1 @ X30 @ X28 @ X29 )
        = ( k1_setfam_1 @ ( k2_tarski @ X28 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = ( k1_setfam_1 @ ( k2_tarski @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('11',plain,(
    ! [X32: $i,X33: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X32 @ X33 ) )
      = ( k3_xboole_0 @ X32 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t12_setfam_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_setfam_1 @ ( k2_tarski @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_struct_0 @ X0 )
      | ~ ( v3_orders_2 @ X0 )
      | ~ ( v4_orders_2 @ X0 )
      | ~ ( v5_orders_2 @ X0 )
      | ~ ( l1_orders_2 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( u1_struct_0 @ X0 ) )
      | ( ( k3_orders_2 @ X0 @ k1_xboole_0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['4','13'])).

thf('15',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
      = k1_xboole_0 )
    | ~ ( l1_orders_2 @ sk_A )
    | ~ ( v5_orders_2 @ sk_A )
    | ~ ( v4_orders_2 @ sk_A )
    | ~ ( v3_orders_2 @ sk_A )
    | ( v2_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','14'])).

thf('16',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v5_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v4_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v3_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
      = k1_xboole_0 )
    | ( v2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16','17','18','19'])).

thf(d2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k1_struct_0 @ A )
        = k1_xboole_0 ) ) )).

thf('21',plain,(
    ! [X37: $i] :
      ( ( ( k1_struct_0 @ X37 )
        = k1_xboole_0 )
      | ~ ( l1_struct_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d2_struct_0])).

thf('22',plain,(
    ( k3_orders_2 @ sk_A @ ( k1_struct_0 @ sk_A ) @ sk_B )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
     != k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    l1_orders_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_orders_2,axiom,(
    ! [A: $i] :
      ( ( l1_orders_2 @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('25',plain,(
    ! [X41: $i] :
      ( ( l1_struct_0 @ X41 )
      | ~ ( l1_orders_2 @ X41 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_orders_2])).

thf('26',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ( k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    v2_struct_0 @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['20','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['0','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.qByOwhl5fS
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:54:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 126 iterations in 0.040s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(v5_orders_2_type, type, v5_orders_2: $i > $o).
% 0.20/0.49  thf(v3_orders_2_type, type, v3_orders_2: $i > $o).
% 0.20/0.49  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.20/0.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.49  thf(v2_struct_0_type, type, v2_struct_0: $i > $o).
% 0.20/0.49  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.20/0.49  thf(l1_orders_2_type, type, l1_orders_2: $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k3_orders_2_type, type, k3_orders_2: $i > $i > $i > $i).
% 0.20/0.49  thf(k1_setfam_1_type, type, k1_setfam_1: $i > $i).
% 0.20/0.49  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.20/0.49  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(k2_orders_2_type, type, k2_orders_2: $i > $i > $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(v4_orders_2_type, type, v4_orders_2: $i > $o).
% 0.20/0.49  thf(k6_domain_1_type, type, k6_domain_1: $i > $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(t60_orders_2, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49           ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.49            ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49          ( ![B:$i]:
% 0.20/0.49            ( ( m1_subset_1 @ B @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49              ( ( k3_orders_2 @ A @ ( k1_struct_0 @ A ) @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t60_orders_2])).
% 0.20/0.49  thf('0', plain, (~ (v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain, ((m1_subset_1 @ sk_B @ (u1_struct_0 @ sk_A))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(t4_subset_1, axiom,
% 0.20/0.49    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X31 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.49  thf(d14_orders_2, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( ~( v2_struct_0 @ A ) ) & ( v3_orders_2 @ A ) & 
% 0.20/0.49         ( v4_orders_2 @ A ) & ( v5_orders_2 @ A ) & ( l1_orders_2 @ A ) ) =>
% 0.20/0.49       ( ![B:$i]:
% 0.20/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.20/0.49           ( ![C:$i]:
% 0.20/0.49             ( ( m1_subset_1 @ C @ ( u1_struct_0 @ A ) ) =>
% 0.20/0.49               ( ( k3_orders_2 @ A @ B @ C ) =
% 0.20/0.49                 ( k9_subset_1 @
% 0.20/0.49                   ( u1_struct_0 @ A ) @ 
% 0.20/0.49                   ( k2_orders_2 @
% 0.20/0.49                     A @ ( k6_domain_1 @ ( u1_struct_0 @ A ) @ C ) ) @ 
% 0.20/0.49                   B ) ) ) ) ) ) ))).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.20/0.49         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.20/0.49          | ((k3_orders_2 @ X39 @ X38 @ X40)
% 0.20/0.49              = (k9_subset_1 @ (u1_struct_0 @ X39) @ 
% 0.20/0.49                 (k2_orders_2 @ X39 @ (k6_domain_1 @ (u1_struct_0 @ X39) @ X40)) @ 
% 0.20/0.49                 X38))
% 0.20/0.49          | ~ (m1_subset_1 @ X40 @ (u1_struct_0 @ X39))
% 0.20/0.49          | ~ (l1_orders_2 @ X39)
% 0.20/0.49          | ~ (v5_orders_2 @ X39)
% 0.20/0.49          | ~ (v4_orders_2 @ X39)
% 0.20/0.49          | ~ (v3_orders_2 @ X39)
% 0.20/0.49          | (v2_struct_0 @ X39))),
% 0.20/0.49      inference('cnf', [status(esa)], [d14_orders_2])).
% 0.20/0.49  thf('4', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X0)
% 0.20/0.49          | ~ (v3_orders_2 @ X0)
% 0.20/0.49          | ~ (v4_orders_2 @ X0)
% 0.20/0.49          | ~ (v5_orders_2 @ X0)
% 0.20/0.49          | ~ (l1_orders_2 @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.49          | ((k3_orders_2 @ X0 @ k1_xboole_0 @ X1)
% 0.20/0.49              = (k9_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.20/0.49                 (k2_orders_2 @ X0 @ (k6_domain_1 @ (u1_struct_0 @ X0) @ X1)) @ 
% 0.20/0.49                 k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X31 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X31))),
% 0.20/0.49      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.20/0.49  thf(redefinition_k9_subset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.49       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.49         (((k9_subset_1 @ X30 @ X28 @ X29) = (k3_xboole_0 @ X28 @ X29))
% 0.20/0.49          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30)))),
% 0.20/0.49      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.20/0.49  thf(t12_setfam_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( k1_setfam_1 @ ( k2_tarski @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X32 : $i, X33 : $i]:
% 0.20/0.49         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 0.20/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.49         (((k9_subset_1 @ X30 @ X28 @ X29)
% 0.20/0.49            = (k1_setfam_1 @ (k2_tarski @ X28 @ X29)))
% 0.20/0.49          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30)))),
% 0.20/0.49      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0)
% 0.20/0.49           = (k1_setfam_1 @ (k2_tarski @ X1 @ k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.49  thf(t2_boole, axiom,
% 0.20/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X32 : $i, X33 : $i]:
% 0.20/0.49         ((k1_setfam_1 @ (k2_tarski @ X32 @ X33)) = (k3_xboole_0 @ X32 @ X33))),
% 0.20/0.49      inference('cnf', [status(esa)], [t12_setfam_1])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((k1_setfam_1 @ (k2_tarski @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['10', '11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((k9_subset_1 @ X0 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['9', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((v2_struct_0 @ X0)
% 0.20/0.49          | ~ (v3_orders_2 @ X0)
% 0.20/0.49          | ~ (v4_orders_2 @ X0)
% 0.20/0.49          | ~ (v5_orders_2 @ X0)
% 0.20/0.49          | ~ (l1_orders_2 @ X0)
% 0.20/0.49          | ~ (m1_subset_1 @ X1 @ (u1_struct_0 @ X0))
% 0.20/0.49          | ((k3_orders_2 @ X0 @ k1_xboole_0 @ X1) = (k1_xboole_0)))),
% 0.20/0.49      inference('demod', [status(thm)], ['4', '13'])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) = (k1_xboole_0))
% 0.20/0.49        | ~ (l1_orders_2 @ sk_A)
% 0.20/0.49        | ~ (v5_orders_2 @ sk_A)
% 0.20/0.49        | ~ (v4_orders_2 @ sk_A)
% 0.20/0.49        | ~ (v3_orders_2 @ sk_A)
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '14'])).
% 0.20/0.49  thf('16', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('17', plain, ((v5_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('18', plain, ((v4_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('19', plain, ((v3_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) = (k1_xboole_0))
% 0.20/0.49        | (v2_struct_0 @ sk_A))),
% 0.20/0.49      inference('demod', [status(thm)], ['15', '16', '17', '18', '19'])).
% 0.20/0.49  thf(d2_struct_0, axiom,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( l1_struct_0 @ A ) => ( ( k1_struct_0 @ A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X37 : $i]:
% 0.20/0.49         (((k1_struct_0 @ X37) = (k1_xboole_0)) | ~ (l1_struct_0 @ X37))),
% 0.20/0.49      inference('cnf', [status(esa)], [d2_struct_0])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (((k3_orders_2 @ sk_A @ (k1_struct_0 @ sk_A) @ sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      ((((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) != (k1_xboole_0))
% 0.20/0.49        | ~ (l1_struct_0 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('24', plain, ((l1_orders_2 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(dt_l1_orders_2, axiom,
% 0.20/0.49    (![A:$i]: ( ( l1_orders_2 @ A ) => ( l1_struct_0 @ A ) ))).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X41 : $i]: ((l1_struct_0 @ X41) | ~ (l1_orders_2 @ X41))),
% 0.20/0.49      inference('cnf', [status(esa)], [dt_l1_orders_2])).
% 0.20/0.49  thf('26', plain, ((l1_struct_0 @ sk_A)),
% 0.20/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (((k3_orders_2 @ sk_A @ k1_xboole_0 @ sk_B) != (k1_xboole_0))),
% 0.20/0.49      inference('demod', [status(thm)], ['23', '26'])).
% 0.20/0.49  thf('28', plain, ((v2_struct_0 @ sk_A)),
% 0.20/0.49      inference('simplify_reflect-', [status(thm)], ['20', '27'])).
% 0.20/0.49  thf('29', plain, ($false), inference('demod', [status(thm)], ['0', '28'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
