%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dl0ecfYpOe

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:34 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   32 (  46 expanded)
%              Number of leaves         :   17 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :  274 ( 848 expanded)
%              Number of equality atoms :    2 (  16 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t37_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ? [D: $i] :
              ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
              & ( v1_funct_2 @ D @ B @ A )
              & ( v1_funct_1 @ D ) )
          & ~ ( v2_funct_1 @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( B != k1_xboole_0 )
            & ? [D: $i] :
                ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
                & ( v1_funct_2 @ D @ B @ A )
                & ( v1_funct_1 @ D ) )
            & ~ ( v2_funct_1 @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t37_funct_2])).

thf('0',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t29_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ X2 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ( v2_funct_1 @ X3 )
      | ~ ( r2_relset_1 @ X2 @ X2 @ ( k1_partfun1 @ X2 @ X1 @ X1 @ X2 @ X3 @ X0 ) @ ( k6_partfun1 @ X2 ) )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ X3 @ X2 @ X1 )
      | ~ ( v1_funct_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t29_funct_2])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
      | ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) @ ( k6_partfun1 @ sk_A ) )
      | ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,
    ( ( v2_funct_1 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['1','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['8','9','10','11'])).

thf('13',plain,(
    $false ),
    inference(demod,[status(thm)],['0','12'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Dl0ecfYpOe
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.47  % Solved by: fo/fo7.sh
% 0.19/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.47  % done 13 iterations in 0.014s
% 0.19/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.47  % SZS output start Refutation
% 0.19/0.47  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.19/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.47  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.19/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.47  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.19/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.47  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.19/0.47  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.19/0.47  thf(t37_funct_2, conjecture,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.47       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.47            ( ?[D:$i]:
% 0.19/0.47              ( ( r2_relset_1 @
% 0.19/0.47                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.19/0.47                  ( k6_partfun1 @ A ) ) & 
% 0.19/0.47                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 0.19/0.47                ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 0.19/0.47            ( ~( v2_funct_1 @ C ) ) ) ) ))).
% 0.19/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.47    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.47        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.47            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.47          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.19/0.47               ( ?[D:$i]:
% 0.19/0.47                 ( ( r2_relset_1 @
% 0.19/0.47                     A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.19/0.47                     ( k6_partfun1 @ A ) ) & 
% 0.19/0.47                   ( m1_subset_1 @
% 0.19/0.47                     D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) & 
% 0.19/0.47                   ( v1_funct_2 @ D @ B @ A ) & ( v1_funct_1 @ D ) ) ) & 
% 0.19/0.47               ( ~( v2_funct_1 @ C ) ) ) ) ) )),
% 0.19/0.47    inference('cnf.neg', [status(esa)], [t37_funct_2])).
% 0.19/0.47  thf('0', plain, (~ (v2_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('1', plain,
% 0.19/0.47      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.47        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.19/0.47        (k6_partfun1 @ sk_A))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('2', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf(t29_funct_2, axiom,
% 0.19/0.47    (![A:$i,B:$i,C:$i]:
% 0.19/0.47     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.47         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.47       ( ![D:$i]:
% 0.19/0.47         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.19/0.47             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.19/0.47           ( ( r2_relset_1 @
% 0.19/0.47               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.19/0.47               ( k6_partfun1 @ A ) ) =>
% 0.19/0.47             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.19/0.47  thf('3', plain,
% 0.19/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.19/0.47         (~ (v1_funct_1 @ X0)
% 0.19/0.47          | ~ (v1_funct_2 @ X0 @ X1 @ X2)
% 0.19/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 0.19/0.47          | (v2_funct_1 @ X3)
% 0.19/0.47          | ~ (r2_relset_1 @ X2 @ X2 @ 
% 0.19/0.47               (k1_partfun1 @ X2 @ X1 @ X1 @ X2 @ X3 @ X0) @ (k6_partfun1 @ X2))
% 0.19/0.47          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.19/0.47          | ~ (v1_funct_2 @ X3 @ X2 @ X1)
% 0.19/0.47          | ~ (v1_funct_1 @ X3))),
% 0.19/0.47      inference('cnf', [status(esa)], [t29_funct_2])).
% 0.19/0.47  thf('4', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v1_funct_1 @ X0)
% 0.19/0.47          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 0.19/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.19/0.47          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.47               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D) @ 
% 0.19/0.47               (k6_partfun1 @ sk_A))
% 0.19/0.47          | (v2_funct_1 @ X0)
% 0.19/0.47          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.19/0.47          | ~ (v1_funct_1 @ sk_D))),
% 0.19/0.47      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.47  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('7', plain,
% 0.19/0.47      (![X0 : $i]:
% 0.19/0.47         (~ (v1_funct_1 @ X0)
% 0.19/0.47          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_B)
% 0.19/0.47          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.19/0.47          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.19/0.47               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ X0 @ sk_D) @ 
% 0.19/0.47               (k6_partfun1 @ sk_A))
% 0.19/0.47          | (v2_funct_1 @ X0))),
% 0.19/0.47      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.19/0.47  thf('8', plain,
% 0.19/0.47      (((v2_funct_1 @ sk_C)
% 0.19/0.47        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.19/0.47        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.19/0.47        | ~ (v1_funct_1 @ sk_C))),
% 0.19/0.47      inference('sup-', [status(thm)], ['1', '7'])).
% 0.19/0.47  thf('9', plain,
% 0.19/0.47      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('10', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('11', plain, ((v1_funct_1 @ sk_C)),
% 0.19/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.47  thf('12', plain, ((v2_funct_1 @ sk_C)),
% 0.19/0.47      inference('demod', [status(thm)], ['8', '9', '10', '11'])).
% 0.19/0.47  thf('13', plain, ($false), inference('demod', [status(thm)], ['0', '12'])).
% 0.19/0.47  
% 0.19/0.47  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
