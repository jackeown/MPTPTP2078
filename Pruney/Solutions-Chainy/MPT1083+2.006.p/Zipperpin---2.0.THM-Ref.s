%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.a4VlTeKbh8

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 (  83 expanded)
%              Number of leaves         :   26 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  398 ( 980 expanded)
%              Number of equality atoms :   26 (  46 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(t200_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ A @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v5_relat_1 @ C @ A )
                & ( v1_funct_1 @ C ) )
             => ( ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) )
                = ( k1_relat_1 @ C ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ( v1_funct_1 @ B )
              & ( v1_funct_2 @ B @ A @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v5_relat_1 @ C @ A )
                  & ( v1_funct_1 @ C ) )
               => ( ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) )
                  = ( k1_relat_1 @ C ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t200_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('3',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X12 ) ) )
      | ( v1_partfun1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X12 ) ) )
      | ~ ( v1_funct_2 @ X13 @ X14 @ X12 )
      | ~ ( v1_funct_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_2 @ X13 @ X14 @ X12 )
      | ( v1_partfun1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ( X12 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_B )
    | ( v1_partfun1 @ sk_B @ sk_A )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v1_partfun1 @ X11 @ X10 )
      | ( ( k1_relat_1 @ X11 )
        = X10 )
      | ~ ( v4_relat_1 @ X11 @ X10 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('14',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v4_relat_1 @ sk_B @ sk_A )
    | ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('17',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('20',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['14','17','20'])).

thf(t46_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
           => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
              = ( k1_relat_1 @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X3 @ X2 ) )
        = ( k1_relat_1 @ X3 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X3 ) @ ( k1_relat_1 @ X2 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t46_relat_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ sk_B ) )
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_A )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ sk_B ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
      = ( k1_relat_1 @ sk_C ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('32',plain,(
    $false ),
    inference(demod,[status(thm)],['0','30','31'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.a4VlTeKbh8
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:58:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.22/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.48  % Solved by: fo/fo7.sh
% 0.22/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.48  % done 29 iterations in 0.016s
% 0.22/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.48  % SZS output start Refutation
% 0.22/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.48  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.22/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.48  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.48  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.22/0.48  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.48  thf(t200_funct_2, conjecture,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.48             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.48           ( ![C:$i]:
% 0.22/0.48             ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & 
% 0.22/0.48                 ( v1_funct_1 @ C ) ) =>
% 0.22/0.48               ( ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) = ( k1_relat_1 @ C ) ) ) ) ) ) ))).
% 0.22/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.48    (~( ![A:$i]:
% 0.22/0.48        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.48          ( ![B:$i]:
% 0.22/0.48            ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.48                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.48              ( ![C:$i]:
% 0.22/0.48                ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & 
% 0.22/0.48                    ( v1_funct_1 @ C ) ) =>
% 0.22/0.48                  ( ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) =
% 0.22/0.48                    ( k1_relat_1 @ C ) ) ) ) ) ) ) )),
% 0.22/0.48    inference('cnf.neg', [status(esa)], [t200_funct_2])).
% 0.22/0.48  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('1', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(d19_relat_1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ B ) =>
% 0.22/0.48       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.48  thf('2', plain,
% 0.22/0.48      (![X0 : $i, X1 : $i]:
% 0.22/0.48         (~ (v5_relat_1 @ X0 @ X1)
% 0.22/0.48          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.22/0.48          | ~ (v1_relat_1 @ X0))),
% 0.22/0.48      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.22/0.48  thf('3', plain,
% 0.22/0.48      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.48  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('5', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.22/0.48      inference('demod', [status(thm)], ['3', '4'])).
% 0.22/0.48  thf('6', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(t132_funct_2, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.48       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.48           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.48         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.22/0.48           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.22/0.48  thf('7', plain,
% 0.22/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.48         (((X12) = (k1_xboole_0))
% 0.22/0.48          | ~ (v1_funct_1 @ X13)
% 0.22/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X12)))
% 0.22/0.48          | (v1_partfun1 @ X13 @ X14)
% 0.22/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X12)))
% 0.22/0.48          | ~ (v1_funct_2 @ X13 @ X14 @ X12)
% 0.22/0.48          | ~ (v1_funct_1 @ X13))),
% 0.22/0.48      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.22/0.48  thf('8', plain,
% 0.22/0.48      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.48         (~ (v1_funct_2 @ X13 @ X14 @ X12)
% 0.22/0.48          | (v1_partfun1 @ X13 @ X14)
% 0.22/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X12)))
% 0.22/0.48          | ~ (v1_funct_1 @ X13)
% 0.22/0.48          | ((X12) = (k1_xboole_0)))),
% 0.22/0.48      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.48  thf('9', plain,
% 0.22/0.48      ((((sk_A) = (k1_xboole_0))
% 0.22/0.48        | ~ (v1_funct_1 @ sk_B)
% 0.22/0.48        | (v1_partfun1 @ sk_B @ sk_A)
% 0.22/0.48        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A))),
% 0.22/0.48      inference('sup-', [status(thm)], ['6', '8'])).
% 0.22/0.48  thf('10', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('11', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('12', plain, ((((sk_A) = (k1_xboole_0)) | (v1_partfun1 @ sk_B @ sk_A))),
% 0.22/0.48      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.22/0.48  thf(d4_partfun1, axiom,
% 0.22/0.48    (![A:$i,B:$i]:
% 0.22/0.48     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.48       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.22/0.48  thf('13', plain,
% 0.22/0.48      (![X10 : $i, X11 : $i]:
% 0.22/0.48         (~ (v1_partfun1 @ X11 @ X10)
% 0.22/0.48          | ((k1_relat_1 @ X11) = (X10))
% 0.22/0.48          | ~ (v4_relat_1 @ X11 @ X10)
% 0.22/0.48          | ~ (v1_relat_1 @ X11))),
% 0.22/0.48      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.22/0.48  thf('14', plain,
% 0.22/0.48      ((((sk_A) = (k1_xboole_0))
% 0.22/0.48        | ~ (v1_relat_1 @ sk_B)
% 0.22/0.48        | ~ (v4_relat_1 @ sk_B @ sk_A)
% 0.22/0.48        | ((k1_relat_1 @ sk_B) = (sk_A)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.48  thf('15', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(cc1_relset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.48       ( v1_relat_1 @ C ) ))).
% 0.22/0.48  thf('16', plain,
% 0.22/0.48      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.48         ((v1_relat_1 @ X4)
% 0.22/0.48          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.22/0.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.48  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.48  thf('18', plain,
% 0.22/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf(cc2_relset_1, axiom,
% 0.22/0.48    (![A:$i,B:$i,C:$i]:
% 0.22/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.48  thf('19', plain,
% 0.22/0.48      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.48         ((v4_relat_1 @ X7 @ X8)
% 0.22/0.48          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.22/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.48  thf('20', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.22/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.48  thf('21', plain,
% 0.22/0.48      ((((sk_A) = (k1_xboole_0)) | ((k1_relat_1 @ sk_B) = (sk_A)))),
% 0.22/0.48      inference('demod', [status(thm)], ['14', '17', '20'])).
% 0.22/0.48  thf(t46_relat_1, axiom,
% 0.22/0.48    (![A:$i]:
% 0.22/0.48     ( ( v1_relat_1 @ A ) =>
% 0.22/0.48       ( ![B:$i]:
% 0.22/0.48         ( ( v1_relat_1 @ B ) =>
% 0.22/0.48           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.22/0.48             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.22/0.48  thf('22', plain,
% 0.22/0.48      (![X2 : $i, X3 : $i]:
% 0.22/0.48         (~ (v1_relat_1 @ X2)
% 0.22/0.48          | ((k1_relat_1 @ (k5_relat_1 @ X3 @ X2)) = (k1_relat_1 @ X3))
% 0.22/0.48          | ~ (r1_tarski @ (k2_relat_1 @ X3) @ (k1_relat_1 @ X2))
% 0.22/0.48          | ~ (v1_relat_1 @ X3))),
% 0.22/0.48      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.22/0.48  thf('23', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_A)
% 0.22/0.48          | ((sk_A) = (k1_xboole_0))
% 0.22/0.48          | ~ (v1_relat_1 @ X0)
% 0.22/0.48          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ sk_B)) = (k1_relat_1 @ X0))
% 0.22/0.48          | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.48      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.48  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.48      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.48  thf('25', plain,
% 0.22/0.48      (![X0 : $i]:
% 0.22/0.48         (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_A)
% 0.22/0.48          | ((sk_A) = (k1_xboole_0))
% 0.22/0.48          | ~ (v1_relat_1 @ X0)
% 0.22/0.48          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ sk_B)) = (k1_relat_1 @ X0)))),
% 0.22/0.48      inference('demod', [status(thm)], ['23', '24'])).
% 0.22/0.48  thf('26', plain,
% 0.22/0.48      ((((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) = (k1_relat_1 @ sk_C))
% 0.22/0.48        | ~ (v1_relat_1 @ sk_C)
% 0.22/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.48      inference('sup-', [status(thm)], ['5', '25'])).
% 0.22/0.48  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('28', plain,
% 0.22/0.48      ((((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) = (k1_relat_1 @ sk_C))
% 0.22/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.48      inference('demod', [status(thm)], ['26', '27'])).
% 0.22/0.48  thf('29', plain,
% 0.22/0.48      (((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) != (k1_relat_1 @ sk_C))),
% 0.22/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.48  thf('30', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.48      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.22/0.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.22/0.48  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.22/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.22/0.48  thf('32', plain, ($false),
% 0.22/0.48      inference('demod', [status(thm)], ['0', '30', '31'])).
% 0.22/0.48  
% 0.22/0.48  % SZS output end Refutation
% 0.22/0.48  
% 0.22/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
