%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rQSiBOohwc

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:34 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   56 (  79 expanded)
%              Number of leaves         :   24 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  337 ( 919 expanded)
%              Number of equality atoms :   13 (  33 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    v5_relat_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v5_relat_1 @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('2',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('6',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( v1_partfun1 @ X10 @ X11 )
      | ~ ( v1_funct_2 @ X10 @ X11 @ X12 )
      | ~ ( v1_funct_1 @ X10 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['10','11'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_partfun1 @ X14 @ X13 )
      | ( ( k1_relat_1 @ X14 )
        = X13 )
      | ~ ( v4_relat_1 @ X14 @ X13 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('14',plain,
    ( ~ ( v1_relat_1 @ sk_B )
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
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
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
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X0 @ sk_B ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
      = ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['4','25'])).

thf('27',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ( k1_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) )
 != ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rQSiBOohwc
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:13:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.46  % Solved by: fo/fo7.sh
% 0.19/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.46  % done 25 iterations in 0.014s
% 0.19/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.46  % SZS output start Refutation
% 0.19/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.46  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.19/0.46  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.19/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.46  thf(t200_funct_2, conjecture,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.19/0.46             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.46           ( ![C:$i]:
% 0.19/0.46             ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & 
% 0.19/0.46                 ( v1_funct_1 @ C ) ) =>
% 0.19/0.46               ( ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) = ( k1_relat_1 @ C ) ) ) ) ) ) ))).
% 0.19/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.46    (~( ![A:$i]:
% 0.19/0.46        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.46          ( ![B:$i]:
% 0.19/0.46            ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.19/0.46                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.46              ( ![C:$i]:
% 0.19/0.46                ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & 
% 0.19/0.46                    ( v1_funct_1 @ C ) ) =>
% 0.19/0.46                  ( ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) =
% 0.19/0.46                    ( k1_relat_1 @ C ) ) ) ) ) ) ) )),
% 0.19/0.46    inference('cnf.neg', [status(esa)], [t200_funct_2])).
% 0.19/0.46  thf('0', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(d19_relat_1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ B ) =>
% 0.19/0.46       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.46  thf('1', plain,
% 0.19/0.46      (![X0 : $i, X1 : $i]:
% 0.19/0.46         (~ (v5_relat_1 @ X0 @ X1)
% 0.19/0.46          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.19/0.46          | ~ (v1_relat_1 @ X0))),
% 0.19/0.46      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.19/0.46  thf('2', plain,
% 0.19/0.46      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['0', '1'])).
% 0.19/0.46  thf('3', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('4', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_A)),
% 0.19/0.46      inference('demod', [status(thm)], ['2', '3'])).
% 0.19/0.46  thf('5', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(cc5_funct_2, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.19/0.46       ( ![C:$i]:
% 0.19/0.46         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.46           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.19/0.46             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.19/0.46  thf('6', plain,
% 0.19/0.46      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.46         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.19/0.46          | (v1_partfun1 @ X10 @ X11)
% 0.19/0.46          | ~ (v1_funct_2 @ X10 @ X11 @ X12)
% 0.19/0.46          | ~ (v1_funct_1 @ X10)
% 0.19/0.46          | (v1_xboole_0 @ X12))),
% 0.19/0.46      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.19/0.46  thf('7', plain,
% 0.19/0.46      (((v1_xboole_0 @ sk_A)
% 0.19/0.46        | ~ (v1_funct_1 @ sk_B)
% 0.19/0.46        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.19/0.46        | (v1_partfun1 @ sk_B @ sk_A))),
% 0.19/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.19/0.46  thf('8', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('9', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('10', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_B @ sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.19/0.46  thf('11', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('12', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.19/0.46      inference('clc', [status(thm)], ['10', '11'])).
% 0.19/0.46  thf(d4_partfun1, axiom,
% 0.19/0.46    (![A:$i,B:$i]:
% 0.19/0.46     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.19/0.46       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.19/0.46  thf('13', plain,
% 0.19/0.46      (![X13 : $i, X14 : $i]:
% 0.19/0.46         (~ (v1_partfun1 @ X14 @ X13)
% 0.19/0.46          | ((k1_relat_1 @ X14) = (X13))
% 0.19/0.46          | ~ (v4_relat_1 @ X14 @ X13)
% 0.19/0.46          | ~ (v1_relat_1 @ X14))),
% 0.19/0.46      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.19/0.46  thf('14', plain,
% 0.19/0.46      ((~ (v1_relat_1 @ sk_B)
% 0.19/0.46        | ~ (v4_relat_1 @ sk_B @ sk_A)
% 0.19/0.46        | ((k1_relat_1 @ sk_B) = (sk_A)))),
% 0.19/0.46      inference('sup-', [status(thm)], ['12', '13'])).
% 0.19/0.46  thf('15', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(cc1_relset_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.46       ( v1_relat_1 @ C ) ))).
% 0.19/0.46  thf('16', plain,
% 0.19/0.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.46         ((v1_relat_1 @ X4)
% 0.19/0.46          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.19/0.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.46  thf('17', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.46      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.46  thf('18', plain,
% 0.19/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf(cc2_relset_1, axiom,
% 0.19/0.46    (![A:$i,B:$i,C:$i]:
% 0.19/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.46       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.46  thf('19', plain,
% 0.19/0.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.19/0.46         ((v4_relat_1 @ X7 @ X8)
% 0.19/0.46          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.19/0.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.46  thf('20', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.19/0.46      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.46  thf('21', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.19/0.46      inference('demod', [status(thm)], ['14', '17', '20'])).
% 0.19/0.46  thf(t46_relat_1, axiom,
% 0.19/0.46    (![A:$i]:
% 0.19/0.46     ( ( v1_relat_1 @ A ) =>
% 0.19/0.46       ( ![B:$i]:
% 0.19/0.46         ( ( v1_relat_1 @ B ) =>
% 0.19/0.46           ( ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) =>
% 0.19/0.46             ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) = ( k1_relat_1 @ A ) ) ) ) ) ))).
% 0.19/0.46  thf('22', plain,
% 0.19/0.46      (![X2 : $i, X3 : $i]:
% 0.19/0.46         (~ (v1_relat_1 @ X2)
% 0.19/0.46          | ((k1_relat_1 @ (k5_relat_1 @ X3 @ X2)) = (k1_relat_1 @ X3))
% 0.19/0.46          | ~ (r1_tarski @ (k2_relat_1 @ X3) @ (k1_relat_1 @ X2))
% 0.19/0.46          | ~ (v1_relat_1 @ X3))),
% 0.19/0.46      inference('cnf', [status(esa)], [t46_relat_1])).
% 0.19/0.46  thf('23', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_A)
% 0.19/0.46          | ~ (v1_relat_1 @ X0)
% 0.19/0.46          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ sk_B)) = (k1_relat_1 @ X0))
% 0.19/0.46          | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.46      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.46  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.46      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.46  thf('25', plain,
% 0.19/0.46      (![X0 : $i]:
% 0.19/0.46         (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_A)
% 0.19/0.46          | ~ (v1_relat_1 @ X0)
% 0.19/0.46          | ((k1_relat_1 @ (k5_relat_1 @ X0 @ sk_B)) = (k1_relat_1 @ X0)))),
% 0.19/0.46      inference('demod', [status(thm)], ['23', '24'])).
% 0.19/0.46  thf('26', plain,
% 0.19/0.46      ((((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) = (k1_relat_1 @ sk_C))
% 0.19/0.46        | ~ (v1_relat_1 @ sk_C))),
% 0.19/0.46      inference('sup-', [status(thm)], ['4', '25'])).
% 0.19/0.46  thf('27', plain, ((v1_relat_1 @ sk_C)),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('28', plain,
% 0.19/0.46      (((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) = (k1_relat_1 @ sk_C))),
% 0.19/0.46      inference('demod', [status(thm)], ['26', '27'])).
% 0.19/0.46  thf('29', plain,
% 0.19/0.46      (((k1_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)) != (k1_relat_1 @ sk_C))),
% 0.19/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.46  thf('30', plain, ($false),
% 0.19/0.46      inference('simplify_reflect-', [status(thm)], ['28', '29'])).
% 0.19/0.46  
% 0.19/0.46  % SZS output end Refutation
% 0.19/0.47  
% 0.19/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
