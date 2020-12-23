%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QMUyRJvHVO

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:17 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  67 expanded)
%              Number of leaves         :   21 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  411 ( 933 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t156_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r1_partfun1 @ B @ C )
           => ( r2_hidden @ C @ ( k5_partfun1 @ A @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r1_partfun1 @ B @ C )
             => ( r2_hidden @ C @ ( k5_partfun1 @ A @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t156_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_C @ ( k5_partfun1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_partfun1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d7_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ C ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( ( v1_funct_1 @ F )
                  & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
                  & ( F = E )
                  & ( v1_partfun1 @ F @ A )
                  & ( r1_partfun1 @ C @ F ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [F: $i,E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ C @ B @ A )
    <=> ( ( r1_partfun1 @ C @ F )
        & ( v1_partfun1 @ F @ A )
        & ( F = E )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F ) ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X11: $i] :
      ( ( zip_tseitin_0 @ X7 @ X8 @ X6 @ X9 @ X11 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X9 ) ) )
      | ( X7 != X8 )
      | ~ ( v1_partfun1 @ X7 @ X11 )
      | ~ ( r1_partfun1 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,(
    ! [X6: $i,X8: $i,X9: $i,X11: $i] :
      ( ~ ( r1_partfun1 @ X6 @ X8 )
      | ~ ( v1_partfun1 @ X8 @ X11 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X8 )
      | ( zip_tseitin_0 @ X8 @ X8 @ X6 @ X9 @ X11 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ sk_C @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_partfun1 @ sk_C @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( v1_partfun1 @ X3 @ X4 )
      | ~ ( v1_funct_2 @ X3 @ X4 @ X5 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('9',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ( v1_partfun1 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('15',plain,
    ( ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_partfun1 @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_C @ sk_C @ X0 @ sk_A @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['5','6','16'])).

thf('18',plain,(
    zip_tseitin_0 @ sk_C @ sk_C @ sk_B @ sk_A @ sk_A ),
    inference('sup-',[status(thm)],['1','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( D
            = ( k5_partfun1 @ A @ B @ C ) )
        <=> ! [E: $i] :
              ( ( r2_hidden @ E @ D )
            <=> ? [F: $i] :
                  ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i,X15: $i,X17: $i,X19: $i,X20: $i] :
      ( ( X17
       != ( k5_partfun1 @ X15 @ X14 @ X13 ) )
      | ( r2_hidden @ X19 @ X17 )
      | ~ ( zip_tseitin_0 @ X20 @ X19 @ X13 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X14 ) ) )
      | ~ ( zip_tseitin_0 @ X20 @ X19 @ X13 @ X14 @ X15 )
      | ( r2_hidden @ X19 @ ( k5_partfun1 @ X15 @ X14 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k5_partfun1 @ sk_A @ sk_A @ sk_B ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ sk_C @ ( k5_partfun1 @ sk_A @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    $false ),
    inference(demod,[status(thm)],['0','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QMUyRJvHVO
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:38:09 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 36 iterations in 0.021s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.46  thf(k5_partfun1_type, type, k5_partfun1: $i > $i > $i > $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.46  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.20/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.46  thf(t156_funct_2, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( v1_funct_1 @ B ) & 
% 0.20/0.46         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.46       ( ![C:$i]:
% 0.20/0.46         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.20/0.46             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.46           ( ( r1_partfun1 @ B @ C ) =>
% 0.20/0.46             ( r2_hidden @ C @ ( k5_partfun1 @ A @ A @ B ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( ( v1_funct_1 @ B ) & 
% 0.20/0.46            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.46          ( ![C:$i]:
% 0.20/0.46            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.20/0.46                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.46              ( ( r1_partfun1 @ B @ C ) =>
% 0.20/0.46                ( r2_hidden @ C @ ( k5_partfun1 @ A @ A @ B ) ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t156_funct_2])).
% 0.20/0.46  thf('0', plain, (~ (r2_hidden @ sk_C @ (k5_partfun1 @ sk_A @ sk_A @ sk_B))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain, ((r1_partfun1 @ sk_B @ sk_C)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d7_partfun1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.46         ( v1_funct_1 @ C ) ) =>
% 0.20/0.46       ( ![D:$i]:
% 0.20/0.46         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.20/0.46           ( ![E:$i]:
% 0.20/0.46             ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.46               ( ?[F:$i]:
% 0.20/0.46                 ( ( v1_funct_1 @ F ) & 
% 0.20/0.46                   ( m1_subset_1 @
% 0.20/0.46                     F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.46                   ( ( F ) = ( E ) ) & ( v1_partfun1 @ F @ A ) & 
% 0.20/0.46                   ( r1_partfun1 @ C @ F ) ) ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_1, axiom,
% 0.20/0.46    (![F:$i,E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.46     ( ( zip_tseitin_0 @ F @ E @ C @ B @ A ) <=>
% 0.20/0.46       ( ( r1_partfun1 @ C @ F ) & ( v1_partfun1 @ F @ A ) & 
% 0.20/0.46         ( ( F ) = ( E ) ) & 
% 0.20/0.46         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.46         ( v1_funct_1 @ F ) ) ))).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 0.20/0.46         ((zip_tseitin_0 @ X7 @ X8 @ X6 @ X9 @ X11)
% 0.20/0.46          | ~ (v1_funct_1 @ X7)
% 0.20/0.46          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X9)))
% 0.20/0.46          | ((X7) != (X8))
% 0.20/0.46          | ~ (v1_partfun1 @ X7 @ X11)
% 0.20/0.46          | ~ (r1_partfun1 @ X6 @ X7))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X6 : $i, X8 : $i, X9 : $i, X11 : $i]:
% 0.20/0.46         (~ (r1_partfun1 @ X6 @ X8)
% 0.20/0.46          | ~ (v1_partfun1 @ X8 @ X11)
% 0.20/0.46          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X9)))
% 0.20/0.46          | ~ (v1_funct_1 @ X8)
% 0.20/0.46          | (zip_tseitin_0 @ X8 @ X8 @ X6 @ X9 @ X11))),
% 0.20/0.46      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((zip_tseitin_0 @ sk_C @ sk_C @ X0 @ sk_A @ sk_A)
% 0.20/0.46          | ~ (v1_funct_1 @ sk_C)
% 0.20/0.46          | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.20/0.46          | ~ (r1_partfun1 @ X0 @ sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['2', '4'])).
% 0.20/0.46  thf('6', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(cc5_funct_2, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.46       ( ![C:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.20/0.46             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5)))
% 0.20/0.46          | (v1_partfun1 @ X3 @ X4)
% 0.20/0.46          | ~ (v1_funct_2 @ X3 @ X4 @ X5)
% 0.20/0.46          | ~ (v1_funct_1 @ X3)
% 0.20/0.46          | (v1_xboole_0 @ X5))),
% 0.20/0.46      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      (((v1_xboole_0 @ sk_A)
% 0.20/0.46        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.46        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.20/0.46        | (v1_partfun1 @ sk_C @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.46  thf('10', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('11', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('12', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_C @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(cc1_partfun1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_xboole_0 @ A ) =>
% 0.20/0.46       ( ![C:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.46         (~ (v1_xboole_0 @ X0)
% 0.20/0.46          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X2)))
% 0.20/0.46          | (v1_partfun1 @ X1 @ X0))),
% 0.20/0.46      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.20/0.46  thf('15', plain, (((v1_partfun1 @ sk_C @ sk_A) | ~ (v1_xboole_0 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.46  thf('16', plain, ((v1_partfun1 @ sk_C @ sk_A)),
% 0.20/0.46      inference('clc', [status(thm)], ['12', '15'])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((zip_tseitin_0 @ sk_C @ sk_C @ X0 @ sk_A @ sk_A)
% 0.20/0.46          | ~ (r1_partfun1 @ X0 @ sk_C))),
% 0.20/0.46      inference('demod', [status(thm)], ['5', '6', '16'])).
% 0.20/0.46  thf('18', plain, ((zip_tseitin_0 @ sk_C @ sk_C @ sk_B @ sk_A @ sk_A)),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '17'])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(zf_stmt_2, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.20/0.46  thf(zf_stmt_3, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( v1_funct_1 @ C ) & 
% 0.20/0.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.46       ( ![D:$i]:
% 0.20/0.46         ( ( ( D ) = ( k5_partfun1 @ A @ B @ C ) ) <=>
% 0.20/0.46           ( ![E:$i]:
% 0.20/0.46             ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.46               ( ?[F:$i]: ( zip_tseitin_0 @ F @ E @ C @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      (![X13 : $i, X14 : $i, X15 : $i, X17 : $i, X19 : $i, X20 : $i]:
% 0.20/0.46         (((X17) != (k5_partfun1 @ X15 @ X14 @ X13))
% 0.20/0.46          | (r2_hidden @ X19 @ X17)
% 0.20/0.46          | ~ (zip_tseitin_0 @ X20 @ X19 @ X13 @ X14 @ X15)
% 0.20/0.46          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14)))
% 0.20/0.46          | ~ (v1_funct_1 @ X13))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      (![X13 : $i, X14 : $i, X15 : $i, X19 : $i, X20 : $i]:
% 0.20/0.46         (~ (v1_funct_1 @ X13)
% 0.20/0.46          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X14)))
% 0.20/0.46          | ~ (zip_tseitin_0 @ X20 @ X19 @ X13 @ X14 @ X15)
% 0.20/0.46          | (r2_hidden @ X19 @ (k5_partfun1 @ X15 @ X14 @ X13)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.46  thf('22', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.46          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A @ sk_A)
% 0.20/0.46          | ~ (v1_funct_1 @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['19', '21'])).
% 0.20/0.46  thf('23', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((r2_hidden @ X0 @ (k5_partfun1 @ sk_A @ sk_A @ sk_B))
% 0.20/0.46          | ~ (zip_tseitin_0 @ X1 @ X0 @ sk_B @ sk_A @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['22', '23'])).
% 0.20/0.46  thf('25', plain, ((r2_hidden @ sk_C @ (k5_partfun1 @ sk_A @ sk_A @ sk_B))),
% 0.20/0.46      inference('sup-', [status(thm)], ['18', '24'])).
% 0.20/0.46  thf('26', plain, ($false), inference('demod', [status(thm)], ['0', '25'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
